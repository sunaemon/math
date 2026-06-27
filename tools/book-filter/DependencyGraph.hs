{-# LANGUAGE OverloadedStrings #-}

{- | The chapter-dependency graph: collecting cross-references between chapters,
laying the nodes out with a force-directed optimizer, and rendering the result
as a TikZ picture.

The layout is expensive, so it is memoized on disk. The cache I/O lives in
honest 'IO' actions ('readDependencyLayoutCache' / 'writeDependencyLayoutCache')
that the caller runs around the pure layout: build a 'DependencyGraphPlan',
read the cache by its signature, hand the cached positions (if any) to
'renderDependencyGraph', and persist the freshly computed positions it returns.
Nothing here reaches the filesystem through 'unsafePerformIO'; the only
remaining 'unsafePerformIO' is the optional, debug-gated timing instrumentation,
which merely measures and never affects which layout is produced or stored.
-}
module DependencyGraph (
  HeaderInfo (..),
  PartInfo (..),
  DependencyEdge (..),
  LayoutBox (..),
  OptimizationConfig (..),
  DependencyGraphPlan,
  planDependencyGraph,
  planCacheNodes,
  planCacheSignature,
  renderDependencyGraph,
  readDependencyLayoutCache,
  writeDependencyLayoutCache,
) where

import Control.Exception (IOException, catch)
import Control.Monad (when)
import Data.Foldable (asum)
import Data.IORef
import Data.List (foldl', sortOn)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, mapMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Data.Time.Clock (diffUTCTime, getCurrentTime)
import SectionRef (nextSectionRef)
import System.Directory (createDirectoryIfMissing)
import System.IO.Unsafe (unsafePerformIO)
import Text.Pandoc.Definition
import Text.Pandoc.Walk (query)

-- A private copy of the raw-TeX format predicate. It is a trivial two-liner, so
-- duplicating it keeps this module standalone instead of forcing a shared-helper
-- module or an awkward import from Main.
isTexFormat :: Format -> Bool
isTexFormat (Format fmt) = fmt == "tex" || fmt == "latex"

data HeaderInfo = HeaderInfo
  { headerIndex :: Int
  , headerLevel :: Int
  , headerId :: Text
  }
  deriving (Eq, Ord, Show)

data PartInfo = PartInfo
  { partIndex :: Int
  , partName :: Text
  }
  deriving (Eq, Ord, Show)

data DependencyEdge = DependencyEdge
  { edgeFrom :: HeaderInfo
  , edgeTo :: HeaderInfo
  , edgeCount :: Int
  }
  deriving (Eq, Show)

data LayoutBox = LayoutBox
  { boxLeft :: Double
  , boxRight :: Double
  , boxTop :: Double
  , boxBottom :: Double
  }
  deriving (Eq, Show)

data OptimizationTiming = OptimizationTiming
  { timingCount :: Int
  , timingPicos :: Integer
  }
  deriving (Eq, Show)

data OptimizationConfig = OptimizationConfig
  { configTimingEnabled :: Bool
  , configDisableAnnealingSwaps :: Bool
  , configDisableRefinementSwaps :: Bool
  , configNewtonBlockOverride :: Maybe Int
  }
  deriving (Eq, Show)

-- Everything about the graph that does not require the expensive layout: the
-- node set, their TikZ names and labels, the edges (full set and the parted
-- subset that drives the layout), the part groups and their frame boxes, and the
-- reciprocal-edge set. Building this is cheap; only 'renderDependencyGraph'
-- triggers the layout solver.
data DependencyGraphPlan = DependencyGraphPlan
  { dgNames :: Map HeaderInfo Text
  , dgLabels :: Map HeaderInfo Text
  , dgNodes :: [HeaderInfo]
  , dgEdges :: [DependencyEdge]
  , dgGroups :: [(PartInfo, [HeaderInfo])]
  , dgBoxes :: Map PartInfo LayoutBox
  , dgLayoutEdges :: [DependencyEdge]
  , dgReciprocal :: Set (HeaderInfo, HeaderInfo)
  }

{- | Build the cheap part of the graph from a document. @graphOnly@ selects
bare chapter-number labels (for a standalone graph page) instead of @\\ref@
labels; @excludedChapters@ drops chapters from the graph by section id.
-}
planDependencyGraph :: Bool -> Set Text -> Pandoc -> DependencyGraphPlan
planDependencyGraph graphOnly excludedChapters doc@(Pandoc _ blocks) =
  DependencyGraphPlan
    { dgNames = names
    , dgLabels = labels
    , dgNodes = nodes
    , dgEdges = edges
    , dgGroups = groups
    , dgBoxes = boxes
    , dgLayoutEdges = layoutEdges
    , dgReciprocal = reciprocalEdges
    }
 where
  headers = collectHeaderInfos doc
  chapters = filter ((== 1) . headerLevel) headers
  parts = collectPartInfos doc
  keepChapter header = headerId header `Set.notMember` excludedChapters
  headerById = Map.fromList [(headerId h, h) | h <- headers]
  chapterNumbers = Map.fromList (zip chapters [(1 :: Int) ..])
  labelToChapter =
    Map.fromList
      [ (headerId h, chapterFor chapters h)
      | h <- headers
      ]
  edgeCounts =
    Map.fromListWith
      (+)
      [ ((target, source), 1 :: Int)
      | (source, ref) <- chapterRefs headerById blocks
      , keepChapter source
      , Just target <- [Map.lookup ref labelToChapter]
      , keepChapter target
      , headerId source /= headerId target
      ]
  edges =
    take 18
      . sortOn (\edge -> (negate (edgeCount edge), headerIndex (edgeFrom edge), headerIndex (edgeTo edge)))
      $ [ DependencyEdge from to count
        | ((from, to), count) <- Map.toList edgeCounts
        ]
  nodes =
    sortOn headerIndex . Set.toList $
      Set.fromList (concat [[edgeFrom edge, edgeTo edge] | edge <- edges])
  names = Map.fromList (zip nodes ["n" <> T.pack (show n) | n <- [(0 :: Int) ..]])
  nodeParts =
    Map.fromList
      [ (node, part)
      | node <- nodes
      , Just part <- [partFor parts node]
      ]
  labels =
    if graphOnly
      then
        Map.fromList
          [ (node, tshow chapterNumber)
          | node <- nodes
          , let chapter = chapterFor chapters node
                chapterNumber = fromMaybe (0 :: Int) (Map.lookup chapter chapterNumbers)
          ]
      else
        Map.fromList
          [ (node, "\\ref{" <> headerId node <> "}")
          | node <- nodes
          ]
  reciprocalEdges =
    Set.fromList
      [ (edgeFrom edge, edgeTo edge)
      | edge <- edges
      , any
          ( \other ->
              edgeFrom other == edgeTo edge
                && edgeTo other == edgeFrom edge
          )
          edges
      ]
  groups = dependencyPartGroups nodeParts nodes
  boxes = dependencyPartBoxes groups
  -- The layout is computed only over nodes that belong to a Part (groups drops
  -- partless nodes), so any edge touching a partless node (e.g. a chapter
  -- before the first \part) is excluded from the layout, mirroring drawnEdges
  -- in the render path.
  partedNodes = Set.fromList (concatMap snd groups)
  layoutEdges =
    [ edge
    | edge <- edges
    , Set.member (edgeFrom edge) partedNodes
    , Set.member (edgeTo edge) partedNodes
    ]

{- | The node list a cache entry is keyed against (the parted nodes, in layout
order). Pass it to the cache read/write actions alongside the signature.
-}
planCacheNodes :: DependencyGraphPlan -> [HeaderInfo]
planCacheNodes plan = concatMap (sortOn headerIndex . snd) (dgGroups plan)

{- | The cache signature for a plan under a given optimizer configuration. A
cache file whose first line does not match this is treated as a miss.
-}
planCacheSignature :: OptimizationConfig -> DependencyGraphPlan -> Text
planCacheSignature graphConfig plan =
  dependencyLayoutCacheSignature graphConfig (dgGroups plan) (dgBoxes plan) (dgLayoutEdges plan)

{- | Render the graph to TikZ. @cached@ is the validated cached positions (or
'Nothing' for a miss). The second component of the result is the freshly
computed positions to persist on a miss, or 'Nothing' when the cache was used;
the caller writes it back with 'writeDependencyLayoutCache'.
-}
renderDependencyGraph ::
  Bool ->
  OptimizationConfig ->
  DependencyGraphPlan ->
  Maybe (Map HeaderInfo (Double, Double)) ->
  (Text, Maybe (Map HeaderInfo (Double, Double)))
renderDependencyGraph debugGraph graphConfig plan cached =
  let (positions, layoutEnergyValue, lossCurve, snapshots, timingLines, fresh) =
        dependencyNodePositions graphConfig (dgGroups plan) (dgBoxes plan) (dgLayoutEdges plan) cached
      body =
        T.unlines $
          [ "% Generated by book-filter.hs from section references."
          , "% Dependency graph layout energy: " <> tshow layoutEnergyValue
          ]
            ++ dependencyLossCurveLines lossCurve
            ++ timingLines
            ++ if debugGraph
              then concatMap (dependencyGraphSnapshotLines (dgBoxes plan) (dgNames plan) (dgLabels plan) (dgNodes plan) (dgReciprocal plan) (dgEdges plan)) snapshots
              else dependencyGraphPictureLines (dgBoxes plan) (dgNames plan) (dgLabels plan) positions (dgNodes plan) (dgReciprocal plan) (dgEdges plan)
   in (body, if fresh then Just positions else Nothing)

collectHeaderInfos :: Pandoc -> [HeaderInfo]
collectHeaderInfos (Pandoc _ blocks) =
  mapMaybe getHeader (zip [(0 :: Int) ..] blocks)
 where
  getHeader :: (Int, Block) -> Maybe HeaderInfo
  getHeader (idx, Header level (hid, _, _) _)
    | not (T.null hid) = Just (HeaderInfo idx level hid)
  getHeader _ = Nothing

collectPartInfos :: Pandoc -> [PartInfo]
collectPartInfos (Pandoc _ blocks) =
  [ PartInfo idx ("Part " <> romanNumeral number)
  | (number, (idx, _)) <- zip [(1 :: Int) ..] partBlocks
  ]
 where
  partBlocks =
    [ (idx, txt)
    | (idx, RawBlock fmt txt) <- zip [(0 :: Int) ..] blocks
    , isTexFormat fmt
    , "\\part{" `T.isInfixOf` txt
    ]

-- A standard subtractive Roman numeral. (The part-box grid in
-- 'dependencyPartBoxes' still lays parts out two-to-a-row, so it assumes a
-- modest number of parts regardless of how the label is rendered.)
romanNumeral :: Int -> Text
romanNumeral n
  | n <= 0 = tshow n
  | otherwise = go n symbols
 where
  symbols =
    [ (1000, "M")
    , (900, "CM")
    , (500, "D")
    , (400, "CD")
    , (100, "C")
    , (90, "XC")
    , (50, "L")
    , (40, "XL")
    , (10, "X")
    , (9, "IX")
    , (5, "V")
    , (4, "IV")
    , (1, "I")
    ]
  go _ [] = ""
  go k table@((value, symbol) : rest)
    | k >= value = symbol <> go (k - value) table
    | otherwise = go k rest

partFor :: [PartInfo] -> HeaderInfo -> Maybe PartInfo
partFor parts header =
  lastMaybe $
    takeWhile ((<= headerIndex header) . partIndex) parts

chapterFor :: [HeaderInfo] -> HeaderInfo -> HeaderInfo
chapterFor chapters header =
  fromMaybe header . lastMaybe $
    takeWhile ((<= headerIndex header) . headerIndex) chapters

lastMaybe :: [a] -> Maybe a
lastMaybe [] = Nothing
lastMaybe xs = Just (last xs)

chapterRefs :: Map Text HeaderInfo -> [Block] -> [(HeaderInfo, Text)]
chapterRefs headerById = go Nothing
 where
  go _ [] = []
  go current (block : rest) =
    case block of
      Header 1 (hid, _, _) _
        | Just chapter <- Map.lookup hid headerById ->
            go (Just chapter) rest
      _ ->
        let here =
              [ (chapter, ref)
              | Just chapter <- [current]
              , ref <- query inlineRefs block
              ]
         in here ++ go current rest

  inlineRefs :: Inline -> [Text]
  inlineRefs (Str txt) = sectionRefsInText txt
  inlineRefs _ = []

sectionRefsInText :: Text -> [Text]
sectionRefsInText txt =
  case nextSectionRef txt of
    Nothing -> []
    Just (_, hid, rest) -> hid : sectionRefsInText rest

dependencyGraphSnapshotLines :: Map PartInfo LayoutBox -> Map HeaderInfo Text -> Map HeaderInfo Text -> [HeaderInfo] -> Set (HeaderInfo, HeaderInfo) -> [DependencyEdge] -> (Int, Double, Map HeaderInfo (Double, Double)) -> [Text]
dependencyGraphSnapshotLines boxes names labels nodes reciprocalEdges edges (step, energy, positions) =
  [ "\\par\\smallskip"
  , "\\noindent\\textit{step " <> tshow step <> ", energy " <> tshow energy <> "}"
  , "\\par\\smallskip"
  ]
    ++ dependencyGraphPictureLines boxes names labels positions nodes reciprocalEdges edges

dependencyGraphPictureLines :: Map PartInfo LayoutBox -> Map HeaderInfo Text -> Map HeaderInfo Text -> Map HeaderInfo (Double, Double) -> [HeaderInfo] -> Set (HeaderInfo, HeaderInfo) -> [DependencyEdge] -> [Text]
dependencyGraphPictureLines boxes names labels positions nodes reciprocalEdges edges =
  -- A part with no positioned nodes (for example a single-chapter excerpt with no
  -- \part structure) would otherwise emit \resizebox{...}{!}{<zero-width box>} and
  -- divide by zero in lualatex; emit nothing for that part instead.
  if null drawnNodes
    then []
    else
      [ "\\resizebox{0.95\\linewidth}{!}{%"
      , "\\begin{tikzpicture}["
      , "  depnode/.style={rectangle, draw, fill=white, inner xsep=4pt, inner ysep=2pt, font=\\scriptsize, minimum width=0.72cm, minimum height=0.46cm},"
      , "  depframe/.style={draw, rounded corners=2pt, inner sep=5pt, fill=black!2},"
      , "  depedge/.style={->, thin, shorten >=2pt, shorten <=2pt}"
      , "]"
      ]
        ++ dependencyNodeLines names labels positions drawnNodes
        ++ dependencyBackgroundLines boxes names positions reciprocalEdges drawnEdges
        ++ [ "\\end{tikzpicture}%"
           , "}"
           ]
 where
  -- positions is keyed only by nodes that belong to a Part; an edge endpoint
  -- with no Part (e.g. a chapter before the first \part) would otherwise make
  -- the positions lookups partial and crash the build with an opaque Map.!.
  drawnNodes = filter (`Map.member` positions) nodes
  drawnEdges =
    [ edge
    | edge <- edges
    , Map.member (edgeFrom edge) positions
    , Map.member (edgeTo edge) positions
    ]

dependencyLossCurveLines :: [(Int, Double)] -> [Text]
dependencyLossCurveLines lossCurve =
  "% Dependency graph loss curve: step energy"
    : [ "%   " <> tshow step <> " " <> tshow energy
      | (step, energy) <- lossCurve
      ]

dependencyNodeLines :: Map HeaderInfo Text -> Map HeaderInfo Text -> Map HeaderInfo (Double, Double) -> [HeaderInfo] -> [Text]
dependencyNodeLines names labels positions nodes =
  [ "\\node[depnode] ("
      <> names Map.! node
      <> ") at ("
      <> tshow x
      <> ","
      <> tshow y
      <> ") {"
      <> labels Map.! node
      <> "};"
  | node <- nodes
  , let (x, y) = positions Map.! node
  ]

dependencyEdgeLines :: Map HeaderInfo Text -> Map HeaderInfo (Double, Double) -> Set (HeaderInfo, HeaderInfo) -> [DependencyEdge] -> [Text]
dependencyEdgeLines names positions reciprocalEdges edges =
  [ "\\draw[depedge"
      <> edgeOptions edge
      <> "] ("
      <> names Map.! edgeFrom edge
      <> ") to ("
      <> names Map.! edgeTo edge
      <> ");"
  | edge <- edges
  ]
 where
  edgeOptions edge
    | Set.member (edgeFrom edge, edgeTo edge) reciprocalEdges = ", bend left=16"
    | edgeCrossesNode edge = ", bend left=13"
    | otherwise = ""

  edgeCrossesNode edge =
    any (nodeNearSegment edge) (Map.toList positions)

  nodeNearSegment edge (node, point)
    | node == edgeFrom edge || node == edgeTo edge = False
    | otherwise =
        pointSegmentDistance point (positions Map.! edgeFrom edge) (positions Map.! edgeTo edge) < 0.34
          && pointBetweenEndpoints point (positions Map.! edgeFrom edge) (positions Map.! edgeTo edge)

dependencyBackgroundLines :: Map PartInfo LayoutBox -> Map HeaderInfo Text -> Map HeaderInfo (Double, Double) -> Set (HeaderInfo, HeaderInfo) -> [DependencyEdge] -> [Text]
dependencyBackgroundLines boxes names positions reciprocalEdges edges =
  "\\begin{scope}[on background layer]"
    : dependencyFrameBodyLines boxes
    ++ dependencyEdgeLines names positions reciprocalEdges edges
    ++ ["\\end{scope}"]

dependencyPartGroups :: Map HeaderInfo PartInfo -> [HeaderInfo] -> [(PartInfo, [HeaderInfo])]
dependencyPartGroups nodeParts nodes =
  sortOn (partIndex . fst) . Map.elems $
    Map.fromListWith
      combine
      [ (partName part, (part, [node]))
      | node <- nodes
      , Just part <- [Map.lookup node nodeParts]
      ]
 where
  combine (part, left) (_, right) =
    (part, left ++ right)

dependencyPartBoxes :: [(PartInfo, [HeaderInfo])] -> Map PartInfo LayoutBox
dependencyPartBoxes groups =
  Map.fromList
    [ (part, partBox groupIdx nodeCount)
    | (groupIdx, (part, groupNodes)) <- indexedGroups
    , let nodeCount = length groupNodes
    ]
 where
  indexedGroups =
    zip [(0 :: Int) ..] groups

  partBox groupIdx nodeCount =
    let groupCol = groupIdx `mod` 2
        groupRow = groupIdx `div` 2
        (width, height) = partSize nodeCount
        left = offsetFor colWidths colGap groupCol
        top = negate (offsetFor rowHeights rowGap groupRow)
     in LayoutBox
          { boxLeft = left
          , boxRight = left + width
          , boxTop = top
          , boxBottom = top - height
          }

  colWidths =
    [ maximumWithDefault
        0
        [ fst (partSize (length groupNodes))
        | (groupIdx, (_, groupNodes)) <- indexedGroups
        , groupIdx `mod` 2 == col
        ]
    | col <- [0, 1]
    ]

  rowHeights =
    [ maximumWithDefault
        0
        [ snd (partSize (length groupNodes))
        | (groupIdx, (_, groupNodes)) <- indexedGroups
        , groupIdx `div` 2 == row
        ]
    | row <- [0, 1]
    ]

  offsetFor sizes gap idx =
    sum (take idx sizes) + fromIntegral idx * gap

  partSize nodeCount =
    let extra = fromIntegral (max 0 (nodeCount - 4))
     in (5.10 + 0.28 * extra, 2.65 + 0.34 * extra)

  maximumWithDefault fallback [] = fallback
  maximumWithDefault _ values = maximum values

  colGap = 1.35
  rowGap = 1.15

dependencyNodePositions :: OptimizationConfig -> [(PartInfo, [HeaderInfo])] -> Map PartInfo LayoutBox -> [DependencyEdge] -> Maybe (Map HeaderInfo (Double, Double)) -> (Map HeaderInfo (Double, Double), Double, [(Int, Double)], [(Int, Double, Map HeaderInfo (Double, Double))], [Text], Bool)
dependencyNodePositions graphConfig groups boxes edges cached =
  let _resetTimings = resetOptimizationTimings (configTimingEnabled graphConfig)
   in _resetTimings `seq`
        case cached of
          Just cachedPositions ->
            let layoutEnergyValue = layoutEnergy cachedPositions
                cacheLines = ["% Dependency graph layout cache: hit"]
                lossCurve = [(0, layoutEnergyValue)]
                snapshots = [(0, layoutEnergyValue, cachedPositions)]
                _forceResult =
                  forcePositionMap cachedPositions `seq`
                    layoutEnergyValue `seq`
                      length lossCurve `seq`
                        length snapshots
                timingLines = _forceResult `seq` cacheLines ++ optimizationTimingLines (configTimingEnabled graphConfig)
             in (cachedPositions, layoutEnergyValue, lossCurve, snapshots, timingLines, False)
          Nothing ->
            let (annealedPositions, annealStopStep, lossCurve, snapshots) =
                  iterateLayout 0 initialPositions [(0, layoutEnergy initialPositions)] []
                refinementTrace = refineLayout annealStopStep annealedPositions
                positions =
                  case refinementTrace of
                    [] -> annealedPositions
                    (_, finalPositions) : _ -> finalPositions
                polishedLossCurve =
                  [(step, layoutEnergy refinedPositions) | (step, refinedPositions) <- refinementTrace] ++ lossCurve
                polishedSnapshots =
                  [(step, layoutEnergy refinedPositions, refinedPositions) | (step, refinedPositions) <- refinementTrace] ++ snapshots
                layoutEnergyValue = layoutEnergy positions
                _forceResult =
                  forcePositionMap positions `seq`
                    layoutEnergyValue `seq`
                      length polishedLossCurve `seq`
                        length polishedSnapshots
                timingLines =
                  _forceResult `seq`
                    "% Dependency graph layout cache: miss"
                      : optimizationTimingLines (configTimingEnabled graphConfig)
             in (positions, layoutEnergyValue, reverse polishedLossCurve, reverse polishedSnapshots, timingLines, True)
 where
  allNodes = concatMap (sortOn headerIndex . snd) groups
  annealingSteps = 3000 :: Int
  lossSampleEvery = 100 :: Int
  annealingStopEnergyCeiling = 82.0 :: Double

  initialPositions =
    Map.fromList
      [ (node, initialNodePosition part nodeIdx count)
      | (part, groupNodes) <- groups
      , let sortedNodes = sortOn headerIndex groupNodes
            count = length sortedNodes
      , (nodeIdx, node) <- zip [(0 :: Int) ..] sortedNodes
      ]

  initialNodePosition part nodeIdx count =
    let box = boxes Map.! part
        center = boxCenter box
        radius = 0.34 + 0.08 * fromIntegral (min 4 count)
        angleJitter = 0.24 * sin (fromIntegral (nodeIdx + count) * 1.37)
        angle =
          2 * pi * fromIntegral nodeIdx / fromIntegral (max 1 count)
            + deterministicAngle (partIndex part * 97 + nodeIdx * 17 + count * 31)
            + angleJitter
        point =
          ( fst center + radius * cos angle
          , snd center + radius * sin angle
          )
     in clampToBox box point

  iterateLayout step positions lossCurve snapshots
    | step >= annealingSteps = (positions, step, lossCurve, snapshots)
    | otherwise =
        let nextStep = step + 1
            nextPositions =
              timedPositions "annealing step total" $
                improveByNearestSwaps nextStep $
                  timedPositions "annealing movement" $
                    projectByPart (advanceLayout step positions)
            shouldSample =
              nextStep `mod` lossSampleEvery == 0 || nextStep == annealingSteps
            nextEnergy =
              layoutEnergy nextPositions
            nextLossCurve =
              if nextStep `mod` lossSampleEvery == 0 || nextStep == annealingSteps
                then (nextStep, nextEnergy) : lossCurve
                else lossCurve
            nextSnapshots =
              if shouldSample
                then (nextStep, nextEnergy, nextPositions) : snapshots
                else snapshots
            shouldStop =
              shouldSample
                && nextStep < annealingSteps
                && nextEnergy <= annealingStopEnergyCeiling
                && annealingHasStalled nextEnergy lossCurve
         in if shouldStop
              then (nextPositions, nextStep, nextLossCurve, nextSnapshots)
              else iterateLayout nextStep nextPositions nextLossCurve nextSnapshots

  annealingHasStalled nextEnergy ((_, previousEnergy) : (_, beforePreviousEnergy) : _) =
    nextEnergy >= previousEnergy && previousEnergy >= beforePreviousEnergy
  annealingHasStalled _ _ = False

  advanceLayout step positions =
    Map.fromList
      [ (node, addPoint (positions Map.! node) (scalePoint (layoutStep step) (forceOn step positions node)))
      | node <- allNodes
      ]

  forceOn step positions node =
    addPoint
      (nodeSeparationForce positions node)
      ( addPoint
          (nodeClearanceForce positions node)
          ( addPoint
              (edgeDirectionForce positions node)
              ( addPoint
                  (edgeSpringForce positions node)
                  ( addPoint
                      (edgeNodeAvoidanceForce positions node)
                      (addPoint (partCenterForce positions node) (thermalForce step node))
                  )
              )
          )
      )

  nearestSamePartNode positions node =
    bestByDistance
      [ other
      | other <- allNodes
      , other /= node
      , nodePart other == nodePart node
      ]
   where
    bestByDistance [] = Nothing
    bestByDistance (candidate : candidates) =
      Just $
        foldl'
          ( \best candidate' ->
              if nodeDistance candidate' < nodeDistance best
                then candidate'
                else best
          )
          candidate
          candidates

    nodeDistance other =
      pointNorm (subPoint (positions Map.! node) (positions Map.! other))

  swapPositions left right positions =
    Map.insert left rightPoint (Map.insert right leftPoint positions)
   where
    leftPoint = positions Map.! left
    rightPoint = positions Map.! right

  nodeSeparationForce positions node =
    foldl'
      addPoint
      (0, 0)
      [ separationContribution (positions Map.! node) (positions Map.! other)
      | other <- allNodes
      , other /= node
      ]

  separationContribution here there =
    let delta = subPoint here there
        dist = max 0.08 (pointNorm delta)
        strength = nodeRepulsion / (dist * dist)
     in scalePoint (strength / dist) delta

  nodeClearanceForce positions node =
    foldl'
      addPoint
      (0, 0)
      [ clearanceContribution node other
      | other <- allNodes
      , other /= node
      ]
   where
    clearanceContribution hereNode thereNode =
      let here = positions Map.! hereNode
          there = positions Map.! thereNode
          delta = subPoint here there
          dist = max 0.08 (pointNorm delta)
       in if dist >= nodeClearance
            then (0, 0)
            else scalePoint (nodeClearanceRepulsion * (nodeClearance - dist) / dist) delta

  edgeSpringForce positions node =
    foldl'
      addPoint
      (0, 0)
      [ springContribution node other
      | other <- adjacentNodes node
      ]
   where
    springContribution hereNode thereNode =
      let here = positions Map.! hereNode
          there = positions Map.! thereNode
          delta = subPoint there here
          dist = max 0.08 (pointNorm delta)
          strength = edgeAttraction * (dist - springLength)
       in scalePoint (strength / dist) delta

  edgeDirectionForce positions node =
    foldl'
      addPoint
      (0, 0)
      [ directionContribution edge
      | edge <- edges
      , not (isReciprocalEdge edge)
      , edgeFrom edge == node || edgeTo edge == node
      ]
   where
    directionContribution edge =
      let (fromX, _) = positions Map.! edgeFrom edge
          (toX, _) = positions Map.! edgeTo edge
          shortfall = horizontalEdgeGap - (toX - fromX)
       in if shortfall <= 0
            then (0, 0)
            else
              let push = edgeDirectionAttraction * shortfall
               in if edgeFrom edge == node
                    then (-push, 0)
                    else (push, 0)

  isReciprocalEdge edge =
    any
      ( \other ->
          edgeFrom other == edgeTo edge
            && edgeTo other == edgeFrom edge
      )
      edges

  edgeNodeAvoidanceForce positions node =
    foldl'
      addPoint
      (0, 0)
      [ edgeAvoidanceContribution node edge
      | edge <- edges
      , edgeFrom edge /= node
      , edgeTo edge /= node
      ]
   where
    edgeAvoidanceContribution avoidNode edge =
      let point = positions Map.! avoidNode
          start = positions Map.! edgeFrom edge
          end = positions Map.! edgeTo edge
          nearest = closestPointOnSegment point start end
          delta = subPoint point nearest
          dist = max 0.08 (pointNorm delta)
       in if dist >= edgeClearance || not (pointBetweenEndpoints nearest start end)
            then (0, 0)
            else scalePoint (edgeNodeRepulsion * (edgeClearance - dist) / dist) (avoidanceDirection avoidNode delta)

    avoidanceDirection avoidNode delta
      | pointNorm delta > 0.001 = delta
      | otherwise =
          let angle = deterministicAngle (headerIndex avoidNode)
           in (cos angle, sin angle)

  partCenterForce positions node =
    case nodePart node of
      Nothing -> (0, 0)
      Just part ->
        scalePoint partAttraction $
          subPoint (boxCenter (boxes Map.! part)) (positions Map.! node)

  thermalForce step node =
    let temp = temperature step
        angle = deterministicAngle (headerIndex node * 97 + step * 31)
     in scalePoint temp (cos angle, sin angle)

  improveByNearestSwaps step positions =
    if configDisableAnnealingSwaps graphConfig
      then positions
      else
        timedPositions "annealing swap checks" $
          foldl' improveOne positions allNodes
   where
    improveOne current node =
      case nearestSamePartNode current node of
        Nothing -> current
        Just other ->
          let swapped = swapPositions node other current
              candidate =
                if step `mod` relaxedSwapEvery == 0
                  then relaxAfterSwap step relaxedSwapSteps swapped
                  else swapped
           in if layoutEnergy candidate < layoutEnergy current
                then candidate
                else current

  relaxAfterSwap step count positions =
    foldl'
      ( \current offset ->
          projectByPart (advanceLayout (step + offset) current)
      )
      positions
      [0 .. count - 1]

  relaxedSwapEvery = 100 :: Int
  relaxedSwapSteps = 3 :: Int

  refineLayout startStep positions =
    snd $
      foldl'
        refineBlock
        ((startStep, positions), [])
        [1 .. configuredNewtonBlockCount]

  refineBlock ((startStep, startPositions), trace) blockIndex =
    let blockInput =
          timedPositions "refinement swap search" $
            if blockIndex == 1 || configDisableRefinementSwaps graphConfig
              then startPositions
              else bestSwapForNextNewton startPositions
        (blockOutput, blockStep) = runNewtonBlock startStep blockInput
     in ((blockStep, blockOutput), (blockStep, blockOutput) : trace)

  runNewtonBlock startStep positions =
    (iterateNewton polishIterations positions, startStep + polishIterations)

  bestSwapForNextNewton positions =
    case sortOn
      (layoutEnergy . fst)
      [ (refined, swapped)
      | (left, right) <- refinementSwapCandidates positions
      , let swapped = swapPositions left right positions
            refined = iterateNewtonTimed "swap lookahead newton step" polishIterations swapped
      , layoutEnergy refined < layoutEnergy positions
      ] of
      [] -> positions
      (_, swapped) : _ -> swapped

  refinementSwapCandidates positions =
    take refinementSwapCandidateCount $
      sortOn (cheapSwapScore positions) allSamePartPairs

  cheapSwapScore positions (left, right) =
    layoutEnergy (swapPositions left right positions)

  newtonStep positions =
    firstImprovingStep positions (newtonDeltas positions)

  firstImprovingStep positions deltas =
    asum
      [ let candidate = applyDeltas scale deltas positions
         in if layoutEnergy candidate < layoutEnergy positions
              then Just candidate
              else Nothing
      | scale <- polishLineSearchScales
      ]

  allSamePartPairs =
    [ (left, right)
    | (idx, left) <- zip [(0 :: Int) ..] allNodes
    , right <- drop (idx + 1) allNodes
    , nodePart left == nodePart right
    ]

  iterateNewton = iterateNewtonTimed "newton refine step"

  iterateNewtonTimed label count positions =
    foldl'
      (\current _ -> timedPositions label (fromMaybe current (newtonStep current)))
      positions
      [1 .. count]

  applyDeltas scale deltas positions =
    projectByPart $
      Map.mapWithKey
        ( \node point ->
            case Map.lookup node deltas of
              Nothing -> point
              Just delta -> addPoint point (scalePoint scale delta)
        )
        positions

  newtonDeltas positions =
    Map.fromList
      [ (node, (coordinateDelta positions node True, coordinateDelta positions node False))
      | node <- allNodes
      ]

  coordinateDelta positions node isX =
    let baseEnergy = layoutEnergy positions
        plus = perturbCoordinate polishEpsilon node isX positions
        minus = perturbCoordinate (negate polishEpsilon) node isX positions
        plusEnergy = layoutEnergy plus
        minusEnergy = layoutEnergy minus
        gradient = (plusEnergy - minusEnergy) / (2 * polishEpsilon)
        curvature =
          max
            polishMinCurvature
            ((plusEnergy - 2 * baseEnergy + minusEnergy) / (polishEpsilon * polishEpsilon))
     in clamp (negate polishMaxStep) polishMaxStep (negate gradient / curvature)

  perturbCoordinate delta node isX positions =
    projectByPart $
      Map.adjust (moveCoordinate delta isX) node positions

  moveCoordinate delta isX (x, y)
    | isX = (x + delta, y)
    | otherwise = (x, y + delta)

  layoutEnergy positions =
    nodeClearanceEnergy positions
      + edgeNodeEnergy positions
      + edgeDirectionEnergy positions
      + edgeLengthEnergy positions

  nodeClearanceEnergy positions =
    sum
      [ let dist = pointNorm (subPoint (positions Map.! left) (positions Map.! right))
            shortfall = max 0 (nodeClearance - dist)
         in shortfall * shortfall
      | (idx, left) <- zip [(0 :: Int) ..] allNodes
      , right <- drop (idx + 1) allNodes
      ]

  edgeNodeEnergy positions =
    sum
      [ let point = positions Map.! node
            start = positions Map.! edgeFrom edge
            end = positions Map.! edgeTo edge
            dist = pointSegmentDistance point start end
            shortfall = max 0 (edgeClearance - dist)
         in if node == edgeFrom edge || node == edgeTo edge || not (pointBetweenEndpoints point start end)
              then 0
              else shortfall * shortfall
      | node <- allNodes
      , edge <- edges
      ]

  edgeDirectionEnergy positions =
    sum
      [ let (fromX, _) = positions Map.! edgeFrom edge
            (toX, _) = positions Map.! edgeTo edge
            shortfall = max 0 (horizontalEdgeGap - (toX - fromX))
         in if isReciprocalEdge edge
              then 0
              else edgeDirectionWeight * shortfall * shortfall
      | edge <- edges
      ]

  edgeLengthEnergy positions =
    sum
      [ let dist = pointNorm (subPoint (positions Map.! edgeFrom edge) (positions Map.! edgeTo edge))
            excess = dist - springLength
         in 0.04 * excess * excess
      | edge <- edges
      ]

  adjacentNodes node =
    concat
      [ [edgeTo edge | edgeFrom edge == node]
          ++ [edgeFrom edge | edgeTo edge == node]
      | edge <- edges
      ]

  -- Precomputed once; the force and projection loops look a node's part up
  -- here every step instead of rescanning the group lists with `elem`.
  nodePartMap =
    Map.fromList
      [ (node, part)
      | (part, groupNodes) <- groups
      , node <- groupNodes
      ]

  nodePart node = Map.lookup node nodePartMap

  projectByPart = Map.mapWithKey projectOne

  projectOne node point =
    case nodePart node of
      Nothing -> point
      Just part -> clampToBox (boxes Map.! part) point

  layoutStep step = 0.018 + 0.095 * temperature step
  temperature step =
    let progress = fromIntegral step / fromIntegral annealingSteps
        slowCool = 1 - progress
        finalQuench = slowCool * slowCool
        baseTemperature =
          if progress < 0.72
            then slowCool ** 0.55
            else finalQuench
     in initialTemperature * baseTemperature
  nodeRepulsion = 0.38
  nodeClearanceRepulsion = 2.20
  nodeClearance = 1.45
  edgeAttraction = 0.055
  edgeDirectionAttraction = 0.08
  edgeDirectionWeight = 1.25
  horizontalEdgeGap = 1.00
  edgeNodeRepulsion = 2.40
  edgeClearance = 0.92
  partAttraction = 0.02
  springLength = 1.85
  initialTemperature = 2.45
  polishIterations = 40 :: Int
  newtonBlockCount = 10 :: Int
  configuredNewtonBlockCount = fromMaybe newtonBlockCount (configNewtonBlockOverride graphConfig)
  refinementSwapCandidateCount = 8 :: Int
  polishEpsilon = 0.015
  polishMinCurvature = 0.05
  polishMaxStep = 0.18
  polishLineSearchScales = [1.0, 0.5, 0.25, 0.125, 0.0625] :: [Double]

dependencyFrameBodyLines :: Map PartInfo LayoutBox -> [Text]
dependencyFrameBodyLines boxes =
  map frameLine (sortOn (partIndex . fst) (Map.toList boxes))
 where
  frameLine (part, box) =
    "\\node[depframe, label={[font=\\scriptsize]above:"
      <> partName part
      <> "}, minimum width="
      <> tshow (boxRight box - boxLeft box)
      <> "cm, minimum height="
      <> tshow (boxTop box - boxBottom box)
      <> "cm] at ("
      <> tshow (boxCenterX box)
      <> ","
      <> tshow (boxCenterY box)
      <> ") {};"

boxCenter :: LayoutBox -> (Double, Double)
boxCenter box = (boxCenterX box, boxCenterY box)

boxCenterX :: LayoutBox -> Double
boxCenterX box = (boxLeft box + boxRight box) / 2

boxCenterY :: LayoutBox -> Double
boxCenterY box = (boxTop box + boxBottom box) / 2

clampToBox :: LayoutBox -> (Double, Double) -> (Double, Double)
clampToBox box (x, y) =
  ( clamp (boxLeft box + margin) (boxRight box - margin) x
  , clamp (boxBottom box + margin) (boxTop box - margin) y
  )
 where
  margin = 0.72

clamp :: (Ord a) => a -> a -> a -> a
clamp lower upper = min upper . max lower

addPoint :: (Double, Double) -> (Double, Double) -> (Double, Double)
addPoint (x1, y1) (x2, y2) = (x1 + x2, y1 + y2)

subPoint :: (Double, Double) -> (Double, Double) -> (Double, Double)
subPoint (x1, y1) (x2, y2) = (x1 - x2, y1 - y2)

scalePoint :: Double -> (Double, Double) -> (Double, Double)
scalePoint factor (x, y) = (factor * x, factor * y)

pointNorm :: (Double, Double) -> Double
pointNorm (x, y) = sqrt (x * x + y * y)

pointSegmentDistance :: (Double, Double) -> (Double, Double) -> (Double, Double) -> Double
pointSegmentDistance point start end =
  pointNorm (subPoint point (closestPointOnSegment point start end))

closestPointOnSegment :: (Double, Double) -> (Double, Double) -> (Double, Double) -> (Double, Double)
closestPointOnSegment point start end =
  addPoint start (scalePoint t segment)
 where
  segment = subPoint end start
  lenSq = dotPoint segment segment
  rawT
    | lenSq <= 0.0001 = 0
    | otherwise = dotPoint (subPoint point start) segment / lenSq
  t = clamp 0 1 rawT

pointBetweenEndpoints :: (Double, Double) -> (Double, Double) -> (Double, Double) -> Bool
pointBetweenEndpoints point start end =
  dotPoint (subPoint point start) (subPoint point end) < 0

dotPoint :: (Double, Double) -> (Double, Double) -> Double
dotPoint (x1, y1) (x2, y2) = x1 * x2 + y1 * y2

deterministicAngle :: Int -> Double
deterministicAngle seed =
  2 * pi * frac (sin (fromIntegral seed * 12.9898) * 43758.5453)
 where
  frac x = x - fromIntegral (floor x :: Int)

optimizationTimingRef :: IORef (Map Text OptimizationTiming)
optimizationTimingRef = unsafePerformIO (newIORef Map.empty)
{-# NOINLINE optimizationTimingRef #-}

optimizationTimingEnabledRef :: IORef Bool
optimizationTimingEnabledRef = unsafePerformIO (newIORef False)
{-# NOINLINE optimizationTimingEnabledRef #-}

resetOptimizationTimings :: Bool -> ()
resetOptimizationTimings enabled =
  unsafePerformIO $ do
    writeIORef optimizationTimingEnabledRef enabled
    writeIORef optimizationTimingRef Map.empty
{-# NOINLINE resetOptimizationTimings #-}

timedPositions :: Text -> Map HeaderInfo (Double, Double) -> Map HeaderInfo (Double, Double)
timedPositions label positions =
  unsafePerformIO $ do
    enabled <- readIORef optimizationTimingEnabledRef
    when enabled $ do
      start <- getCurrentTime
      let forced = forcePositionMap positions
      forced `seq` pure ()
      finish <- getCurrentTime
      recordOptimizationTiming label (durationToPicos (diffUTCTime finish start))
    pure positions
{-# NOINLINE timedPositions #-}

forcePositionMap :: Map HeaderInfo (Double, Double) -> Double
forcePositionMap =
  Map.foldl' (\total (x, y) -> total + x + y) 0

recordOptimizationTiming :: Text -> Integer -> IO ()
recordOptimizationTiming label duration =
  modifyIORef' optimizationTimingRef $
    Map.insertWith combine label (OptimizationTiming 1 duration)
 where
  combine new old =
    OptimizationTiming
      { timingCount = timingCount old + timingCount new
      , timingPicos = timingPicos old + timingPicos new
      }

optimizationTimingLines :: Bool -> [Text]
optimizationTimingLines enabled
  | not enabled = []
  | otherwise =
      unsafePerformIO $ do
        timings <- readIORef optimizationTimingRef
        pure $
          "% Dependency graph optimization timing: label count total-ms avg-ms"
            : [ "%   "
                  <> label
                  <> " "
                  <> tshow count
                  <> " "
                  <> formatMilliseconds totalPicos
                  <> " "
                  <> formatMilliseconds (totalPicos `div` fromIntegral count)
              | (label, OptimizationTiming count totalPicos) <- Map.toList timings
              , count > 0
              ]
{-# NOINLINE optimizationTimingLines #-}

formatMilliseconds :: Integer -> Text
formatMilliseconds picos =
  T.pack (show value)
 where
  value = fromIntegral picos / 1000000000 :: Double

durationToPicos :: (Real a) => a -> Integer
durationToPicos duration =
  floor (realToFrac duration * (1000000000000 :: Double))

dependencyLayoutCacheSignature :: OptimizationConfig -> [(PartInfo, [HeaderInfo])] -> Map PartInfo LayoutBox -> [DependencyEdge] -> Text
dependencyLayoutCacheSignature graphConfig groups boxes edges =
  T.intercalate
    "|"
    [ "dependency-layout-v1"
    , "annealing-swaps=" <> boolText (not (configDisableAnnealingSwaps graphConfig))
    , "refinement-swaps=" <> boolText (not (configDisableRefinementSwaps graphConfig))
    , "newton-blocks=" <> maybe "default" tshow (configNewtonBlockOverride graphConfig)
    , "refinement-candidates=8"
    , "node-clearance=1.45"
    , "edge-direction-weight=1.25"
    , "edge-direction-attraction=0.08"
    , "edge-length-weight=0.04"
    , "groups=" <> T.intercalate "," (map groupSignature groups)
    , "boxes=" <> T.intercalate "," (map boxSignature (sortOn (partIndex . fst) (Map.toList boxes)))
    , "edges=" <> T.intercalate "," (map edgeSignature edges)
    ]
 where
  groupSignature (part, groupNodes) =
    partName part <> ":" <> T.intercalate "/" (map headerId (sortOn headerIndex groupNodes))

  boxSignature (part, box) =
    partName part
      <> ":"
      <> T.intercalate "/" (map tshow [boxLeft box, boxRight box, boxTop box, boxBottom box])

  edgeSignature edge =
    headerId (edgeFrom edge) <> ">" <> headerId (edgeTo edge) <> ":" <> tshow (edgeCount edge)

  boolText True = "true"
  boolText False = "false"

{- | Read cached layout positions from @path@, returning 'Nothing' when the file
is absent/unreadable or its signature does not match. A plain 'IO' action:
the caller runs it in 'processDoc' and hands the result to
'renderDependencyGraph'.
-}
readDependencyLayoutCache :: FilePath -> Text -> [HeaderInfo] -> IO (Maybe (Map HeaderInfo (Double, Double)))
readDependencyLayoutCache path signature nodes =
  ( do
      content <- TIO.readFile path
      pure (parseDependencyLayoutCache signature nodes content)
  )
    `catch` dependencyLayoutCacheReadFailed

dependencyLayoutCacheReadFailed :: IOException -> IO (Maybe (Map HeaderInfo (Double, Double)))
dependencyLayoutCacheReadFailed _ =
  pure Nothing

parseDependencyLayoutCache :: Text -> [HeaderInfo] -> Text -> Maybe (Map HeaderInfo (Double, Double))
parseDependencyLayoutCache signature nodes content =
  case T.lines content of
    firstLine : positionLines
      | firstLine == "signature\t" <> signature -> do
          positionsById <- Map.fromList <$> mapM parsePositionLine positionLines
          nodePositions <-
            mapM
              ( \node -> do
                  point <- Map.lookup (headerId node) positionsById
                  pure (node, point)
              )
              nodes
          pure (Map.fromList nodePositions)
    _ -> Nothing
 where
  parsePositionLine line =
    case T.splitOn "\t" line of
      [nodeId, rawX, rawY] -> do
        x <- readMaybeDouble (T.unpack rawX)
        y <- readMaybeDouble (T.unpack rawY)
        pure (nodeId, (x, y))
      _ -> Nothing

{- | Persist freshly computed layout positions to @path@ (creating the parent
directory). The caller writes back the positions 'renderDependencyGraph'
returns on a cache miss.
-}
writeDependencyLayoutCache :: FilePath -> Text -> [HeaderInfo] -> Map HeaderInfo (Double, Double) -> IO ()
writeDependencyLayoutCache path signature nodes positions = do
  ensureParentDirectory path
  TIO.writeFile path $
    T.unlines $
      ("signature\t" <> signature)
        : [ headerId node <> "\t" <> tshow x <> "\t" <> tshow y
          | node <- nodes
          , let (x, y) = positions Map.! node
          ]

ensureParentDirectory :: FilePath -> IO ()
ensureParentDirectory path =
  createDirectoryIfMissing True directory
 where
  directory =
    case reverse (dropWhile (/= '/') (reverse path)) of
      "" -> "."
      dir -> dir

readMaybeDouble :: String -> Maybe Double
readMaybeDouble input =
  case reads input of
    [(value, "")] -> Just value
    _ -> Nothing

tshow :: (Show a) => a -> Text
tshow = T.pack . show

{-# LANGUAGE OverloadedStrings #-}

module DependencyGraphTests (runDependencyPlanTests) where

import qualified Data.Map.Strict as Map
import Data.Maybe (isJust)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import DependencyGraph
import SectionRef (nextSectionRef)
import System.FilePath ((</>))
import Text.Pandoc.Definition

runDependencyPlanTests :: FilePath -> IO [String]
runDependencyPlanTests tmp = do
  cacheFailures <- mapM finiteCache ["NaN", "Infinity", "-Infinity", "1e9999"]
  pure (semanticFailures ++ concat cacheFailures)
 where
  config = OptimizationConfig False False False Nothing
  header name = Header 1 (name, [], []) [Str name]
  part = RawBlock (Format "tex") "\\part{Part}"
  references names = Para [Str (T.concat ["§{" <> name <> "}" | name <- names])]
  plan =
    planDependencyGraph
      False
      Set.empty
      ( Pandoc
          nullMeta
          [part, header "a", references ["b-sub", "b-sub"], part, header "b", Header 2 ("b-sub", [], []) [Str "Subsection"], references ["a"]]
      )
  edgeTuples graph = Set.fromList [(headerId (edgeFrom edge), headerId (edgeTo edge), edgeCount edge) | edge <- dgEdges graph]
  grouped graph = [(partName p, map headerId nodes) | (p, nodes) <- dgGroups graph]
  capPlan =
    planDependencyGraph
      False
      Set.empty
      ( Pandoc
          nullMeta
          (part : header "c0" : references ["c" <> T.pack (show n) | n <- [1 .. 20 :: Int]] : [header ("c" <> T.pack (show n)) | n <- [1 .. 20 :: Int]])
      )
  manyParts =
    planDependencyGraph
      False
      Set.empty
      ( Pandoc
          nullMeta
          ( concat
              [[part, header (name n), references [name (n `mod` 8 + 1)]] | n <- [1 .. 8 :: Int]]
          )
      )
  name n = "chapter" <> T.pack (show n)
  boxes = Map.elems (dgBoxes manyParts)
  overlap a b =
    max (boxLeft a) (boxLeft b) < min (boxRight a) (boxRight b)
      && max (boxBottom a) (boxBottom b) < min (boxTop a) (boxTop b)
  malformedParts =
    planDependencyGraph
      False
      Set.empty
      ( Pandoc
          nullMeta
          [ RawBlock (Format "tex") "% \\part{comment}\n\\newcommand{\\p}{\n\\part{macro}\n}\n\\begin{verbatim}\n\\part{literal}\n\\end{verbatim}\n\\part{First}\n\\part{Second}"
          , header "a"
          , references ["b"]
          , part
          , header "b"
          , references ["a"]
          ]
      )
  orphan =
    planDependencyGraph
      False
      Set.empty
      ( Pandoc
          nullMeta
          [header "orphan", references ["a"], part, header "a", references ["orphan"]]
      )
  excluded =
    planDependencyGraph
      False
      (Set.singleton "b")
      ( Pandoc
          nullMeta
          [part, header "a", references ["b"], header "b", references ["a"]]
      )
  signature = planCacheSignature config plan
  semanticFailures =
    ["graph must count subsection references toward their chapter and point prerequisite -> referring chapter" | edgeTuples plan /= Set.fromList [("b", "a", 2), ("a", "b", 1)]]
      ++ ["graph chapter-to-part grouping drifted" | grouped plan /= [("Part I", ["a"]), ("Part II", ["b"])]]
      ++ ["reciprocal edges must include both directions" | Set.size (dgReciprocal plan) /= 2]
      ++ ["excluded chapters must not leave edges or nodes" | not (null (dgEdges excluded) && null (dgNodes excluded))]
      ++ ["edge-cap omission counts drifted" | length (dgEdges capPlan) /= 18 || dgOmittedEdges capPlan /= 2 || dgOmittedNodes capPlan /= 2]
      ++ ["eight-part graph frames overlap or lose groups" | length boxes /= 8 || or [overlap a b | (i, a) <- zip [0 :: Int ..] boxes, b <- drop (i + 1) boxes]]
      ++ ["comments, macro bodies or verbatim created phantom parts, or two part lines collapsed" | map (partName . fst) (dgGroups malformedParts) /= ["Part II", "Part III"]]
      ++ ["partless chapter must remain in collection but not in the layout" | length (dgNodes orphan) /= 2 || length (planCacheNodes orphan) /= 1 || not (null (dgLayoutEdges orphan))]
      ++ ["layout signature lacks the implementation fingerprint" | not ("implementation=" `T.isInfixOf` signature)]
      ++ ["optimizer configuration must change layout signature" | signature == planCacheSignature config{configNewtonBlockOverride = Just 3} plan]
      ++ ["section-reference tokenizer boundary changed" | or [nextSectionRef text /= expected | (text, expected) <- sectionCases]]
  sectionCases :: [(Text, Maybe (Text, Text, Text))]
  sectionCases = [("", Nothing), ("§", Nothing), ("§{unclosed", Nothing), ("§{}", Just ("", "", "")), ("x§{a}§{b}", Just ("x", "a", "§{b}")), ("§{a§{b}", Just ("", "a§{b", ""))]
  finiteCache raw = do
    let path = tmp </> "nonfinite-cache"
        node = HeaderInfo 1 1 "node"
    TIO.writeFile path ("signature\ttest\nnode\t" <> raw <> "\t0\n")
    result <- readDependencyLayoutCache path "test" [node]
    pure ["nonfinite cached coordinate was accepted: " <> T.unpack raw | isJust result]

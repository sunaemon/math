{-# LANGUAGE OverloadedStrings #-}

{- | Recognition produces candidates only. The temporary JSON adapter preserves
annotations from the Python interpreter while its remaining callers migrate.
-}
module StructuralSyntax (structuralRequest, extractBindings, expressionList, alignedRows, conjunctionShape, indexedSingletons, normalTokens, expressionTokens, ballFamilies, naturalFamilies, convergenceShape, summationChunks, predicateSets, boundedInfimum, casesNode, isDecimal, decimal, SequenceCandidate (..), sequenceCandidate) where

import Control.Monad (foldM)
import Data.Aeson (Value (..), object, toJSON, withObject, (.:), (.=))
import qualified Data.Aeson.Key as K
import qualified Data.Aeson.KeyMap as KM
import Data.Aeson.Types (Parser, parseMaybe)
import Data.Char (GeneralCategory (DecimalNumber), generalCategory, isAlpha, isDigit, isSpace, ord)
import Data.Foldable (toList)
import Data.Maybe (fromMaybe, listToMaybe)
import Data.Text (Text)
import qualified Data.Text as T
import LocatedMath (SourceSpan (..))
import SemanticExpr (macroNames)

-- An observed sequence binder is not a resolved binding or an approved meaning.
data SequenceCandidate = SequenceCandidate Text Integer Int [(SourceSpan, Text)]

field :: Text -> Value -> Value
field key (Object fields) = fromMaybe Null (KM.lookup (K.fromText key) fields)
field _ _ = Null

text :: Value -> Text
text (String value) = value
text _ = ""

label :: Text -> Value -> Text
label key = text . field key

items :: Text -> Value -> [Value]
items key value = case field key value of
  Array values -> toList values
  _ -> []

integer :: Value -> Int
integer value = fromMaybe 0 (parseMaybe parseInt value)
 where
  parseInt v = case v of
    Number n | fromInteger (round n) == n -> pure (round n)
    _ -> fail "Expected integer"

start :: Value -> Int
start = integer . field "start"

patch :: Value -> [(Text, Value)] -> Value
patch (Object fields) changes = Object (foldr (uncurry (KM.insert . K.fromText)) fields changes)
patch value _ = value

number :: Int -> Value
number = Number . fromIntegral

isKind :: Text -> Value -> Bool
isKind kind node = label "kind" node == kind

isDecimal :: Text -> Bool
isDecimal value = not (T.null value) && T.all ((== DecimalNumber) . generalCategory) value

-- Unicode decimal blocks contain runs of ten digits, sometimes adjacent blocks.
-- Using ASCII read would silently lose the parser's Unicode index support.
decimal :: Text -> Integer
decimal = T.foldl' (\n c -> n * 10 + fromIntegral (digit c)) 0
 where
  digit c = (ord c - beginning (ord c)) `mod` 10
  beginning n
    | n > 0 && generalCategory (toEnum (n - 1)) == DecimalNumber = beginning (n - 1)
    | otherwise = n

blank :: Value -> Bool
blank node = let value = label "text" node in not (T.null value) && T.all isSpace value

simpleCommand :: Text -> Value -> Bool
simpleCommand name node = isKind "command" node && label "name" node == name && null (items "args" node) && field "optional" node == Null

expressionTokens :: Value -> Either String [Value]
expressionTokens node
  | isKind "command" node && any (`simpleCommand` node) [",", ";", "!", "quad", "qquad", " "] = Right []
  | isKind "text" node = Right (reverse (foldl token [] (zip [start node ..] (T.unpack (label "text" node)))))
  | isKind "script" node = do
      base <- expressionTokens (field "base" node)
      case reverse base of
        [] -> Left "Empty script base."
        lastToken : before ->
          let (digits, prefix) = span (isDecimal . label "text") (lastToken : before)
              combined = object ["kind" .= ("text" :: Text), "text" .= T.concat (map (label "text") (reverse digits)), "start" .= start (last digits), "end" .= field "end" (field "base" node)]
              refined = if label "marker" node == "^" && not (null digits) then combined : prefix else lastToken : before
           in case refined of
                final : rest -> Right (reverse rest <> [patch node [("base", final), ("start", number (start final))]])
                [] -> Left "Empty script base."
  | otherwise = Right [node]
 where
  token (previous : rest) (offset, '\'')
    | isKind "bound-symbol" previous || (not (T.null (label "text" previous)) && T.all isAlpha (label "text" previous)) =
        patch previous [("kind", String "bound-symbol"), ("text", String (label "text" previous <> "'")), ("end", number (offset + 1))] : rest
  token previous (offset, char) = object ["kind" .= ("text" :: Text), "text" .= T.singleton char, "start" .= offset] : previous

sequenceCandidate :: Value -> Either String (Maybe SequenceCandidate)
sequenceCandidate node
  | not (isKind "command" node && label "name" node == "Sequence" && field "optional" node == Null) = Right Nothing
  | [_, domain] <- items "args" node
  , isKind "sequence" domain = do
      tokens <- concatMap (filter (not . blank)) <$> traverse expressionTokens (items "items" domain)
      let merged = case tokens of
            variable : relation : digits@(firstDigit : _ : _)
              | all (\v -> isKind "text" v && isDecimal (label "text" v)) digits
              , and (zipWith (\a b -> start b == start a + T.length (label "text" a)) digits (drop 1 digits)) ->
                  [variable, relation, patch firstDigit [("text", String (T.concat (map (label "text") digits))), ("end", number (start (last digits) + T.length (label "text" (last digits))))]]
            _ -> tokens
      pure $ case merged of
        [variable, relation, carrier]
          | isKind "text" variable
          , not (T.null (label "text" variable))
          , T.all isAlpha (label "text" variable)
          , Just offset <- origin relation carrier ->
              Just
                ( SequenceCandidate
                    (label "text" variable)
                    offset
                    (start variable)
                    [ (SourceSpan (start variable) (start variable + T.length (label "text" variable)), "lambda.binder")
                    , (SourceSpan (start relation) (start relation + T.length (label "name" relation) + 1), "lambda.domain")
                    , (SourceSpan (start carrier) (carrierEnd carrier), "lambda.domain")
                    ]
                )
        _ -> Nothing
  | otherwise = Right Nothing
 where
  origin relation carrier
    | simpleCommand "ge" relation && isKind "text" carrier && isDecimal (label "text" carrier) = Just (decimal (label "text" carrier))
    | simpleCommand "in" relation && simpleCommand "omega" carrier = Just 0
    | otherwise = Nothing
  carrierEnd carrier = case field "end" carrier of
    Null -> start carrier + T.length (if isKind "command" carrier then label "name" carrier else label "text" carrier) + if isKind "command" carrier then 1 else 0
    value -> integer value

sequenceValue :: SequenceCandidate -> Value
sequenceValue (SequenceCandidate symbol origin declaration components) =
  object
    [ "symbol" .= symbol
    , "leanType" .= ("ℕ" :: Text)
    , "indexOffset" .= origin
    , "declarationOffset" .= declaration
    , "components" .= [object ["start" .= a, "end" .= b, "target" .= target] | (SourceSpan a b, target) <- components]
    ]

decoratedName :: Bool -> Value -> Maybe Value
decoratedName star node
  | isKind "script" node
  , label "marker" node == (if star then "^" else "_")
  , let base = field "base" node
  , isKind "text" base
  , Just (_, lastChar) <- T.unsnoc (label "text" base)
  , isAlpha lastChar
  , Just argument <- unwrap (field "argument" node)
  , let suffix = label "text" argument
  , if star then suffix == "*" else isKind "text" argument && not (T.null suffix) && T.all isDigit suffix =
      Just (object ["symbol" .= (T.singleton lastChar <> (if star then "^*" else "_" <> suffix)), "start" .= (start base + T.length (label "text" base) - 1), "end" .= field "end" node])
  | otherwise = Nothing
 where
  unwrap value
    | isKind "group" value = unwrap (field "body" value)
    | isKind "sequence" value = case (if star then filter (not . blank) else id) (items "items" value) of
        [child] -> unwrap child
        _ -> Nothing
    | otherwise = Just value

normalTokens :: Value -> Either String [Value]
normalTokens node = concatMap (filter (not . blank)) <$> traverse expressionTokens (items "items" node)

identifier :: Value -> Bool
identifier node = isKind "text" node && T.length (label "text" node) == 1 && T.all isAlpha (label "text" node)

conjunctionToken :: Value -> Bool
conjunctionToken node =
  isKind "command" node && label "name" node == "text" && field "optional" node == Null && case items "args" node of
    [argument] -> isKind "sequence" argument && all (isKind "text") (items "items" argument) && T.concat (map (label "text") (items "items" argument)) == "and"
    _ -> False

sequenceNode :: [Value] -> Value
sequenceNode [] = Null
sequenceNode values@(first : _) = object ["kind" .= ("sequence" :: Text), "items" .= values, "start" .= start first, "end" .= end (last values)]
 where
  end v = case field "end" v of
    Null -> start v + T.length (label "text" v)
    value -> integer value

conjunctionShape :: Value -> Either String Value
conjunctionShape node
  | not (isKind "sequence" node) = Right Null
  | otherwise = split 0 [] <$> normalTokens node
 where
  split :: Int -> [Value] -> [Value] -> Value
  split _ _ [] = Null
  split depth previous (token : rest)
    | nextDepth == 0 && conjunctionToken token = if null previous || null rest then Null else object ["clauses" .= [sequenceNode (reverse previous), sequenceNode rest], "operator" .= token]
    | otherwise = split nextDepth (token : previous) rest
   where
    nextDepth = depth + if label "text" token == "(" then 1 else if label "text" token == ")" then -1 else 0

mapstoShape :: Value -> Either String Value
mapstoShape node
  | not (isKind "sequence" node) = Right Null
  | otherwise = do
      tokens <- normalTokens node
      let arrows = [i | (i, t) <- zip [0 :: Int ..] tokens, label "name" t == "mapsto"]
          result = object ["tokens" .= tokens]
      pure $ case (arrows, tokens) of
        ([], _) -> Null
        ([1], point : arrow : body@(_ : _)) | identifier point, simpleCommand "mapsto" arrow -> patch result [("point", point), ("arrow", arrow), ("body", toJSON body)]
        _ -> result

typedMapShape :: Value -> Either String Value
typedMapShape node
  | not (isKind "sequence" node) = Right Null
  | otherwise = do
      tokens <- normalTokens node
      let arrows = [i | (i, t) <- zip [0 :: Int ..] tokens, label "name" t == "to"]
          commas = [i | (i, t) <- zip [0 :: Int ..] tokens, label "text" t == ","]
          identity t = (label "kind" t, if field "name" t == Null then field "text" t else field "name" t)
      pure $ case (tokens, arrows, commas) of
        (function : colon : domain : arrow : _, [3], comma : _)
          | length tokens >= 12
          , label "text" colon == ":"
          , comma > 4
          , equation@(name : opening : point : closing : equals : _ : _) <- drop (comma + 1) tokens
          , identity function == identity name
          , map (label "text") [opening, closing, equals] == ["(", ")", "="]
          , identifier point ->
              object ["function" .= function, "domain" .= domain, "codomain" .= take (comma - 4) (drop 4 tokens), "colon" .= colon, "arrow" .= arrow, "equation" .= equation, "point" .= point]
        _ -> Null

boundedInfimum :: Value -> Either String Value
boundedInfimum node
  | not (isKind "sequence" node) = Right Null
  | otherwise = do
      tokens <- normalTokens node
      pure $ case (tokens, reverse tokens) of
        (op : opening : _, closing : domain : relation : binder : colon : _)
          | length tokens >= 8
          , simpleCommand "inf" op
          , simpleCommand "{" opening
          , simpleCommand "}" closing
          , simpleCommand "in" relation
          , identifier binder
          , identifier domain
          , label "text" colon == ":"
          , let body = take (length tokens - 7) (drop 2 tokens)
          , not (any (\t -> label "name" t `elem` ["Sequence", "IndexedFamily", "ExternalDisjointUnion", "prod", "sum", "bigcap", "bigcup", "inf", "mapsto", "{", "}"]) body) ->
              object ["tokens" .= tokens, "body" .= body, "binder" .= binder, "domain" .= domain, "relation" .= relation]
        _ -> Null

alignedRows :: Value -> Either String Value
alignedRows node
  | not (isKind "sequence" node) = Right Null
  | otherwise = do
      tokens <- normalTokens node
      pure $ case tokens of
        first : rest
          | length rest >= 2
          , boundary "begin" first
          , boundary "end" (last rest) ->
              maybe Null toJSON (splitRows [] [] (init rest) >>= traverse clean)
        _ -> Null
 where
  boundary name value =
    isKind "command" value && label "name" value == name && field "optional" value == Null && case items "args" value of
      [arg] | isKind "sequence" arg -> case items "items" arg of
        [word] -> label "text" word == "aligned"
        _ -> False
      _ -> False
  splitRows done current [] = if null current then Nothing else Just (done <> [current])
  splitRows done current (token : rest)
    | label "name" token `elem` ["begin", "end"] = Nothing
    | label "name" token == "\\" = if null current || not (null (items "args" token)) || field "optional" token /= Null then Nothing else splitRows (done <> [current]) [] rest
    | otherwise = splitRows done (current <> [token]) rest
  clean row
    | length (filter ((== "&") . label "text") row) > 1 = Nothing
    | otherwise =
        let without = filter ((/= "&") . label "text") row
            stripped = if not (null without) && label "text" (last without) `elem` [",", "."] then init without else without
         in if null stripped then Nothing else Just (object ["kind" .= ("sequence" :: Text), "items" .= stripped, "start" .= start (headSafe stripped), "end" .= field "end" (last stripped)])
  headSafe (x : _) = x
  headSafe [] = Null

expressionList :: Value -> Either String Value
expressionList node
  | isKind "contextual-interpretations" node = Right (field "interpretations" node)
  | not (isKind "sequence" node) = Right Null
  | otherwise = do
      aligned <- alignedRows node
      if aligned /= Null
        then Right aligned
        else do
          tokens <- normalTokens node
          valid <- traverse entry [v | (i, v) <- zip [0 :: Int ..] tokens, even i]
          pure $
            if length tokens < 3 || even (length tokens) || not (and valid) || not (and [label "text" v == "," | (i, v) <- zip [0 :: Int ..] tokens, odd i])
              then Null
              else toJSON [sequenceNode [v] | (i, v) <- zip [0 :: Int ..] tokens, even i]
 where
  entry node'
    | identifier node' = Right True
    | isKind "script" node'
    , label "marker" node' == "_" = do
        base <- expressionTokens (field "base" node')
        index <- expressionTokens (field "argument" node')
        pure $ case (base, index) of
          ([a], [b]) -> identifier a && (identifier b || isKind "text" b && isDecimal (label "text" b))
          _ -> False
    | otherwise = Right False

convergenceShape :: Value -> Either String Value
convergenceShape node
  | not (isKind "sequence" node) = Right Null
  | otherwise = do
      tokens <- concat <$> traverse expressionTokens (items "items" node)
      case arrows 0 0 tokens of
        [position] -> do
          let left = take position tokens
              scripts = concatMap (filter (isKind "script") . visit) left
              blocked = any (any (\v -> isKind "command" v && label "name" v `elem` ["Sequence", "IndexedFamily", "ExternalDisjointUnion", "prod", "sum", "bigcap", "bigcup", "inf", "mapsto"]) . visit) left
              indices = map (field "argument") scripts
              basic = object ["left" .= left, "right" .= drop (position + 1) tokens, "arrow" .= (tokens !! position)]
          if null scripts
            then Right Null
            else
              if blocked || not (all (\v -> label "marker" v `elem` ["_", "^"] && identifier (field "argument" v)) scripts) || not (all ((== label "text" (first indices)) . label "text") indices)
                then Right basic
                else do
                  families <- traverse (expressionTokens . field "base") scripts
                  unlessNonempty families
                  let binder =
                        object
                          [ "symbol" .= label "text" (first indices)
                          , "leanType" .= ("ℕ" :: Text)
                          , "declarationOffset" .= start (first indices)
                          , "familyOffsets" .= map (start . last) families
                          , "components" .= [object ["start" .= start i, "end" .= field "end" i, "target" .= ("sequence.lambda.binder" :: Text)] | i <- indices]
                          ]
                  Right (patch basic [("scripts", toJSON scripts), ("binder", binder)])
        _ -> Right Null
 where
  first (v : _) = v
  first [] = Null
  unlessNonempty values = if any null values then Left "Empty script base." else Right ()
  arrows :: Int -> Int -> [Value] -> [Int]
  arrows _ _ [] = []
  arrows depth index (t : rest)
    | label "text" t == "(" = arrows (depth + 1) (index + 1) rest
    | label "text" t == ")" = arrows (depth - 1) (index + 1) rest
    | depth == 0 && any (`simpleCommand` t) ["to", "longrightarrow"] = index : arrows depth (index + 1) rest
    | otherwise = arrows depth (index + 1) rest
  visit value =
    value : case value of
      Object fields -> concatMap descend (KM.elems fields)
      _ -> []
  descend value@(Object fields) | KM.member "kind" fields = visit value
  descend (Array values) = concatMap descend values
  descend _ = []

naturalLowerBound :: Value -> Either String Value
naturalLowerBound node
  | isKind "group" node = naturalLowerBound (field "body" node)
  | not (isKind "sequence" node) = Right Null
  | otherwise = do
      tokens <- normalTokens node
      pure $ case tokens of
        variable : relation : digits@(first : _)
          | identifier variable
          , simpleCommand "ge" relation
          , all (\t -> let value = label "text" t in not (T.null value) && T.all isDigit value) digits
          , and (zipWith (\a b -> start b == start a + T.length (label "text" a)) digits (drop 1 digits)) ->
              object
                [ "symbol" .= label "text" variable
                , "declarationOffset" .= start variable
                , "lowerBound" .= T.concat (map (label "text") digits)
                , "components"
                    .= [ component (start variable) (number (start variable + 1)) "lambda.binder"
                       , component (start relation) (field "end" relation) "lambda.domain.predicate"
                       , component (start first) (number (start (last digits) + T.length (label "text" (last digits)))) "lambda.domain.lower-bound"
                       ]
                ]
        _ -> Null
 where
  component :: Int -> Value -> Text -> Value
  component a b target = object ["start" .= a, "end" .= b, "target" .= target]

summationChunks :: Value -> Either String Value
summationChunks node
  | not (isKind "sequence" node) = Right (toJSON ([] :: [Value]))
  | otherwise = do
      tokens <- normalTokens node
      toJSON <$> scan tokens 0 tokens
 where
  scan _ _ [] = Right []
  scan tokens position (script : rest)
    | isKind "script" script
    , label "marker" script == "_"
    , label "name" (field "base" script) == "sum" = do
        let argument = field "argument" script
            lower = if isKind "group" argument then field "body" argument else argument
            children = if isKind "sequence" lower then items "items" lower else [lower]
        lowerTokens <- concatMap (filter (not . blank)) <$> traverse expressionTokens children
        case lowerTokens of
          [binder, relation, bound]
            | identifier binder
            , Just mode <- sumMode relation bound ->
                let (body, remaining, depth) = collect 0 [] rest
                    ending = position + 1 + length body
                 in if null body || depth /= 0
                      then scan tokens (position + 1) rest
                      else do
                        subsequent <- scan tokens ending remaining
                        pure
                          ( object
                              [ "script" .= script
                              , "binder" .= binder
                              , "relation" .= relation
                              , "bound" .= bound
                              , "body" .= sequenceNode body
                              , "mode" .= mode
                              , "first" .= position
                              , "last" .= ending
                              , "tokens" .= tokens
                              ]
                              : subsequent
                          )
          _ -> scan tokens (position + 1) rest
    | otherwise = scan tokens (position + 1) rest
  sumMode :: Value -> Value -> Maybe Text
  sumMode relation bound
    | label "name" relation == "in" && label "name" bound == "omega" = Just "infinite"
    | (label "text" relation == "<" || label "name" relation == "ge") && isKind "text" bound
    , let value = label "text" bound
    , not (T.null value) && (T.all isAlpha value || isDecimal value) =
        Just (if label "text" relation == "<" then "finite" else "tail")
    | otherwise = Nothing
  collect :: Int -> [Value] -> [Value] -> ([Value], [Value], Int)
  collect depth previous [] = (reverse previous, [], depth)
  collect depth previous remaining@(token : rest)
    | depth == 0 && (label "text" token `elem` ["+", "-", "=", "<", ">", ",", ")", "."] || label "name" token `elem` ["le", "ge", "ne", "in", "to", "longrightarrow", "}"]) = (reverse previous, remaining, depth)
    | otherwise = collect (depth + if label "text" token == "(" then 1 else if label "text" token == ")" then -1 else 0) (token : previous) rest

-- A shape is only a candidate: no carrier or binder identity is inferred here.
predicateSets :: Value -> Either String Value
predicateSets node
  | not (isKind "sequence" node) = Right (toJSON ([] :: [Value]))
  | otherwise = do
      raw <- normalTokens node
      let tokens = map (\t -> patch t [("end", fromMaybe (number (start t + T.length (label "text" t))) (case field "end" t of Null -> Nothing; value -> Just value))]) raw
      pure (toJSON (scan tokens 0))
 where
  scan tokens i
    | i >= length tokens = []
    | label "name" (tokens !! i) /= "{" = scan tokens (i + 1)
    | otherwise = case closing tokens (i + 1) 1 of
        Nothing -> []
        Just end ->
          let sized = i > 0 && label "name" (tokens !! (i - 1)) == "left"
              rightSized = label "name" (tokens !! (end - 1)) == "right"
              stop = end - if rightSized then 1 else 0
              explicit = stop > i + 5 && simpleCommand "in" (tokens !! (i + 2)) && identifier (tokens !! (i + 3)) && label "text" (tokens !! (i + 4)) == ":"
              colon = i + if explicit then 4 else 2
           in if sized /= rightSized || stop <= i + 3 || not (identifier (tokens !! (i + 1))) || label "text" (tokens !! colon) /= ":"
                then scan tokens (i + 1)
                else
                  let body = take (stop - colon - 1) (drop (colon + 1) tokens)
                      shape =
                        object
                          [ "binder" .= (tokens !! (i + 1))
                          , "colon" .= (tokens !! colon)
                          , "body" .= sequenceNode body
                          , "opening" .= (tokens !! i)
                          , "closing" .= (tokens !! end)
                          , "tokens" .= tokens
                          , "first" .= (i - if sized then 1 else 0)
                          , "last" .= (end + 1)
                          ]
                      complete = if explicit then patch shape [("domain", tokens !! (i + 3)), ("domainRelation", tokens !! (i + 2))] else shape
                   in complete : scan tokens (end + 1)
  closing :: [Value] -> Int -> Int -> Maybe Int
  closing tokens i depth
    | i >= length tokens = Nothing
    | label "name" (tokens !! i) == "{" = closing tokens (i + 1) (depth + 1)
    | label "name" (tokens !! i) == "}" = if depth == 1 then Just i else closing tokens (i + 1) (depth - 1)
    | otherwise = closing tokens (i + 1) depth

indexedSingletons :: Value -> Either String Value
indexedSingletons node
  | not (isKind "sequence" node) = Right (toJSON ([] :: [Value]))
  | otherwise = do
      tokens <- normalTokens node
      candidates <- traverse (shape tokens) [0 .. length tokens - 4]
      pure (toJSON (concat candidates))
 where
  shape tokens position = case take 4 (drop position tokens) of
    [operator, opening, value, closing]
      | isKind "script" operator
      , label "marker" operator == "_"
      , simpleCommand "bigcup" (field "base" operator)
      , simpleCommand "{" opening
      , simpleCommand "}" closing -> do
          let unwrap v = if isKind "group" v then unwrap (field "body" v) else v
              domain = unwrap (field "argument" operator)
              children = if isKind "sequence" domain then items "items" domain else [domain]
          parts <- concatMap (filter (not . blank)) <$> traverse expressionTokens children
          pure $ case parts of
            [point, relation, carrier]
              | identifier point
              , simpleCommand "in" relation
              , Just indexType <- lookup (label "name" carrier) [("QQ", "ℚ" :: Text), ("R", "ℝ"), ("omega", "ℕ")]
              , simpleCommand (label "name" carrier) carrier
              , isKind "text" value
              , label "text" value == label "text" point ->
                  [ object
                      [ "marker" .= field "base" operator
                      , "binder" .= patch point [("end", number (start point + 1))]
                      , "domainRelation" .= relation
                      , "domain" .= carrier
                      , "indexType" .= indexType
                      , "subscript" .= object ["start" .= field "end" (field "base" operator), "end" .= field "start" (field "argument" operator)]
                      , "opening" .= opening
                      , "value" .= patch value [("end", number (start value + 1))]
                      , "closing" .= closing
                      , "whole" .= (position == 0 && position + 4 == length tokens)
                      , "end" .= field "end" closing
                      ]
                  ]
            _ -> []
    _ -> Right []

ballFamilies :: Value -> Either String Value
ballFamilies node
  | not (isKind "sequence" node) = Right (toJSON ([] :: [Value]))
  | otherwise = do
      raw <- normalTokens node
      let tokens = map withEnd raw
      toJSON . concat <$> traverse (shape tokens) (zip [0 ..] tokens)
 where
  withEnd t = patch t [("end", case field "end" t of Null -> number (start t + T.length (label "text" t)); value -> value)]
  symbol value
    | identifier value = Just (label "text" value)
    | any (`simpleCommand` value) ["phi", "epsilon", "varepsilon", "rho", "delta", "iota"] = Just ("\\" <> label "name" value)
    | otherwise = Nothing
  argument value
    | isKind "sequence" value = do
        tokens <- normalTokens value
        pure $ case tokens of [single] -> symbol single; _ -> Nothing
    | otherwise = Right (symbol value)
  closing :: [Value] -> Int -> Int -> Maybe Int
  closing tokens position depth
    | position >= length tokens = Nothing
    | label "name" (tokens !! position) == "{" = closing tokens (position + 1) (depth + 1)
    | label "name" (tokens !! position) == "}" = if depth == 1 then Just position else closing tokens (position + 1) (depth - 1)
    | otherwise = closing tokens (position + 1) depth
  clauses :: Int -> [[Value]] -> [Value] -> [Value] -> [Value] -> Maybe ([[Value]], [Value])
  clauses depth previous current separators [] = if depth == 0 then Just (previous <> [current], separators) else Nothing
  clauses depth previous current separators (token : rest) =
    let next = depth + if label "text" token `elem` ["(", "["] || label "name" token == "{" then 1 else if label "text" token `elem` [")", "]"] || label "name" token == "}" then -1 else 0
     in if label "text" token == "," && next == 0
          then clauses next (previous <> [current]) [] (separators <> [token]) rest
          else clauses next previous (current <> [token]) separators rest
  shape tokens (position, opening)
    | label "name" opening == "{"
    , value : colon : _ <- drop (position + 1) tokens
    , label "name" value == "MetricBall"
    , [_, center, radiusArg] <- items "args" value
    , field "optional" value == Null
    , label "text" colon == ":"
    , Just end <- closing tokens (position + 3) 1
    , Just ([point, radius, trace], separators) <- clauses 0 [] [] [] (take (end - position - 3) (drop (position + 3) tokens))
    , [pointVar, relation, domain] <- point
    , Just pointName <- symbol pointVar
    , Just _ <- symbol domain
    , simpleCommand "in" relation
    , [radiusVar, greater, zero] <- radius
    , Just radiusName <- symbol radiusVar
    , label "text" greater == ">"
    , label "text" zero == "0"
    , pointName /= radiusName
    , diameter : less : _ : _ <- trace
    , label "name" diameter == "MetricDiameter"
    , length (items "args" diameter) == 2
    , field "optional" diameter == Null
    , label "text" less == "<" = do
        centerName <- argument center
        radiusSymbol <- argument radiusArg
        pure $
          if centerName /= Just pointName || radiusSymbol /= Just radiusName
            then []
            else
              let base =
                    object
                      [ "kind" .= ("metric-ball-family" :: Text)
                      , "opening" .= opening
                      , "closing" .= (tokens !! end)
                      , "value" .= value
                      , "colon" .= colon
                      , "pointDomain" .= point
                      , "radiusCondition" .= radius
                      , "traceCondition" .= trace
                      , "separators" .= separators
                      ]
               in [if position > 0 && simpleCommand "bigcup" (tokens !! (position - 1)) then patch base [("union", tokens !! (position - 1))] else base]
    | otherwise = Right []

naturalFamilies :: Value -> Either String [Value]
naturalFamilies node
  | not (isKind "sequence" node) = Right []
  | otherwise = do
      tokens <- normalTokens node
      concat <$> traverse (shape tokens) [0 .. length tokens - 2]
 where
  unwrapOne value = if isKind "group" value then field "body" value else value
  unwrap value
    | isKind "group" value = unwrap (field "body" value)
    | isKind "sequence" value, [single] <- items "items" value = unwrap single
    | otherwise = value
  explicit family domain allowLower = do
    lower <- if allowLower then naturalLowerBound domain else Right Null
    if lower /= Null
      then Right lower
      else do
        found <- sequenceCandidate (object ["kind" .= ("command" :: Text), "name" .= ("Sequence" :: Text), "args" .= [family, domain], "optional" .= Null])
        pure (maybe Null sequenceValue found)
  component :: Int -> Value -> Text -> Value
  component offset end target = object ["start" .= offset, "end" .= end, "target" .= target]
  subscript operator = component (start (field "argument" operator) - 1) (field "start" (field "argument" operator))
  retarget from to binder = patch binder [("components", toJSON [patch c [("target", String (T.replace from to (label "target" c)))] | c <- items "components" binder])]
  addComponent binder value = patch binder [("components", toJSON (items "components" binder <> [value]))]
  result marker family binder index whole ending = object ["marker" .= marker, "family" .= family, "binder" .= binder, "index" .= index, "whole" .= whole, "end" .= ending]
  shape tokens position = do
    let operator = tokens !! position
        family = tokens !! (position + 1)
        scripted = isKind "script" operator && label "marker" operator == "_"
        marker = if scripted then field "base" operator else operator
        setFamily = label "name" marker `elem` ["bigcap", "bigcup"]
        allowed = label "name" marker `elem` ["prod", "ExternalDisjointUnion", "bigcap", "bigcup"] && null (items "args" marker) && field "optional" marker == Null
    if not allowed || setFamily && not scripted
      then Right []
      else
        if setFamily && (label "name" family == "{" || isKind "predicate-set" family)
          then do
            shapes <-
              if isKind "predicate-set" family && field "domain" family /= Null
                then Right [family]
                else do
                  candidates <- predicateSets node
                  pure $ case candidates of Array values -> [s | s <- toList values, start (field "opening" s) == start family, field "domain" s /= Null]; _ -> []
            found <- explicit family (unwrapOne (field "argument" operator)) False
            pure $ case shapes of
              selected : _
                | found /= Null
                , field "indexOffset" found == Number 0 ->
                    let ending = if isKind "predicate-set" family then position + 2 else integer (field "last" selected)
                        body = patch (sequenceNode (take (ending - position - 1) (drop (position + 1) tokens))) [("start", field "start" family), ("end", field "end" (field "closing" selected))]
                        binder = addComponent (patch found [("carrierOffset", field "start" (field "domain" selected))]) (subscript operator "lambda.domain")
                     in [result marker body binder (object ["start" .= field "declarationOffset" found]) (position == 0 && ending == length tokens) (field "end" body)]
              _ -> []
          else
            if setFamily && label "text" family == "("
              then case close tokens (position + 2) 1 of
                Nothing -> Right []
                Just ending -> do
                  let bodyTokens = take (ending - position - 3) (drop (position + 2) tokens)
                      body = sequenceNode bodyTokens
                      domain = unwrap (field "argument" operator)
                  found <- explicit body domain True
                  let symbol = if found == Null then field "text" domain else field "symbol" found
                      visited = descendants body
                      families = [v | v <- visited, isKind "script" v, label "marker" v == "_", field "text" (field "argument" v) == symbol]
                      blocked = any (\v -> isKind "command" v && label "name" v `elem` ["Sequence", "IndexedFamily", "ExternalDisjointUnion", "prod", "sum", "bigcap", "bigcup", "inf", "mapsto"]) visited
                  if null bodyTokens || blocked || null families then Right [] else finish tokens position operator marker scripted setFamily body families ending
              else finish tokens position operator marker scripted setFamily family [family] (position + 2)
  finish tokens position operator marker scripted setFamily family families ending = case families of
    representative : _
      | isKind "script" representative
      , label "marker" representative == "_"
      , let base = field "base" representative
      , let index = field "argument" representative
      , identifier base
      , identifier index
      , all (\f -> isKind "text" (field "base" f) && T.length (label "text" (field "base" f)) == 1) families -> do
          let initial = object ["symbol" .= label "text" index, "declarationOffset" .= start index, "components" .= [component (start index) (field "end" index) "forall.binder"]]
          binder <-
            if not scripted
              then Right initial
              else do
                let domain = unwrapOne (field "argument" operator)
                    simpleDomain = case items "items" domain of [single] | isKind "sequence" domain -> single; _ -> domain
                found <- explicit family domain setFamily
                let chosen =
                      if isKind "text" simpleDomain && field "text" simpleDomain == field "text" index
                        then patch initial [("declarationOffset", field "start" simpleDomain), ("components", toJSON [component (start simpleDomain) (field "end" simpleDomain) "lambda.binder"])]
                        else found
                pure $ if chosen == Null || field "symbol" chosen /= field "text" index then Null else addComponent (retarget "lambda." "forall." chosen) (subscript operator "forall.domain")
          let adjusted = if label "name" marker `elem` ["ExternalDisjointUnion", "bigcap", "bigcup"] then retarget "forall." "lambda." binder else binder
              withFamily = patch adjusted [("familyOffset", field "start" base)]
              complete = if setFamily then patch withFamily [("familyOffsets", toJSON [field "start" (field "base" f) | f <- families])] else withFamily
              final = tokens !! (ending - 1)
              end = case field "end" final of Null -> number (start final + T.length (label "text" final)); value -> value
          pure [result marker family complete index (position == 0 && ending == length tokens) end | binder /= Null]
    _ -> Right []
  close :: [Value] -> Int -> Int -> Maybe Int
  close tokens position depth
    | position >= length tokens = Nothing
    | otherwise =
        let tokenText = label "text" (tokens !! position)
            next = depth + if tokenText == "(" then 1 else if tokenText == ")" then -1 else 0
         in if next == 0 then Just (position + 1) else close tokens (position + 1) next
  descendants value = value : case value of Object fields -> concatMap descend (KM.elems fields); _ -> []
  descend value@(Object fields) | KM.member "kind" fields = descendants value
  descend (Array values) = concatMap descend values
  descend _ = []

-- Lexical occurrences and unapproved binding guards. No Lean names are guessed.
lexicalWalk :: Value -> Either String ([Value], [Value])
lexicalWalk root = walk root ([], [])
 where
  variableCommands = ["phi", "epsilon", "varepsilon", "rho", "delta", "iota"]
  bindingCommands = ["Sequence", "IndexedFamily", "ExternalDisjointUnion", "prod", "sum", "bigcap", "bigcup", "inf", "mapsto"]
  values (Array array) = toList array
  values _ = []
  updateLast changes xs = case reverse xs of
    final : rest -> reverse rest <> [patch final changes]
    [] -> []
  walk node state@(variables, effects)
    | isKind "text" node = Right (foldl (textToken node) variables (zip [start node ..] (T.unpack (label "text" node))), effects)
    | isKind "command" node =
        let name = label "name" node
         in if name `elem` ["text", "begin", "end", "operatorname", "mathop"]
              then Right state
              else do
                let occurrences = if name `elem` variableCommands then variables <> [object ["symbol" .= ("\\" <> name), "start" .= start node, "end" .= (start node + T.length name + 1)]] else variables
                declarations <-
                  if name `elem` bindingCommands
                    then do
                      binder <- sequenceCandidate node
                      let base = object ["command" .= name, "start" .= start node, "end" .= field "end" node]
                      pure (effects <> [patch base (case binder of Just found -> [("binder", sequenceValue found)]; Nothing -> [("reason", String "Local/dependent binder requires a reviewed binding rule.")])])
                    else Right effects
                let optional = field "optional" node
                foldM (flip walk) (occurrences, declarations) (items "args" node <> [optional | optional /= Null])
    | isKind "sequence" node = do
        infimum <- boundedInfimum node
        guarded <-
          if infimum /= Null
            then Right effects
            else do
              tokens <- concat <$> traverse expressionTokens (items "items" node)
              balls <- values <$> ballFamilies node
              pure (snd (foldl (guardToken balls) ([], effects) tokens))
        (vars, guards, _, _) <- foldM child (variables, guarded, Nothing, Nothing) (items "items" node)
        pure (vars, guards)
    | isKind "group" node = walk (field "body" node) state
    | isKind "script" node = do
        let before = length variables
            base = field "base" node
        (vars, guards) <- walk base state
        case decoratedName True node of
          Just (Object star) | length vars > before -> pure (updateLast [(K.toText key, value) | (key, value) <- KM.toList star] vars, guards)
          _ -> do
            let eligible = (isKind "text" base || isKind "command" base) && length vars > before
                marked
                  | eligible && label "marker" node == "_" = updateLast ([("subscriptBase", Bool True)] <> maybe [] (\named -> [("numericSubscriptName", named)]) (decoratedName False node)) vars
                  | eligible && label "marker" node == "^" = updateLast [("superscriptBase", Bool True)] vars
                  | otherwise = vars
            walk (field "argument" node) (marked, guards)
    | otherwise = Right state
  textToken node previous (offset, char)
    | isAlpha char = previous <> [object ["symbol" .= T.singleton char, "start" .= offset, "end" .= (offset + 1)]]
    | char == '\''
    , final : _ <- reverse previous
    , start final >= start node
    , field "end" final == number offset =
        updateLast [("symbol", String (label "symbol" final <> "'")), ("end", number (offset + 1))] previous
    | otherwise = previous
  guardToken balls (stack, effects) token
    | label "name" token == "{" = ((start token, False) : stack, effects)
    | label "text" token == ":", (opening, _) : rest <- stack = ((opening, True) : rest, effects)
    | label "name" token == "}"
    , (opening, builder) : rest <- stack =
        let base = object ["command" .= ("unreviewed-set-builder" :: Text), "start" .= opening, "end" .= field "end" token, "reason" .= ("Set comprehension requires a reviewed lexical binding rule." :: Text)]
            candidate = case [shape | shape <- balls, start (field "opening" shape) == opening] of
              shape : _ -> patch base [("candidateGenerator", shape), ("candidateGeneratorOffsetConvention", String "relative to formula bodyStart")]
              _ -> base
            complete = case [r | r <- items "generatorRestrictions" root, field "generatorOffset" r == number opening] of
              restriction : _ -> patch candidate [("sourceRestriction", restriction)]
              _ -> candidate
         in (rest, effects <> [complete | builder])
    | otherwise = (stack, effects)
  child (variables, effects, decoration, previous) node
    | isKind "command" node, label "name" node == "hat", null (items "args" node) = Right (variables, effects, Just node, Just node)
    | otherwise = do
        let primed = case previous of
              Just command
                | isKind "text" node
                , "'" `T.isPrefixOf` label "text" node
                , isKind "command" command
                , label "name" command `elem` variableCommands
                , null (items "args" command)
                , field "optional" command == Null
                , final : _ <- reverse variables
                , field "end" final == number (start node) ->
                    let primes = T.takeWhile (== '\'') (label "text" node)
                     in updateLast [("symbol", String (label "symbol" final <> primes)), ("end", number (start node + T.length primes))] variables
              _ -> variables
            before = length primed
        (vars, guards) <- walk node (primed, effects)
        pure $ case decoration of
          Just hat
            | length vars > before ->
                let decorated = [if index == before then patch v [("symbol", String ("\\hat " <> label "symbol" v)), ("start", field "start" hat)] else v | (index, v) <- zip [0 ..] vars]
                 in (decorated, guards, Nothing, Just node)
          _ -> (vars, guards, decoration, Just node)

-- Binding registration follows lexical extraction, without resolving Lean names.
extractBindings :: Value -> Either String ([Value], [Value])
extractBindings root = do
  conjunction <- conjunctionShape root
  if conjunction /= Null
    then do
      parts <- traverse extractBindings (items "clauses" conjunction)
      pure (concatMap fst parts, concatMap snd parts)
    else do
      (variables, initial) <- lexicalWalk root
      families <- register familyPass root initial
      sets <- register setPass root families
      sums <- register sumPass root sets
      infima <- register infPass root sums
      singletons <- register singletonPass root infima
      balls <- ballFamilies root >>= \v -> foldM ballPass singletons (values v)
      signature <- typedMapShape root
      let typed =
            if signature == Null
              then balls
              else
                let point = field "point" signature
                    equation = items "equation" signature
                 in balls
                      <> [ object
                             [ "command" .= ("typed-map" :: Text)
                             , "start" .= field "start" (first equation)
                             , "end" .= field "end" root
                             , "binder" .= object ["symbol" .= field "text" point, "declarationOffset" .= start point, "domainOffset" .= field "start" (field "domain" signature), "components" .= [component point (number (start point + 1)) "forall.binder"]]
                             ]
                         ]
      mapping <- mapstoShape root
      let mapped =
            if mapping == Null
              then typed
              else
                let base = object ["command" .= ("mapsto" :: Text), "start" .= start root, "end" .= field "end" root]
                 in if field "point" mapping == Null
                      then typed <> [patch base [("reason", String "Mapsto requires one scalar binder with a reviewed domain.")]]
                      else
                        let point = field "point" mapping
                         in filter (\e -> not (label "command" e == "mapsto" && start e == start (field "arrow" mapping))) typed
                              <> [patch base [("binder", object ["symbol" .= field "text" point, "declarationOffset" .= start point, "components" .= [component point (number (start point + 1)) "lambda.binder"]])]]
      convergence <- convergenceShape root
      let result =
            if convergence == Null
              then mapped
              else
                let base = object ["command" .= ("sequence-limit" :: Text), "start" .= start root, "end" .= field "start" (field "arrow" convergence)]
                 in mapped <> [patch base [if field "binder" convergence == Null then ("reason", String "Convergence needs a single reviewed sequence index.") else ("binder", field "binder" convergence)]]
      pure (variables, result)
 where
  first (v : _) = v
  first [] = Null
  values (Array array) = toList array
  values _ = []
  children (Object fields) = concatMap descend (KM.elems fields)
  children _ = []
  descend value@(Object fields) | KM.member "kind" fields = [value]
  descend (Array array) = concatMap descend array
  descend _ = []
  register pass node effects = do
    current <- pass node effects
    foldM (flip (register pass)) current (children node)
  removeReason (Object fields) = Object (KM.delete "reason" fields)
  removeReason value = value
  update predicate changes effects = case break predicate effects of
    (before, old : after) -> Right (before <> [removeReason (patch old changes)] <> after)
    _ -> Left "Missing original lexical binding effect"
  component :: Value -> Value -> Text -> Value
  component token end target = object ["start" .= start token, "end" .= end, "target" .= target]
  guardAt opening closing effect = label "command" effect == "unreviewed-set-builder" && start effect == start opening && field "end" effect == field "end" closing
  familyPass node effects = do
    shapes <- naturalFamilies node
    foldM
      ( \state shape ->
          let marker = field "marker" shape
              command = if label "name" marker `elem` ["bigcap", "bigcup"] then "natural-set-family" else "natural-type-family"
           in update
                (\e -> field "command" e == field "name" marker && start e == start marker)
                [("command", String command), ("end", field "end" (field "family" shape)), ("binder", field "binder" shape), ("setCarrierAllowed", Bool (label "name" marker == "prod"))]
                state
      )
      effects
      shapes
  setPass node effects = do
    shapes <- values <$> predicateSets node
    foldM
      ( \state shape -> do
          let opening = field "opening" shape
              closing = field "closing" shape
              point = field "binder" shape
              cleared = filter (not . guardAt opening closing) state
              base = object ["symbol" .= field "text" point, "declarationOffset" .= start point, "components" .= [component point (field "end" point) "set.lambda.binder"]]
              binder = if field "domain" shape == Null then base else patch base [("domainOffset", field "start" (field "domain" shape))]
              registered =
                if any (\e -> label "command" e == "predicate-set" && start e == start opening) cleared
                  then cleared
                  else
                    cleared <> [object ["command" .= ("predicate-set" :: Text), "start" .= start opening, "end" .= field "end" closing, "binder" .= binder]]
          register setPass (field "body" shape) registered
      )
      effects
      shapes
  sumPass node effects = do
    shapes <- values <$> summationChunks node
    foldM
      ( \state shape -> do
          let marker = field "base" (field "script" shape)
              point = field "binder" shape
              body = field "body" shape
              binder = object ["symbol" .= field "text" point, "leanType" .= ("ℕ" :: Text), "declarationOffset" .= start point, "bodyStart" .= start body, "components" .= [component point (number (start point + 1)) "sum.lambda.binder"]]
          changed <- update (\e -> label "command" e `elem` ["sum", "natural-sum"] && start e == start marker) [("command", String "natural-sum"), ("end", field "end" body), ("binder", binder)] state
          register sumPass body changed
      )
      effects
      shapes
  infPass node effects
    | not (isKind "sequence" node) = Right effects
    | otherwise = do
        tokens <- concat <$> traverse expressionTokens (items "items" node)
        foldM
          ( \state (position, token) ->
              if label "name" token /= "inf"
                then Right state
                else do
                  shape <- boundedInfimum (object ["kind" .= ("sequence" :: Text), "items" .= drop position tokens])
                  if shape == Null
                    then Right state
                    else do
                      let source = items "tokens" shape
                          point = field "binder" shape
                          cleared = filter (not . guardAt (first (drop 1 source)) (last source)) state
                          binder = object ["symbol" .= field "text" point, "declarationOffset" .= start point, "domainOffset" .= field "start" (field "domain" shape), "components" .= [component point (number (start point + 1)) "image.lambda.binder"]]
                      update (\e -> label "command" e == "inf" && start e == start token) [("command", String "bounded-infimum"), ("end", field "start" (field "relation" shape)), ("binder", binder)] cleared
          )
          effects
          (zip [0 ..] tokens)
  singletonPass node effects = do
    shapes <- values <$> indexedSingletons node
    pure (foldl (\state shape -> map (apply shape) state) effects shapes)
   where
    apply shape effect
      | label "command" effect == "bigcup"
      , start effect == start (field "marker" shape) =
          let proposed = patch effect [("candidateSingletonFamily", shape), ("candidateSingletonOffsetConvention", String "relative to formula bodyStart"), ("reason", String "Indexed singleton union needs a reviewed ambient carrier and element coercion.")]
           in if label "type" (field "rationalAmbient" root) /= "Real" || label "indexType" shape /= "ℚ"
                then proposed
                else
                  removeReason
                    ( patch
                        proposed
                        [ ("command", String "rational-singleton-family")
                        , ("end", field "end" shape)
                        ,
                          ( "binder"
                          , object
                              [ "symbol" .= field "text" (field "binder" shape)
                              , "leanType" .= ("ℚ" :: Text)
                              , "declarationOffset" .= field "start" (field "binder" shape)
                              , "components" .= [patch (field key shape) [("target", String "lambda.domain")] | key <- ["binder", "domainRelation", "domain", "subscript"]]
                              ]
                          )
                        ]
                    )
      | otherwise = effect
  ballPass effects shape = case [r | r <- items "generatorRestrictions" root, field "generatorOffset" r == field "start" (field "opening" shape)] of
    restriction : _
      | field "union" shape /= Null ->
          let opening = field "opening" shape
              closing = field "closing" shape
              point = first (items "pointDomain" shape)
              radius = first (items "radiusCondition" shape)
              cleared = filter (\e -> not (guardAt opening closing e || label "command" e == "bigcup" && start e == start (field "union" shape))) effects
              effect role token =
                object
                  [ "command" .= ("ball-generator-" <> role)
                  , "start" .= start opening
                  , "end" .= field "end" closing
                  , "sourceRestriction" .= restriction
                  , "binder"
                      .= object
                        [ "symbol" .= (if field "text" token == Null then "\\" <> label "name" token else label "text" token)
                        , "declarationOffset" .= start token
                        , "domainOffset" .= field "start" (last (items "pointDomain" shape))
                        , "nameDiscriminator" .= start token
                        , "components" .= [component token (field "end" token) ("generator.exists." <> role)]
                        ]
                  ]
           in Right (cleared <> [effect "point" point, effect "radius" radius])
    _ -> Right effects

-- Integer exponents retain the original source tree and each lexical token.
-- This normalization does not elaborate arithmetic or approve an interpretation.
integerExpression :: Value -> Either String Value
integerExpression node = do
  body <- convert node
  pure (patch node [("kind", String "integer-expression"), ("body", body)])
 where
  convert part = case label "kind" part of
    "group" -> do body <- convert (field "body" part); pure (patch part [("body", body)])
    "sequence" -> do children <- traverse convert (items "items" part); pure (patch part [("items", toJSON children)])
    "text" -> do
      tokens <- tokenize (start part) (label "text" part)
      pure (patch part [("kind", String "sequence"), ("items", toJSON tokens)])
    _ -> Left "Integer exponent requires scalar integer arithmetic."
  tokenize offset value = case T.uncons value of
    Nothing -> Right []
    Just (char, rest) -> do
      let (chunk, remaining) = if generalCategory char == DecimalNumber then T.span ((== DecimalNumber) . generalCategory) value else (T.singleton char, rest)
          kind
            | isDecimal chunk = "integer-literal"
            | T.all isAlpha chunk = "integer-variable"
            | otherwise = "text"
      if kind == "text" && not (char `elem` ['+', '-', '*', '(', ')'] || whitespace char)
        then Left "Unsupported integer-exponent arithmetic."
        else do
          subsequent <- tokenize (offset + T.length chunk) remaining
          pure (object ["kind" .= (kind :: Text), "text" .= chunk, "start" .= offset, "end" .= (offset + T.length chunk)] : subsequent)
  whitespace char = isSpace char || char `elem` ['\x1c', '\x1d', '\x1e', '\x1f', '\x85']

casesNode :: Value -> Either String Value
casesNode payload = do
  let node = field "tree" payload
      occupied = [name | String name <- items "occupied" payload]
  tokens <- concat <$> traverse expressionTokens (items "items" node)
  let delimiter name token =
        label "name" token == name && case items "args" token of
          [argument] -> case filter (not . blank) (if isKind "sequence" argument then items "items" argument else [argument]) of
            [value] -> T.strip (label "text" value) == "cases"
            _ -> False
          _ -> False
      begins = [i | (i, token) <- zip [0 ..] tokens, delimiter "begin" token]
      ends = [i | (i, token) <- zip [0 ..] tokens, delimiter "end" token]
  case begins of
    [] -> Right Null
    [begin]
      | [stop] <- ends
      , stop > begin -> do
          let rows = splitRows (take (stop - begin - 1) (drop (begin + 1) tokens))
          if length rows /= 2
            then Left "Cases require two complementary conditions."
            else do
              branches <- traverse (branch occupied (start (tokens !! begin))) (zip [0 :: Int ..] rows)
              let grouped = patch node [("kind", String "real-cases"), ("branches", toJSON branches), ("start", field "start" (tokens !! begin)), ("end", field "end" (tokens !! stop)), ("opening", tokens !! begin)]
              pure (patch node [("items", toJSON (take begin tokens <> [grouped] <> drop (stop + 1) tokens))])
    _ -> Left "Cases require one unnested environment."
 where
  splitRows [] = [[]]
  splitRows (token : rest)
    | label "name" token == "\\" = [] : splitRows rest
    | otherwise = case splitRows rest of row : rows -> (token : row) : rows; [] -> [[token]]
  clean tokens =
    let stripped = reverse (dropWhile (\t -> blank t || label "text" t `elem` [",", "."]) (reverse tokens))
        trimmed = reverse (dropWhile blank (reverse (dropWhile blank stripped)))
     in if null trimmed then Left "Empty expression operand." else Right (sequenceNode trimmed)
  branch occupied begin (index, row) = case [i | (i, token) <- zip [0 ..] row, label "text" token == "&"] of
    [position] -> do
      body <- clean (take position row)
      condition <- clean (drop (position + 1) row)
      let fresh candidateName = if candidateName `elem` occupied then fresh (candidateName <> "_") else candidateName
          name = fresh ("book_case_" <> T.pack (show begin) <> "_" <> T.pack (show index))
      pure (object ["body" .= body, "condition" .= condition, "separator" .= (row !! position), "kind" .= ("case-branch" :: Text), "proofName" .= name, "equality" .= (index == 0), "start" .= field "start" body, "end" .= field "end" condition])
    _ -> Left "Each cases row needs one value and condition."

syntaxChildren :: Value -> [Value]
syntaxChildren (Object fields) = concatMap descend (KM.elems fields)
 where
  descend value@(Object child) = [value | KM.member "kind" child]
  descend (Array values) = [value | value@(Object child) <- toList values, KM.member "kind" child]
  descend _ = []
syntaxChildren _ = []

-- Visible operators remain candidates even when no interpretation rule succeeds.
operatorCandidates :: Value -> Either String [Value]
operatorCandidates node
  | field "numericDomain" node /= Null = Right [object ["start" .= field "numericStart" node, "end" .= field "numericEnd" node]]
  | isKind "command" node && name `elem` ["text", "begin", "end", "operatorname", "mathop"] =
      Right [spanValue (start node) (integer (field "end" node)) | conjunctionToken node || name == "begin" && case items "args" node of [argument] -> isKind "sequence" argument && map (label "text") (items "items" argument) == ["cases"]; _ -> False]
  | isKind "script" node
  , Just _ <- decoratedName True node = do
      nested <- operatorCandidates (field "base" node)
      pure (spanValue (integer (field "end" (field "base" node))) (integer (field "end" node)) : nested)
  | otherwise = do
      own <- case label "kind" node of
        "text" -> pure (textOperators (T.unpack (label "text" node)))
        "command" -> pure [spanValue (start node) (start node + T.length name + 1) | name `elem` operators]
        "script" -> let begin = start (field "argument" node) in pure [spanValue (begin - 1) begin]
        "sequence" -> do
          tokens <- normalTokens node
          pure [object ["start" .= field "end" power, "end" .= field "end" power, "notation" .= ("juxtaposition" :: Text)] | (power, following, opening) <- zip3 tokens (drop 1 tokens) (drop 2 tokens), numericPower power, label "text" opening == "(", isKind "script" following || isKind "text" following && not (T.null (label "text" following)) && T.all isAlpha (label "text" following)]
        _ -> pure []
      nested <- concat <$> traverse operatorCandidates (syntaxChildren node)
      pure (own <> nested)
 where
  name = label "name" node
  operators = map fst macroNames <> ["Sequence", "IndexedFamily", "ExternalDisjointUnion", "prod", "sum", "bigcap", "bigcup", "inf", "mapsto", "Pair", "seqPower", "to", "longrightarrow", "le", "ge", "ne", "in", "IncludedIn", "hookrightarrow", "emptyset", "MetricDiameter", "TwoPointSpace", "Homeomorphic", "NonnegativeDimensionLevel", "MetricBall", "cdots", "supseteq", "cap", "cup", "times", "restrict", "circ", "{"]
  numericPower value = isKind "script" value && label "marker" value == "^" && isKind "text" (field "base" value) && isDecimal (label "text" (field "base" value)) && decimal (label "text" (field "base" value)) > 0
  spanValue begin end = object ["start" .= begin, "end" .= end]
  textOperators characters = [spanValue (start node + offset) (start node + offset + width) | (offset, char) <- zip [0 ..] characters, let previous = if offset == 0 then Nothing else Just (characters !! (offset - 1)); following = drop (offset + 1) characters; width = if char == ':' then 2 else 1, char == ':' && take 1 following == "=" || char `elem` ("+-*/=<>" :: String) && not (char == '=' && previous == Just ':')]

inspectionPlan :: Value -> Either String Value
inspectionPlan root = do
  fragments <- expressionList root
  operators <- operatorCandidates root
  let parts = case fragments of Array values -> toList values; _ -> []
      entry isRoot tree = object ["root" .= isRoot, "tree" .= tree]
      descend node = [entry False node | isKind "command" node && label "name" node `elem` (map fst macroNames <> ["MetricDiameter", "MetricBall"])] <> concatMap descend (syntaxChildren node)
  pure (object ["fragments" .= fragments, "operators" .= operators, "nodes" .= ((if null parts then [entry True root] else map (entry False) parts) <> descend root)])

structuralRequest :: Value -> Parser Value
structuralRequest = withObject "structural candidate request" $ \fields -> do
  operation <- fields .: "operation"
  node <- fields .: "node"
  result <- either fail pure (recognize operation node)
  pure (object ["result" .= result])
 where
  recognize :: Text -> Value -> Either String Value
  recognize "operatorCandidates" node = toJSON <$> operatorCandidates node
  recognize "inspectionPlan" node = inspectionPlan node
  recognize "integerExpression" node = integerExpression node
  recognize "casesNode" node = casesNode node
  recognize "extractBindings" node = do
    (variables, effects) <- extractBindings node
    pure (object ["variables" .= variables, "effects" .= effects])
  recognize "lexicalWalk" node = do
    (variables, effects) <- lexicalWalk node
    pure (object ["variables" .= variables, "effects" .= effects])
  recognize "naturalFamilies" node = toJSON <$> naturalFamilies node
  recognize "naturalFamily" node = do
    found <- naturalFamilies node
    pure (fromMaybe Null (listToMaybe [s | s <- found, field "whole" s == Bool True, label "name" (field "marker" s) `elem` ["prod", "ExternalDisjointUnion"]]))
  recognize "ballFamilies" node = ballFamilies node
  recognize "predicateSets" node = predicateSets node
  recognize "indexedSingletons" node = indexedSingletons node
  recognize "naturalLowerBound" node = naturalLowerBound node
  recognize "summationChunks" node = summationChunks node
  recognize "alignedRows" node = alignedRows node
  recognize "expressionList" node = expressionList node
  recognize "convergenceShape" node = convergenceShape node
  recognize "typedMapShape" node = typedMapShape node
  recognize "isConjunctionToken" node = Right (Bool (conjunctionToken node))
  recognize "conjunctionShape" node = conjunctionShape node
  recognize "mapstoShape" node = mapstoShape node
  recognize "boundedInfimum" node = boundedInfimum node
  recognize "expressionTokens" node = toJSON <$> expressionTokens node
  recognize "sequenceBinder" node = maybe Null sequenceValue <$> sequenceCandidate node
  recognize "starredName" node = Right (fromMaybe Null (decoratedName True node))
  recognize "numericSubscriptName" node = Right (fromMaybe Null (decoratedName False node))
  recognize "numericPower" node = Right (Bool (isKind "script" node && label "marker" node == "^" && isKind "text" (field "base" node) && isDecimal (label "text" (field "base" node)) && decimal (label "text" (field "base" node)) > 0))
  recognize _ _ = Left "Unknown structural candidate operation"

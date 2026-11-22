{-# LANGUAGE OverloadedStrings #-}

{- | Located syntax -> semantic AST -> both renderings.
Unsupported syntax and annotations remain explicit failures. The caller never
selects another interpreter after a native error or unsupported result.
-}
module SemanticTranslation (translationRequest) where

import ChapterMappingRules
import Control.Applicative ((<|>))
import Control.Monad (unless, when, (>=>))
import Data.Aeson (Object, Value (..), object, parseJSON, toJSON, withObject, (.!=), (.:), (.:?), (.=))
import qualified Data.Aeson.Key as K
import qualified Data.Aeson.KeyMap as KM
import Data.Aeson.Types (Parser, parseEither)
import Data.Char (isAlpha, isAlphaNum, isDigit, isSpace)
import Data.Either (fromRight)
import Data.List (sortOn)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, isJust, isNothing, listToMaybe)
import Data.Text (Text)
import qualified Data.Text as T
import LocatedMath
import ProofContexts (contextBridgeRequest)
import SemanticExpr
import SemanticInspection (semanticValue)
import StructuralSyntax (SequenceCandidate (..), ballFamilies, boundedInfimum, casesNode, conjunctionShape, convergenceShape, decimal, indexedSingletons, isDecimal, naturalFamilies, normalTokens, predicateSets, sequenceCandidate, summationChunks)
import Text.Read (readMaybe)

data MeaningEnv = MeaningEnv
  { envConstants :: Map.Map Text Text
  , envBindings :: Map.Map Int BindingIdentity
  , envConventions :: Map.Map Text Text
  , envConstructed :: Map.Map Int (SourceSpan, Expr)
  , envRootSpan :: Maybe SourceSpan
  , envCurrentSpan :: Maybe SourceSpan
  , envOccupied :: [Text]
  , envBranchProof :: Maybe Text
  , envRecords :: Map.Map Text [SourceBinder]
  , envNumericDomain :: Maybe NumericDomain
  }

data SourceBinder = SourceBinder Text Text

sourceBinders :: Value -> Parser [SourceBinder]
sourceBinders = withObject "original context record" $ \fields -> do
  binders <- fields .:? "binders" .!= []
  mapM (withObject "original context binder" (\b -> SourceBinder <$> b .: "name" <*> b .:? "type" .!= "")) binders

numericDomain :: Value -> Parser NumericDomain
numericDomain = withObject "source numeral domain" $ \fields -> do
  onlyFields ["type", "target", "binding"] fields
  ty <- fields .: "type"
  target <- fields .: "target"
  identity <- fields .:? "binding"
  let (prefix, name) = T.breakOnEnd "/" target
      context = T.dropEnd 1 prefix
  unless (not (T.null (T.strip ty)) && not (T.null context) && not (T.null name)) (fail "Numeric domain requires its original context and witness")
  pure (NumericDomain ty target identity context (if name == "@constant" then Nothing else Just name))

onlyFields :: [Text] -> Object -> Parser ()
onlyFields allowed fields = unless (all ((`elem` allowed) . K.toText) (KM.keys fields)) (fail "Unknown semantic annotation field")

validateNumericDomain :: MeaningEnv -> NumericDomain -> Either String ()
validateNumericDomain env domain = case Map.lookup (numericContext domain) (envRecords env) of
  Nothing -> Left "Missing numeric-domain witness in the original Lean context"
  Just binders -> unless (maybe True (\name -> any (\(SourceBinder candidateName _) -> name == candidateName) binders) (numericWitness domain)) (Left "Missing numeric-domain witness in the original Lean context")

-- Normalization metadata remains typed source evidence. Known annotations are
-- consumed explicitly; the lossless syntax decoder still rejects unknown keys.
annotatedMeaning :: MeaningEnv -> Bool -> Value -> Either String Expr
annotatedMeaning env root value = do
  fields <- parseEither (withObject "annotated source expression" pure) value
  kind <- parseEither (.: "kind") fields :: Either String Text
  if kind == "interpreted-literal"
    then contextualMeaning env fields
    else do
      scope <- parseEither (\f -> f .:? "numericContext" >>= traverse numericDomain) fields
      expression <- parseEither (\f -> f .:? "numericExpression" .!= False) fields
      literal <- parseEither (\f -> f .:? "numericDomain" >>= traverse numericDomain) fields
      prefix <- parseEither (.:? "prefixPredicate") fields
      rational <- parseEither (.:? "rationalAmbient") fields
      restrictions <- parseEither (\f -> f .:? "generatorRestrictions" .!= [] >>= mapM restrictionEvidence) fields
      let remaining = foldr (KM.delete . K.fromText) fields ["numericContext", "numericExpression", "numericDomain", "numeral", "numericStart", "numericEnd", "prefixPredicate", "rationalAmbient", "generatorRestrictions"]
          scoped = env{envNumericDomain = scope <|> envNumericDomain env}
      when (isNothing literal && any (`KM.member` fields) ["numeral", "numericStart", "numericEnd"]) (Left "Numeric literal annotation has no source domain")
      when (expression && (isJust literal || isJust prefix)) (Left "Conflicting source expression annotations")
      when (isJust rational && (expression || isJust literal || isJust prefix)) (Left "Conflicting rational-ambient annotation")
      when (not (null restrictions) && (expression || isJust literal || isJust prefix || isJust rational)) (Left "Conflicting generator restriction annotation")
      case (literal, prefix, kind) of
        (Just domain, Nothing, "source-numeral") -> do
          only <- parseEither (\f -> onlyFields ["kind", "start", "end"] f >> SourceSpan <$> f .: "start" <*> f .: "end") remaining
          literalMeaning scoped only Nothing domain fields
        _ -> do
          syntax@(LocatedMath location _) <- parseEither (if isJust literal then locatedSyntaxWith True else locatedSyntax) (Object remaining)
          let selected = scoped{envRootSpan = if root then Just location else Nothing}
          case (literal, prefix) of
            (Just domain, Nothing) -> literalMeaning selected location (Just syntax) domain fields
            (Nothing, Just predicate) -> prefixMeaning selected syntax predicate
            (Nothing, Nothing)
              | not (null restrictions) -> generatedMeaning selected root syntax restrictions
              | Just ambient <- rational -> rationalMeaning selected syntax ambient
              | expression -> case envNumericDomain selected of
                  Nothing -> Left "Numeric expression needs an explicit source domain"
                  Just domain -> numericOperandMeaning selected domain (sourceTokens syntax)
              | otherwise -> (if root then rootMeaning else meaning) selected syntax
            _ -> Left "Conflicting source literal and predicate annotations"

rationalMeaning :: MeaningEnv -> LocatedMath -> Value -> Either String Expr
rationalMeaning env syntax@(LocatedMath location _) ambient = do
  evidence <-
    parseEither
      ( withObject
          "source rational ambient"
          ( \f -> do
              onlyFields ["type", "scope", "start", "end"] f
              ty <- f .: "type"
              scope <- f .: "scope"
              source <- SourceSpan <$> f .: "start" <*> f .: "end"
              unless (ty == "Real" && not (T.null scope) && spanStart source >= 0 && spanEnd source >= spanStart source) (fail "Invalid source rational ambient")
              pure (AmbientEvidence ty scope source)
          )
      )
      ambient
  shapes <- indexedSingletons (locatedValue syntax) >>= parseEither parseJSON
  tokens <- normalTokens (locatedValue syntax) >>= traverse (parseEither (locatedSyntaxWith True))
  case (shapes, tokens) of
    ([shape], [rationals@(LocatedMath rationalsSpan _), equals@(LocatedMath operator _), _, _, _, _])
      | commandIs True "QQ" rationals
      , symbol equals == "=" -> do
          (marker, binder, relation, domain, subscript, opening, value, closing) <- parseEither parseShape shape
          identity <- maybe (Left "Rational singleton union needs its lexical index") Right (Map.lookup (spanStart binder) (envBindings env))
          unless (bindingLocalBinder identity && bindingType identity == "ℚ") (Left "Rational singleton union needs a lexical rational index")
          point <- meaning env value
          let LocatedMath valueSpan _ = value
              singleton = SingletonSet opening opening closing (Just (coercionTargetDisplay rationalReal)) (Coerce valueSpan rationalReal point)
              family = TypedLambda binder rationalSingletonFamily identity [relation, domain] subscript singleton
              union = Aggregate marker rationalUnion evidence family
              image = TypedRange rationalsSpan rationalReal (CoercionFunction rationalsSpan rationalReal)
          pure (SetIdentity location operator image union)
    _ -> Left "Rational ambient requires the complete identity-singleton union equality"
 where
  parseShape = withObject "rational singleton candidate" $ \f -> do
    ty <- f .: "indexType" :: Parser Text
    unless (ty == "ℚ") (fail "Rational singleton candidate needs Rat indices")
    (,,,,,,,) <$> (f .: "marker" >>= sourceSpan) <*> (f .: "binder" >>= sourceSpan) <*> (f .: "domainRelation" >>= locatedSyntaxWith True) <*> (f .: "domain" >>= locatedSyntaxWith True) <*> (f .: "subscript" >>= sourceSpan) <*> (f .: "opening" >>= sourceSpan) <*> (f .: "value" >>= locatedSyntaxWith True) <*> (f .: "closing" >>= sourceSpan)

restrictionEvidence :: Value -> Parser RestrictionEvidence
restrictionEvidence = withObject "bounded-trace source premise" $ \f -> do
  onlyFields ["kind", "generatorOffset", "premise", "source", "metric", "subset", "trace"] f
  kind <- f .: "kind" :: Parser Text
  unless (kind == "bounded-trace") (fail "Unknown generator restriction")
  offset <- f .: "generatorOffset"
  premise <- f .: "premise"
  (source, text) <-
    f .: "source"
      >>= withObject
        "premise source"
        ( \s -> do
            onlyFields ["start", "end", "text"] s
            span' <- SourceSpan <$> s .: "start" <*> s .: "end"
            content <- s .: "text"
            unless (spanStart span' >= 0 && spanEnd span' - spanStart span' == T.length content) (fail "Premise text does not match its source span")
            pure (span', content)
        )
  unless (offset >= 0 && not (T.null premise)) (fail "Generator restriction needs its source premise")
  metric <- f .: "metric" >>= reference
  subset <- f .: "subset" >>= reference
  trace <- f .: "trace" >>= locatedSyntaxWith True
  pure (RestrictionEvidence kind offset premise source text [("metric", metric), ("subset", subset)] [("trace", trace)])
 where
  reference = withObject "source binding reference" $ \f -> do
    onlyFields ["id", "target"] f
    (,) <$> f .: "id" <*> f .: "target"

data GeneratedShape = GeneratedShape SourceSpan SourceSpan SourceSpan SourceSpan [LocatedMath] [LocatedMath] [LocatedMath] [SourceSpan] LocatedMath

generatedMeaning :: MeaningEnv -> Bool -> LocatedMath -> [RestrictionEvidence] -> Either String Expr
generatedMeaning env root syntax@(LocatedMath location node) restrictions = do
  unless (length restrictions == Map.size (Map.fromList [(restrictionOffset r, ()) | r <- restrictions])) (Left "Duplicate generator restrictions")
  shapes <- ballFamilies (locatedValue syntax) >>= parseEither parseJSON >>= traverse (parseEither parseShape)
  let select evidence = case [shape | shape@(GeneratedShape _ opening _ _ _ _ _ _ _) <- shapes, spanStart opening == restrictionOffset evidence] of
        [shape] -> Right (shape, evidence)
        _ -> Left "Restriction needs exactly one matching generated family"
  selected <- traverse select restrictions
  expressions <- traverse interpret selected
  let replacements = sortOn (spanStart . fst) [(SourceSpan (spanStart union) (spanEnd closing), expression) | ((GeneratedShape union _ closing _ _ _ _ _ _, _), expression) <- zip selected expressions]
      definitions = Map.fromList [(spanStart source, (source, expression)) | (source, expression) <- replacements]
      collapse [] tokens = tokens
      collapse _ [] = []
      collapse replacements'@((source, _) : rest) tokens@(token@(LocatedMath current _) : remaining)
        | spanStart current < spanStart source = token : collapse replacements' remaining
        | spanStart current == spanStart source = LocatedMath source (LocatedRaw "") : collapse rest (dropWhile (\(LocatedMath span' _) -> spanStart span' < spanEnd source) tokens)
        | otherwise = tokens
  children <- case node of LocatedSequence values -> Right (concatMap refine values); _ -> Left "Generated union needs a source sequence"
  (if root then rootMeaning else meaning) env{envConstructed = definitions <> envConstructed env} (LocatedMath location (LocatedSequence (collapse replacements children)))
 where
  parseShape = withObject "generated family candidate" $ \f -> GeneratedShape <$> (f .: "union" >>= sourceSpan) <*> (f .: "opening" >>= sourceSpan) <*> (f .: "closing" >>= sourceSpan) <*> (f .: "colon" >>= sourceSpan) <*> (f .: "pointDomain" >>= mapM (locatedSyntaxWith True)) <*> (f .: "radiusCondition" >>= mapM (locatedSyntaxWith True)) <*> (f .: "traceCondition" >>= mapM (locatedSyntaxWith True)) <*> (f .: "separators" >>= mapM sourceSpan) <*> (f .: "value" >>= locatedSyntaxWith True)
  identity (LocatedMath source _) = maybe (Left "Generated family needs resolved lexical binders") Right (Map.lookup (spanStart source) (envBindings env))
  target source = fromMaybe "" (bindingContext source) <> "/" <> bindingName source
  interpret (GeneratedShape union opening closing colon pointDomain radiusCondition traceCondition separators value, evidence) = case (pointDomain, radiusCondition, traceCondition) of
    ([pointSyntax@(LocatedMath pointSpan _), LocatedMath relation _, carrierSyntax], radiusSyntax@(LocatedMath radiusSpan _) : _, LocatedMath _ (LocatedCommand "MetricDiameter" Nothing [metricSyntax, traceSyntax]) : _) -> do
      point <- identity pointSyntax
      radius <- identity radiusSyntax
      carrierIdentity <- identity carrierSyntax
      metric <- identity (sourceAtom metricSyntax)
      subsetSyntax <- case filter (not . blank) (sourceTokens traceSyntax) of
        [_, intersection, subset] | commandIs True "cap" intersection -> Right subset
        _ -> Left "Generator boundedness needs its displayed trace intersection"
      subset <- identity subsetSyntax
      unless (fmap snd (lookup "metric" (restrictionReferences evidence)) == Just (target metric)) (Left "Bounded-trace premise does not match the active metric binding")
      unless (fmap snd (lookup "subset" (restrictionReferences evidence)) == Just (target subset)) (Left "Bounded-trace premise does not match the active subset binding")
      unless (lookup "trace" (restrictionSyntax evidence) == Just traceSyntax) (Left "Bounded-trace premise does not match the displayed trace")
      unless (bindingRole point == Just "ball-generator-point" && bindingRole radius == Just "ball-generator-radius" && bindingType radius == "ℝ" && bindingName point /= bindingName radius && bindingType point == bindingName carrierIdentity) (Left "Generated family requires distinct point and real radius binders on its carrier")
      carrier <- meaning env carrierSyntax
      metricValue <- meaning env metricSyntax
      traceValue <- setMeaning env traceSyntax
      positive <- sourceSequence radiusCondition >>= meaning env
      ball <- meaning env value
      condition <- sourceSequence traceCondition >>= meaning env
      let occupied = envOccupied env <> map bindingName (Map.elems (envBindings env))
          fresh previous name = if name `elem` previous then fresh previous (name <> "_") else name
          setName = fresh occupied "book_ball_set"
          positiveName = fresh (setName : occupied) "book_ball_positive"
          boundedName = fresh (positiveName : setName : occupied) "book_ball_bounded"
          familySpan = SourceSpan (spanStart union) (spanEnd closing)
          proofSpan = SourceSpan (spanStart radiusSpan) (spanEnd radiusSpan)
          binders = [(bindingName point, carrier), (bindingName radius, SourceConstant radiusSpan "ℝ"), (positiveName, Parenthesized proofSpan (RepeatedEvaluation positive)), (boundedName, Parenthesized proofSpan (MetricBoundedSet proofSpan metricValue traceValue))]
          predicate = ExistentialSetPredicate familySpan setName carrier binders ball condition
          components = [(pointSpan, "generator.exists.point"), (relation, "generator.exists.point-domain"), (radiusSpan, "generator.exists.radius"), (colon, "generator.conditions"), (closing, "generator.scope-end")] <> [(source, "generator.condition-separator") | source <- separators]
          family = GuardedSet familySpan opening components carrier evidence predicate
      pure (GeneratedUnion familySpan union carrier evidence family)
    _ -> Left "Generated family has an unsupported source predicate"

sourceTokens :: LocatedMath -> [LocatedMath]
sourceTokens (LocatedMath _ (LocatedSequence children)) = concatMap refine children
sourceTokens syntax = refine syntax

sourceCharacters :: LocatedMath -> Maybe [(Int, Char)]
sourceCharacters (LocatedMath location node) = case node of
  LocatedText text -> Just (zip [spanStart location ..] (T.unpack text))
  LocatedSequence children -> concat <$> traverse sourceCharacters children
  _ -> Nothing

sourceTextAt :: LocatedMath -> SourceSpan -> Maybe Text
sourceTextAt syntax location = do
  characters <- Map.fromList <$> sourceCharacters syntax
  T.pack <$> traverse (`Map.lookup` characters) [spanStart location .. spanEnd location - 1]

literalMeaning :: MeaningEnv -> SourceSpan -> Maybe LocatedMath -> NumericDomain -> Object -> Either String Expr
literalMeaning env location syntax domain fields = do
  (number, operator) <- parseEither (\f -> (,) <$> f .: "numeral" <*> (SourceSpan <$> f .: "numericStart" <*> f .: "numericEnd")) fields
  unless (spanStart location >= 0 && spanEnd location >= spanStart location && not (T.null number) && T.all isDigit number && spanEnd operator - spanStart operator == T.length number && spanStart operator >= spanStart location && spanEnd operator <= spanEnd location) (Left "Numeric literal does not match its source span")
  case syntax of
    Just original -> unless (sourceTextAt original operator == Just number && maybe False (T.all isDigit . T.dropAround numericWhitespace . T.pack . map snd) (sourceCharacters original)) (Left "Numeric literal does not match its source text")
    Nothing -> pure ()
  validateNumericDomain env domain
  pure (Literal location operator (WitnessLiteral domain) number)

prefixMeaning :: MeaningEnv -> LocatedMath -> Value -> Either String Expr
prefixMeaning env syntax@(LocatedMath location _) value = do
  (domain, operator, boundValue) <-
    parseEither
      ( withObject "prefix predicate" $ \fields -> do
          onlyFields ["domain", "operator", "bound"] fields
          domain <- fields .: "domain" >>= numericDomain
          operatorValue <- fields .: "operator"
          LocatedMath operator node <- locatedSyntaxWith True operatorValue
          unless (node == LocatedText "<") (fail "Unsupported prefix predicate operator")
          (,,) domain operator <$> fields .: "bound"
      )
      value
  bound <- annotatedMeaning env False boundValue
  case bound of
    Literal _ source (WitnessLiteral boundDomain) number -> unless (boundDomain == domain && sourceTextAt syntax source == Just number && sourceTextAt syntax operator == Just "<") (Left "Prefix predicate does not match its source bound")
    _ -> Left "Prefix predicate needs a source-owned numeric bound"
  let fresh candidateName = if candidateName `elem` envOccupied env then fresh (candidateName <> "_") else candidateName
      name = fresh "book_radius"
  pure (OperatorSection location operator radiusSection name domain bound)

contextualMeaning :: MeaningEnv -> Object -> Either String Expr
contextualMeaning env fields = do
  (location, operator, identity, constant, consumer, literal) <- parseEither parse fields
  let LiteralConsumer declaration callee _ = consumer
  unless (all (`Map.member` envRecords env) [constant, declaration, callee]) (Left "Missing declaration evidence for a contextual literal")
  pure (ContextualLiteral location operator identity constant consumer literal)
 where
  parse f = do
    onlyFields ["kind", "start", "end", "args", "operatorStart", "operatorEnd", "interpretationId", "expectedConstant", "consumer", "lowering"] f
    arguments <- f .: "args" :: Parser [Value]
    unless (null arguments) (fail "Contextual literals have no source operands")
    location <- SourceSpan <$> f .: "start" <*> f .: "end"
    operator <- SourceSpan <$> f .: "operatorStart" <*> f .: "operatorEnd"
    consumer <-
      f .: "consumer"
        >>= withObject
          "literal consumer"
          ( \c -> do
              onlyFields ["declaration", "callee", "argumentPosition"] c
              position <- c .: "argumentPosition"
              unless (position >= 0) (fail "Negative literal consumer position")
              LiteralConsumer <$> c .: "declaration" <*> c .: "callee" <*> pure position
          )
    literal <-
      f .: "lowering"
        >>= withObject
          "literal lowering"
          ( \l -> do
              onlyFields ["kind", "sourceLiteral"] l
              kind <- l .: "kind" :: Parser Text
              unless (kind == "contextual-literal") (fail "Unsupported contextual literal lowering")
              l .: "sourceLiteral"
          )
    unless (spanStart location >= 0 && spanEnd location >= spanStart location && not (T.null literal) && T.all isDigit literal && spanStart operator >= spanStart location && spanEnd operator <= spanEnd location && spanEnd operator - spanStart operator == T.length literal) (fail "Contextual literal source span mismatch")
    (,,,,,) location operator <$> f .: "interpretationId" <*> f .: "expectedConstant" <*> pure consumer <*> pure literal

numericOperandMeaning :: MeaningEnv -> NumericDomain -> [LocatedMath] -> Either String Expr
numericOperandMeaning env@MeaningEnv{envConstructed = constructed} domain raw = do
  unless (all numericScalarToken raw) (Left "Numeric expression is outside its source scalar grammar")
  validateNumericDomain env domain
  let (tokens, expressions) = numbers raw
      scoped = env{envConstructed = Map.fromList expressions <> constructed}
  source <- sourceSequence (filter (not . numericBlank) tokens)
  meaning scoped source
 where
  numericBlank (LocatedMath _ (LocatedText text)) = not (T.null text) && T.all numericWhitespace text
  numericBlank _ = False
  numbers [] = ([], [])
  numbers (first@(LocatedMath location (LocatedText text)) : rest)
    | not (T.null text)
    , T.all isDigit text =
        let (digits, tailTokens) = collect (spanEnd location) rest
            number = text <> T.concat (map symbol digits)
            ending = case reverse digits of LocatedMath final _ : _ -> spanEnd final; [] -> spanEnd location
            source = SourceSpan (spanStart location) ending
            (tokens, expressions) = numbers tailTokens
         in (LocatedMath source (LocatedRaw "") : tokens, (spanStart source, (source, Literal source source (WitnessLiteral domain) number)) : expressions)
    | otherwise = let (tokens, expressions) = numbers rest in (first : tokens, expressions)
  numbers (first : rest) = let (tokens, expressions) = numbers rest in (first : tokens, expressions)
  collect _ [] = ([], [])
  collect previous remaining@(token@(LocatedMath location (LocatedText text)) : rest)
    | previous == spanStart location, not (T.null text), T.all isDigit text = let (digits, tailTokens) = collect (spanEnd location) rest in (token : digits, tailTokens)
    | otherwise = ([], remaining)
  collect _ remaining = ([], remaining)

numericWhitespace :: Char -> Bool
numericWhitespace c = isSpace c || c `elem` ['\x1c', '\x1d', '\x1e', '\x1f', '\x85']

numericScalarToken :: LocatedMath -> Bool
numericScalarToken (LocatedMath _ (LocatedText text)) = not (T.null text) && T.all (\c -> isDigit c || numericWhitespace c || c `elem` ['+', '*', '/', '(', ')', '-']) text
numericScalarToken _ = False

-- The shared parser owns the syntax. This decoder accepts only its lossless
-- located nodes, not arbitrary Python-normalized annotations with hidden meaning.
locatedSyntax :: Value -> Parser LocatedMath
locatedSyntax = locatedSyntaxWith False

-- Structural candidates refine text into tokens. Their token end is derived
-- solely from the original start and Unicode text, never from generated Lean.
locatedSyntaxWith :: Bool -> Value -> Parser LocatedMath
locatedSyntaxWith refined = withObject "located syntax" $ \fields -> do
  kind <- fields .: "kind" :: Parser Text
  start <- fields .: "start"
  end <-
    if kind == "text"
      then do
        body <- fields .: "text"
        fields .:? "end" .!= (start + T.length body)
      else fields .: "end"
  unless (start >= 0 && end >= start) (fail "Invalid source span")
  let allowed rest = unless (all ((`elem` ("kind" : "start" : "end" : rest)) . K.toText) (KM.keys fields)) (fail "Unknown semantic source annotation")
  node <- case kind of
    "sequence" -> allowed ["items"] >> LocatedSequence <$> (fields .: "items" >>= mapM (locatedSyntaxWith refined))
    "group" -> allowed ["body"] >> LocatedGroup <$> (fields .: "body" >>= locatedSyntaxWith refined)
    "text" -> do
      allowed ["text"]
      body <- fields .: "text"
      unless (end - start == T.length body) (fail "Text source span does not match its Unicode length")
      pure (LocatedText body)
    "bound-symbol" | refined -> do
      allowed ["text"]
      body <- fields .: "text"
      unless (end - start == T.length body) (fail "Bound-symbol span does not match its Unicode length")
      pure (LocatedText body)
    "command" -> do
      allowed ["name", "optional", "args"]
      name <- fields .: "name"
      optional <- fields .: "optional" >>= traverse (locatedSyntaxWith refined)
      arguments <- fields .: "args" >>= mapM (locatedSyntaxWith refined)
      pure (LocatedCommand name optional arguments)
    "script" -> do
      allowed ["base", "marker", "argument"]
      LocatedScript <$> (fields .: "base" >>= locatedSyntaxWith refined) <*> fields .: "marker" <*> (fields .: "argument" >>= locatedSyntaxWith refined)
    "raw" | refined -> allowed ["text"] >> LocatedRaw <$> fields .: "text"
    _ -> fail "Syntax constructor is not yet in the native semantic interpreter"
  let children = case node of
        LocatedSequence xs -> xs
        LocatedGroup body -> [body]
        LocatedCommand _ optional xs -> maybe xs (: xs) optional
        LocatedScript base _ argument -> [base, argument]
        _ -> []
  unless (all (\(LocatedMath span' _) -> spanStart span' >= start && spanEnd span' <= end) children) (fail "Child source span escapes its parent")
  pure (LocatedMath (SourceSpan start end) node)

binding :: Value -> Parser (Int, BindingIdentity)
binding = withObject "resolved source binding" $ \fields -> do
  status <- fields .: "status" :: Parser Text
  unless (status == "resolved") $ do
    reason <- fields .:? "reason" .!= "Missing source-owned binding"
    fail (T.unpack ("Source binding is unresolved: " <> reason))
  origin <- fields .:? "indexOrigin"
  lower <- fields .:? "indexLowerBound" >>= traverse naturalBound
  shifted <- fields .:? "indexOffset"
  selector <- fields .:? "occurrenceSelector"
  named <- fields .:? "namedSubscript" .!= False
  sourceSymbol <- fields .:? "symbol"
  local <- fields .:? "localBinder" .!= False
  sourceContext <- fields .:? "binderContext"
  sourceStart <- fields .:? "start"
  sourceEnd <- fields .:? "end"
  let width = (-) <$> sourceEnd <*> sourceStart
  when (maybe False (< 0) width) (fail "Invalid source binding span")
  offset <- fields .: "formulaOffset"
  projection <- fields .:? "projection" :: Parser (Maybe Text)
  unless (projection `elem` [Nothing, Just "Subtype.val"]) (fail "Unknown source binder projection")
  ty <- fields .: "leanType"
  constant <- fields .:? "constantDeclaration"
  adaptation <- case projection of
    Just _ -> pure SubtypeValue
    Nothing
      | KM.member "indexOffset" fields -> do
          unless (ty `elem` ["Nat", "ℕ"]) (fail "Shifted source indices require a natural-number binder")
          NaturalOffset <$> fields .: "indexOffset"
      | KM.member "indexLowerBound" fields -> pure SubtypeValue
      | otherwise -> pure DirectReference
  when (isJust constant && adaptation /= DirectReference) (fail "Constants cannot have a source binder adaptation")
  identity <- BindingIdentity <$> fields .: "id" <*> fields .: "declaration" <*> fields .: "leanName" <*> pure ty <*> pure constant <*> pure adaptation <*> pure origin <*> pure (lower <|> shifted) <*> pure selector <*> pure named <*> pure sourceSymbol <*> pure width <*> pure local <*> pure sourceContext <*> fields .:? "binderRole"
  pure (offset, identity)

naturalBound :: Value -> Parser Integer
naturalBound (String text) | isDecimal text = pure (decimal text)
naturalBound value = do
  number <- parseJSON value
  unless (number >= 0) (fail "Natural index lower bound must be nonnegative")
  pure number

meaning :: MeaningEnv -> LocatedMath -> Either String Expr
meaning env@MeaningEnv{envConstructed = constructed} syntax@(LocatedMath location _)
  | Just (source, expression) <- Map.lookup (spanStart location) constructed, source == location = Right expression
  | otherwise = sourceMeaning env syntax

sourceMeaning :: MeaningEnv -> LocatedMath -> Either String Expr
sourceMeaning env@MeaningEnv{envConstants = constants, envBindings = bindings, envConventions = conventions} (LocatedMath location node) = case node of
  LocatedText value
    | T.length value == 1 && T.all isAlpha value -> case Map.lookup (spanStart location) bindings of
        Just identity -> sourceReference location identity
        Nothing -> Left "No explicit source binding for native variable"
    | not (T.null value) && T.all isDigit value -> Right (Literal location location InferredLiteral value)
    | otherwise -> Left "Text needs construction recognition"
  LocatedGroup body -> Parenthesized location <$> meaning env body
  LocatedCommand "AmbientClosure" Nothing [carrier, subset] -> do
    unless (sourceCarrierTokens bindings [carrier]) (Left "Ambient closure requires a resolved source carrier")
    AmbientSetClosure location <$> meaning env carrier <*> setMeaning env subset
  LocatedCommand "MetricBall" Nothing [metric, center, radius] -> do
    carrier <- maybe (Left "Metric ball requires a source metric-space parameter") Right (sourceMetric bindings metric)
    size <- realScalarMeaning env radius >>= maybe (meaning env radius) pure
    ExplicitMetricBall location carrier (envBranchProof env) <$> meaning env metric <*> meaning env center <*> pure size
  LocatedCommand "MetricDiameter" Nothing [metric, subset] -> do
    carrier <- maybe (Left "Metric diameter requires a source metric-space parameter") Right (sourceMetric bindings metric)
    ExplicitMetricDiameter location carrier <$> meaning env metric <*> setMeaning env subset
  LocatedCommand "restrict" Nothing [function, subset] -> do
    metric <- sourceDistance env function
    value <- maybe (meaning env function) pure metric
    Restriction location value <$> setMeaning env subset
  LocatedCommand "Pair" Nothing [tag, point] -> do
    let LocatedMath pointSpan _ = sequenceAtom point
    identity <- maybe (Left "Tagged pair needs a resolved point in a dependent fiber") Right (Map.lookup (spanStart pointSpan) bindings)
    (familyName, _) <- case T.splitOn " " (bindingType identity) of
      [family, index] | word family && word index -> Right (family, index)
      _ -> Left "Tagged pair needs a named family applied to a named index"
    let original = maybe [] (\context -> Map.findWithDefault [] context (envRecords env)) (bindingContext identity)
        families = [name | SourceBinder name ty <- original, name == familyName, naturalTypeFamily ty]
    family <- case families of [name] -> Right name; _ -> Left "Tagged pair needs a unique named Nat-indexed type family in its original context"
    SigmaPair location family <$> meaning env tag <*> meaning env point
  LocatedCommand "seqPower" Nothing [alphabet@(LocatedMath alphabetSpan alphabetNode), index] -> do
    body <- case alphabetNode of
      LocatedSequence children -> case concatMap (filter (not . blank) . refine) children of
        [LocatedMath opening (LocatedCommand "{" Nothing []), LocatedMath _ (LocatedText "0"), LocatedMath _ (LocatedText ","), LocatedMath _ (LocatedText "1"), LocatedMath _ (LocatedCommand "}" Nothing [])] -> Right (BinarySequenceAlphabet alphabetSpan opening (Map.lookup "realSequenceEmbedding" conventions))
        _ -> sourceCarrierValue alphabet
      _ -> sourceCarrierValue alphabet
    unless (sourceCarrierTokens bindings [index]) (Left "Sequence power needs a registered index carrier")
    domain <- meaning env index
    pure (CoordinateSpace location (SourceSpan (spanStart location) (spanStart location + 9)) IndexedCoordinates body domain)
  LocatedCommand "Homeomorphic" Nothing [left, right] -> do
    lhs <- meaning env left
    rhs <- meaning env right
    let operator = SourceSpan (spanStart location) (spanStart location + 13)
    pure (NonemptyType location operator (HomeomorphismType location operator lhs rhs))
  LocatedCommand "NonnegativeDimensionLevel" Nothing [argument@(LocatedMath source _)] -> do
    number <- maybe (Left "A nonnegative dimension level requires a natural numeral") Right (bareText argument)
    unless (not (T.null number) && T.all isDigit number) (Left "A nonnegative dimension level requires a natural numeral")
    pure (Literal location (SourceSpan (spanStart location) (spanStart location + 26)) (SourceLiteral dimensionNumeral source dimensionOrigin) number)
  LocatedCommand name Nothing [endpoint, upper@(LocatedMath upperSpan _)]
    | name `elem` ["OpenInterval", "LeftClosedInterval"]
    , commandIs False "infty" upper -> do
        value <- meaning env endpoint
        pure (UpperRay location (SourceSpan (spanStart location) (spanStart location + T.length name + 1)) (if name == "OpenInterval" then OpenUpperRay else ClosedUpperRay) value upperSpan)
  LocatedCommand "Sequence" Nothing [body, LocatedMath domainSpan _] -> do
    found <- sequenceCandidate (locatedValue (LocatedMath location node))
    SequenceCandidate _ origin declaration components <- maybe (Left "Sequence index range requires a reviewed binding rule") Right found
    identity <- maybe (Left "Sequence binder has no resolved source identity") Right (Map.lookup declaration bindings)
    unless (bindingLocalBinder identity && bindingType identity `elem` ["Nat", "ℕ"]) (Left "Sequence binder has not been resolved lexically")
    value <- meaning env body
    pure (Lambda location (SourceSpan (spanStart location) (spanStart location + 9)) (Binder SequenceBinder identity "ℕ" (Just domainSpan) Nothing components origin) value)
  LocatedCommand "SetDifference" Nothing [left, right]
    | commandIs False "R" left && commandIs False "QQ" right -> do
        unless (Map.lookup "R" constants == Just "ℝ" && Map.lookup "QQ" constants == Just "ℚ") (Left "Real/rational embedding requires its registered constants")
        lhs <- setMeaningIn env (Just right) left
        let LocatedMath rightSpan _ = right
        pure (EmbeddedRationalComplement location (SourceSpan (spanStart location) (spanStart location + 14)) lhs (RationalImage rightSpan))
    | otherwise -> SetExpression location (SourceSpan (spanStart location) (spanStart location + 14)) DifferenceSet <$> setMeaningIn env (Just right) left <*> setMeaningIn env (Just left) right
  LocatedCommand name Nothing arguments
    | name `elem` ["frac", "Abs", "Closure", "Ball", "ClosedInterval", "OpenInterval", "LeftClosedInterval"] -> do
        operands <- traverse (meaning env) arguments
        Macro (Just location) <$> operation name operands
  LocatedCommand "TwoPointSpace" Nothing [] -> Right (BinaryAlphabet location)
  LocatedCommand name Nothing [] | Just target <- Map.lookup name constants -> Right (SourceConstant location target)
  LocatedCommand name Nothing []
    | name `elem` ["phi", "epsilon", "varepsilon", "rho", "delta", "iota"] ->
        maybe (Left "No explicit source binding for native variable") (sourceReference location) (Map.lookup (spanStart location) bindings)
  LocatedScript (LocatedMath baseSpan (LocatedCommand "ell" Nothing [])) "^" argument -> do
    powerIndex <- extendedExponent env argument
    let LocatedMath argumentSpan _ = argument
    pure (RealSequenceSpace location (SourceSpan (spanStart argumentSpan - 1) (spanStart argumentSpan)) baseSpan powerIndex)
  LocatedScript base@(LocatedMath _ (LocatedText number)) "^" argument
    | not (T.null number)
    , T.all isDigit number
    , Just value <- readMaybe (T.unpack number) :: Maybe Integer
    , value > 0 -> do
        lhs <- meaning env base
        rhs <- integerMeaning bindings argument
        let LocatedMath argumentSpan _ = argument
        pure (RealIntegerPower location (SourceSpan (spanStart argumentSpan - 1) (spanStart argumentSpan)) lhs rhs)
  LocatedScript base marker argument
    | Just (name, decoration) <- decoratedSymbol base marker argument
    , Just identity <- Map.lookup (sourceStart base) bindings
    , decoration == StarredName || bindingNamedSubscript identity -> do
        unless (bindingSourceSymbol identity == Just name && isNothing (bindingIndexOrigin identity)) (Left "Decorated names require their own resolved source binding")
        let operator = case decoration of
              SubscriptName -> SourceSpan (sourceStart argument - 1) (sourceStart argument)
              StarredName -> SourceSpan (sourceStart base + 1) (spanEnd location)
        pure (NamedReference location operator decoration identity)
  LocatedScript base "^" argument | sourceCarrierTokens bindings [base] -> do
    let natural = sourceAtom argument
        LocatedMath naturalSpan naturalNode = natural
        numeric = case naturalNode of LocatedText value -> not (T.null value) && T.all isDigit value; _ -> False
        named = maybe False ((`elem` ["Nat", "ℕ"]) . bindingType) (Map.lookup (spanStart naturalSpan) bindings)
    unless (numeric || named) (Left "Finite carrier power requires a natural-number dimension")
    dimension <- meaning env argument
    body <- meaning env base
    let LocatedMath argumentSpan _ = argument
    pure (CoordinateSpace location (SourceSpan (spanStart argumentSpan - 1) (spanStart argumentSpan)) FiniteCoordinates body (FiniteIndex naturalSpan dimension))
  LocatedScript base marker argument | marker `elem` ["_", "^"] -> do
    identity <- maybe (Left "Indexed base has no resolved family binder") Right (Map.lookup (sourceStart base) bindings)
    let ty = bindingType identity
    unless ("→" `T.isInfixOf` ty || "->" `T.isInfixOf` ty || "∀" `T.isPrefixOf` ty) (Left "Subscript requires a function-valued family binder")
    let naturalFamily = T.strip (fst (T.breakOn "→" ty)) `elem` ["Nat", "ℕ"]
    when (marker == "^" && (bindingOccurrenceSelector identity /= Just "superscript-base" || not naturalFamily)) (Left "Sequence superscripts need an explicit source selector and a Nat-indexed family")
    function <- case bindingIndexOrigin identity of
      Nothing -> meaning env base
      Just _ -> case base of
        LocatedMath span' (LocatedText value) | T.length value == 1 && T.all isAlpha value && naturalFamily -> Right (Reference span' identity)
        _ -> Left "Reindexing requires a named natural-number family"
    unless (indexable function) (Left "Indexed base needs a named family or nested source application")
    originalIndex <- meaning env argument
    index <- case bindingIndexOrigin identity of
      Nothing -> pure originalIndex
      Just origin -> do
        unless (maybe False (>= origin) (indexLowerBound bindings argument)) (Left "Reindexed family needs a source index with the declared lower bound")
        let LocatedMath indexSpan _ = argument
        pure (ShiftIndex indexSpan origin originalIndex)
    let operator = SourceSpan (sourceStart argument - 1) (sourceStart argument)
        notation = if marker == "_" then Subscript else Superscript
    pure (Index location operator notation function index)
  LocatedSequence children -> Scoped location <$> sequenceMeaningAt env location (concatMap refine children)
  _ -> Left "Construction is not yet in the native semantic interpreter"
 where
  word text = not (T.null text) && T.all (\c -> isAlphaNum c || c == '_') text
  naturalTypeFamily ty =
    let (domain, target) = T.breakOn "→" (T.replace "->" "→" ty)
        result = T.stripStart (T.drop 1 target)
     in T.strip domain `elem` ["Nat", "ℕ"] && (result == "Type" || case T.stripPrefix "Type " result of Just universe -> not (T.null universe) && T.all (not . isSpace) universe; _ -> False)
  sourceCarrierValue syntax = do
    unless (sourceCarrierTokens bindings [syntax]) (Left "Sequence power needs a registered carrier or the binary alphabet {0,1}")
    meaning env syntax
  sourceStart (LocatedMath source _) = spanStart source
  indexable Reference{} = True
  indexable Index{} = True
  indexable _ = False

sourceAtom :: LocatedMath -> LocatedMath
sourceAtom syntax@(LocatedMath location node) = case node of
  LocatedGroup body -> sourceAtom body
  LocatedSequence children -> case trim children of [child] -> sourceAtom child; _ -> syntax
  LocatedText value -> LocatedMath (SourceSpan (spanStart location + T.length value - T.length (T.stripStart value)) (spanEnd location)) (LocatedText (T.strip value))
  _ -> syntax

sequenceAtom :: LocatedMath -> LocatedMath
sequenceAtom syntax@(LocatedMath location node) = case node of
  LocatedSequence children -> case trim children of [child] -> sequenceAtom child; _ -> syntax
  LocatedText value -> LocatedMath (SourceSpan (spanStart location + T.length value - T.length (T.stripStart value)) (spanEnd location)) (LocatedText (T.strip value))
  _ -> syntax

sourceMetric :: Map.Map Int BindingIdentity -> LocatedMath -> Maybe MetricDomain
sourceMetric bindings syntax =
  let simple@(LocatedMath location _) = sequenceAtom syntax
   in Map.lookup (spanStart location) bindings >>= (`metricCarrier` simple)

sourceDistance :: MeaningEnv -> LocatedMath -> Either String (Maybe Expr)
sourceDistance env@MeaningEnv{envBindings = bindings, envConstructed = constructed} syntax@(LocatedMath location _) =
  let LocatedMath simpleSpan node = sequenceAtom syntax
   in case sourceMetric bindings syntax of
        Just carrier -> Just . DistanceFunction location (MetricDistance carrier) <$> meaning env syntax
        Nothing -> case Map.lookup (spanStart simpleSpan) bindings of
          Just identity
            | named simpleSpan node identity
            , [left, right, "ℝ"] <- map T.strip (T.splitOn "→" (bindingType identity))
            , left == right ->
                Just . DistanceFunction location (BinaryDistance left) <$> meaning env syntax
          _ -> Right Nothing
 where
  named _ (LocatedText text) identity = bindingSourceSymbol identity == Just text
  named sourceSpan' (LocatedRaw _) identity = case Map.lookup (spanStart sourceSpan') constructed of Just (_, Reference _ source) -> bindingName source == bindingName identity && bindingContext source == bindingContext identity; _ -> False
  named _ (LocatedSequence children) identity = case concatMap refine children of
    LocatedMath _ (LocatedCommand "hat" Nothing []) : rest | [LocatedMath _ (LocatedText name)] <- trim rest -> bindingSourceSymbol identity == Just ("\\hat " <> name)
    _ -> False
  named _ _ _ = False

-- Reuse the source scalar grammar, but construct casts as semantic operands.
-- Their spans remain those of the original atoms; unknown functions/macros
-- leave the source expression unchanged rather than guessing a real type.
realScalarMeaning :: MeaningEnv -> LocatedMath -> Either String (Maybe Expr)
realScalarMeaning env@MeaningEnv{envBindings = bindings, envConstructed = constructed} syntax = do
  let raw = case syntax of LocatedMath _ (LocatedSequence children) -> concatMap refine children; _ -> refine syntax
  case convert raw of
    Nothing -> pure Nothing
    Just (tokens, expressions) -> do
      source <- sourceSequence tokens
      Just <$> meaning env{envConstructed = Map.fromList expressions <> constructed} source
 where
  convert [] = Just ([], [])
  convert (token@(LocatedMath location (LocatedText text)) : rest)
    | not (T.null text)
    , T.all isDigit text =
        let (digits, remaining) = collect (spanEnd location) rest
            number = text <> T.concat (map symbol digits)
            ending = case reverse digits of LocatedMath final _ : _ -> spanEnd final; [] -> spanEnd location
            source = SourceSpan (spanStart location) ending
         in insert source (Literal source source InferredLiteral number) remaining
    | Just identity <- Map.lookup (spanStart location) bindings
    , bindingType identity `elem` ["Nat", "ℕ", "Int", "ℤ", "Real", "ℝ"] =
        insert location (Reference location identity) rest
    | T.all isSpace text || text `elem` ["+", "-", "*", "/", "(", ")"] = do
        (tokens, expressions) <- convert rest
        pure (token : tokens, expressions)
    | otherwise = Nothing
  convert _ = Nothing
  insert location body rest = do
    (tokens, expressions) <- convert rest
    pure (LocatedMath location (LocatedRaw "") : tokens, (spanStart location, (location, RealScalar location body)) : expressions)
  collect _ [] = ([], [])
  collect previous remaining@(token@(LocatedMath location (LocatedText text)) : rest)
    | previous == spanStart location, not (T.null text), T.all isDigit text = let (digits, tailTokens) = collect (spanEnd location) rest in (token : digits, tailTokens)
    | otherwise = ([], remaining)
  collect _ remaining = ([], remaining)

-- Map-arrow recognition applies to the root of an expression job. Nested
-- source groups do not acquire new binders merely because an arrow occurs there.
rootMeaning :: MeaningEnv -> LocatedMath -> Either String Expr
rootMeaning env syntax@(LocatedMath location _) = do
  conjunction <- conjunctionShape (locatedValue syntax)
  if conjunction == Null
    then do
      found <- convergenceShape (locatedValue syntax)
      if found == Null then rootOrdinaryMeaning env syntax else convergenceMeaning env syntax found
    else do
      (clauses, operator) <- parseEither (withObject "source conjunction" (\f -> (,) <$> (f .: "clauses" >>= mapM (locatedSyntaxWith True)) <*> (f .: "operator" >>= sourceSpan))) conjunction
      expressions <- traverse (\clause@(LocatedMath source _) -> Scoped source <$> rootMeaning env{envRootSpan = Just source, envBindings = Map.filterWithKey (\offset _ -> spanStart source <= offset && offset < spanEnd source) (envBindings env)} clause) clauses
      case expressions of
        [left, right] -> pure (Conjunction location operator left right)
        _ -> Left "Conjunction requires two nonempty clauses"

convergenceMeaning :: MeaningEnv -> LocatedMath -> Value -> Either String Expr
convergenceMeaning env@MeaningEnv{envBindings = bindings} (LocatedMath location _) value = do
  (left, right, operator, declaration, name, offsets, components) <- parseEither shape value
  identity <- maybe (Left "Unresolved convergence index") Right (Map.lookup declaration bindings)
  unless (bindingLocalBinder identity) (Left "Convergence index must be resolved lexically")
  unless (all naturalFamily offsets) (Left "Convergence requires natural-number-indexed families")
  when (any (\(offset, source) -> offset > spanStart operator && bindingSourceSymbol source == Just name) (Map.toList bindings)) (Left "The limit contains the bound sequence index")
  body <- meaning env left
  let witness = SequenceWitness identity body
      LocatedMath targetSpan targetNode = case right of
        LocatedMath _ (LocatedSequence [single]) -> single
        _ -> right
  target <- case targetNode of
    LocatedText number | not (T.null number) && T.all isDigit number -> pure (Literal targetSpan targetSpan (SequenceLiteral witness) number)
    _ | LocatedMath _ (LocatedCommand "MetricDiameter" _ _) <- sequenceAtom left -> realScalarMeaning env right >>= maybe (meaning env right) pure
    _ -> meaning env right
  let LocatedMath bodySpan _ = left
      origin = case bindingAdaptation identity of NaturalOffset offset -> Just offset; _ -> Nothing
  pure (SequenceConvergence location operator components origin (ConvergenceSequence bodySpan witness target) target)
 where
  naturalFamily offset = maybe False ((`elem` ["Nat", "ℕ"]) . T.strip . fst . T.breakOn "→" . bindingType) (Map.lookup offset bindings)
  shape :: Value -> Parser (LocatedMath, LocatedMath, SourceSpan, Int, Text, [Int], [(SourceSpan, Text)])
  shape = withObject "convergence candidate" $ \fields -> do
    left <- fields .: "left" >>= candidateSequence
    rightTokens <- fields .: "right" >>= mapM (locatedSyntaxWith True)
    let trimmed = trim rightTokens
        withoutStop = if not (null trimmed) && symbol (last trimmed) `elem` [".", ","] then init trimmed else trimmed
    right <- either fail pure (sourceSequence withoutStop)
    arrow <- fields .: "arrow" >>= sourceSpan
    binder <- fields .: "binder"
    (declaration, name, offsets, components) <- withObject "convergence binder" (\b -> (,,,) <$> b .: "declarationOffset" <*> b .: "symbol" <*> b .: "familyOffsets" <*> (b .: "components" >>= mapM component)) binder
    pure (left, right, arrow, declaration, name, offsets, components)
  component v = (,) <$> sourceSpan v <*> withObject "binding component" (.: "target") v

candidateSequence :: [Value] -> Parser LocatedMath
candidateSequence values = mapM (locatedSyntaxWith True) values >>= either fail pure . sourceSequence

rootOrdinaryMeaning :: MeaningEnv -> LocatedMath -> Either String Expr
rootOrdinaryMeaning env@MeaningEnv{envBindings = bindings} syntax@(LocatedMath location node) = case node of
  LocatedSequence children ->
    let tokens = concatMap (filter (not . blank) . refine) children
        arrows = [i | (i, LocatedMath _ (LocatedCommand "mapsto" _ _)) <- zip [0 :: Int ..] tokens]
     in case (arrows, tokens) of
          _ | Just result <- typedMapMeaning env location tokens -> result
          ([], _) -> meaning env syntax
          ([1], LocatedMath pointSpan (LocatedText point) : LocatedMath arrowSpan (LocatedCommand "mapsto" Nothing []) : body@(_ : _))
            | T.length point == 1 && T.all isAlpha point -> do
                identity <- maybe (Left "Unresolved mapsto binder") Right (Map.lookup (spanStart pointSpan) bindings)
                unless (bindingLocalBinder identity) (Left "Unresolved mapsto binder")
                context <- maybe (Left "Missing source-owned mapsto domain context") Right (bindingBinderContext identity)
                when (T.null context) (Left "Missing source-owned mapsto domain context")
                bodySyntax <- sourceSequence body
                value <- meaning env bodySyntax
                pure (Lambda location arrowSpan (Binder MapstoBinder identity (bindingType identity) Nothing (Just context) [(pointSpan, "lambda.binder")] 0) value)
          _ -> Left "Mapsto requires one scalar binder with a reviewed domain"
  _ -> meaning env syntax

-- A signature with a defining equation owns its input binder. The domain is
-- a subspace predicate supplied by the source, not an inferred ambient type.
typedMapMeaning :: MeaningEnv -> SourceSpan -> [LocatedMath] -> Maybe (Either String Expr)
typedMapMeaning env@MeaningEnv{envBindings = bindings} location tokens = case tokens of
  function : colon : predicate : LocatedMath arrowSpan (LocatedCommand "to" Nothing []) : _
    | symbol colon == ":"
    , [3] <- [i | (i, LocatedMath _ (LocatedCommand "to" _ _)) <- zip [0 :: Int ..] tokens]
    , comma : _ <- [i | (i, token) <- zip [0 :: Int ..] tokens, symbol token == ","]
    , comma > 4
    , equation@(name : opening : LocatedMath pointSpan (LocatedText point) : closing : equals : _ : _) <- drop (comma + 1) tokens
    , tokenIdentity function == tokenIdentity name
    , map symbol [opening, closing, equals] == ["(", ")", "="]
    , T.length point == 1 && T.all isAlpha point -> Just $ do
        identity <- maybe (Left "Unresolved typed-map binder") Right (Map.lookup (spanStart pointSpan) bindings)
        unless (bindingLocalBinder identity) (Left "Unresolved typed-map binder")
        context <- maybe (Left "Missing source-owned typed-map domain context") Right (bindingBinderContext identity)
        when (T.null context) (Left "Missing source-owned typed-map domain context")
        value <- meaning env predicate
        let LocatedMath predicateSource _ = predicate
            LocatedMath colonSpan _ = colon
            domain = SubtypeType predicateSource (SourceSpan (spanStart predicateSource) (spanStart predicateSource + 1)) ExplicitSubspace value
        target <- sourceSequence (take (comma - 4) (drop 4 tokens)) >>= meaning env
        functionValue <- meaning env function
        body <- sourceSequence equation >>= meaning env
        let functionType = FunctionType location arrowSpan ("book_arrow_input_" <> T.pack (show (spanStart arrowSpan))) domain target
            typed = TypeDeclaration location (SourceSpan (spanStart colonSpan) (spanStart colonSpan + 1)) functionType functionValue
            quantified = TypedMapForall location (SourceSpan (spanStart pointSpan) (spanStart pointSpan + 1)) identity domain body
        pure (Comparisons [typed, quantified])
  _ -> Nothing
 where
  tokenIdentity (LocatedMath _ node) = case node of
    LocatedText text -> Just (False, text)
    LocatedCommand name _ _ -> Just (True, name)
    _ -> Nothing

bareText :: LocatedMath -> Maybe Text
bareText (LocatedMath _ node) = case node of
  LocatedSequence children -> case trim children of [child] -> bareText child; _ -> Nothing
  LocatedText value -> Just (T.strip value)
  _ -> Nothing

extendedExponent :: MeaningEnv -> LocatedMath -> Either String Expr
extendedExponent env@MeaningEnv{envBindings = bindings} syntax@(LocatedMath location node) = case node of
  LocatedGroup body -> extendedExponent env body
  LocatedSequence children -> case trim children of [child] -> extendedExponent env child; _ -> Left "Sequence-space exponent needs a reviewed extended-nonnegative-real interpretation"
  LocatedCommand "infty" Nothing [] -> Right (ExtendedTop location)
  LocatedText value
    | value /= T.strip value ->
        extendedExponent env (LocatedMath (SourceSpan (spanStart location + T.length value - T.length (T.stripStart value)) (spanEnd location)) (LocatedText (T.strip value)))
  LocatedText value
    | let number = T.strip value
    , not (T.null number)
    , T.all isDigit number ->
        let source = SourceSpan (spanStart location + T.length value - T.length (T.stripStart value)) (spanEnd location)
         in Right (Literal source source (InstanceLiteral extendedNumeral) number)
  _ -> do
    identity <- maybe (Left "Sequence-space exponent needs a reviewed extended-nonnegative-real interpretation") Right (Map.lookup (spanStart location) bindings)
    unless (bindingType identity `elem` ["ENNReal", "ℝ≥0∞"]) (Left "Sequence-space exponent needs a reviewed extended-nonnegative-real interpretation")
    meaning env syntax

integerMeaning :: Map.Map Int BindingIdentity -> LocatedMath -> Either String Expr
integerMeaning bindings syntax@(LocatedMath location node) = case node of
  LocatedGroup body -> Parenthesized location <$> integerMeaning bindings body
  LocatedSequence children -> integerArithmetic bindings (concatMap refine children)
  LocatedText _ -> integerArithmetic bindings (refine syntax)
  _ -> Left "Integer exponent requires scalar integer arithmetic"

integerArithmetic :: Map.Map Int BindingIdentity -> [LocatedMath] -> Either String Expr
integerArithmetic bindings raw = do
  let tokens = trim raw
  location <- spanOf tokens
  case arithmeticChoice tokens of
    Just (_, Divide) -> Left "Unsupported integer-exponent arithmetic"
    Just (position, op) -> do
      left <- operand (take position tokens)
      right <- operand (drop (position + 1) tokens)
      let LocatedMath operator _ = tokens !! position
      pure (Scalar location operator op left right)
    Nothing -> case tokens of
      LocatedMath operator (LocatedText "-") : rest -> IntegerNegate location operator <$> operand rest
      [LocatedMath source (LocatedText value)]
        | T.all isAlpha value -> do
            identity <- maybe (Left "Integer exponent needs an explicitly resolved Nat or Int variable") Right (Map.lookup (spanStart source) bindings)
            unless (bindingType identity `elem` ["Nat", "ℕ", "Int", "ℤ"]) (Left "Integer exponent needs an explicitly resolved Nat or Int variable")
            reference <- sourceReference source identity
            pure (if bindingType identity `elem` ["Nat", "ℕ"] then IntegerCast source reference else reference)
      [single@(LocatedMath _ (LocatedGroup _))] -> integerMeaning bindings single
      first : rest | symbol first == "(", not (null rest), symbol (last rest) == ")", enclosesTokens tokens -> Parenthesized location <$> operand (init rest)
      _ | all (\t -> T.length (symbol t) == 1 && T.all isDigit (symbol t)) tokens -> Right (Literal location location (FixedLiteral "ℤ") (T.concat (map symbol tokens)))
      _ -> Left "Unsupported integer-exponent arithmetic"
 where
  operand values = do
    location <- spanOf (trim values)
    Scoped location <$> integerArithmetic bindings values

sourceReference :: SourceSpan -> BindingIdentity -> Either String Expr
sourceReference location identity = do
  unless (isNothing (bindingIndexOrigin identity)) (Left "Reindexed families require an explicit supported source index")
  when (bindingNamedSubscript identity) (Left "Named subscripts require their own source-symbol rule")
  pure (Reference location identity)

decoratedSymbol :: LocatedMath -> Text -> LocatedMath -> Maybe (Text, NameDecoration)
decoratedSymbol (LocatedMath _ (LocatedText base)) marker argument
  | T.length base == 1
  , T.all isAlpha base = do
      suffix <- unwrap argument
      case marker of
        "_" | not (T.null suffix), T.all isDigit suffix -> Just (base <> "_" <> suffix, SubscriptName)
        "^" | suffix == "*" -> Just (base <> "^*", StarredName)
        _ -> Nothing
 where
  unwrap (LocatedMath _ (LocatedGroup body)) = unwrap body
  unwrap (LocatedMath _ (LocatedSequence children)) = case (if marker == "^" then trim children else children) of [child] -> unwrap child; _ -> Nothing
  unwrap (LocatedMath _ (LocatedText value)) = Just value
  unwrap _ = Nothing
decoratedSymbol _ _ _ = Nothing

indexLowerBound :: Map.Map Int BindingIdentity -> LocatedMath -> Maybe Integer
indexLowerBound bindings (LocatedMath location node) = case node of
  LocatedSequence children -> case trim children of [child] -> indexLowerBound bindings child; _ -> Nothing
  LocatedText value | not (T.null (T.strip value)) && T.all isDigit (T.strip value) -> readMaybe (T.unpack (T.strip value))
  _ -> bindingIndexLowerBound =<< Map.lookup (spanStart location) bindings

refine :: LocatedMath -> [LocatedMath]
refine (LocatedMath location (LocatedText text)) =
  [LocatedMath (SourceSpan offset (offset + 1)) (LocatedText (T.singleton char)) | (offset, char) <- zip [spanStart location ..] (T.unpack text)]
refine (LocatedMath _ (LocatedCommand name Nothing [])) | name `elem` [",", ";", "!", "quad", "qquad", " "] = []
refine (LocatedMath location (LocatedScript base marker argument)) =
  let reversed = reverse (refine base)
      (digits, prefix) = span (\t -> not (T.null (symbol t)) && T.all isDigit (symbol t)) reversed
      merged = case reverse digits of
        LocatedMath first _ : _ | marker == "^" -> let LocatedMath final _ = base in LocatedMath (SourceSpan (spanStart first) (spanEnd final)) (LocatedText (T.concat (map symbol (reverse digits)))) : prefix
        _ -> reversed
   in case merged of
        lastBase@(LocatedMath baseLocation _) : previous -> reverse previous <> [LocatedMath (SourceSpan (spanStart baseLocation) (spanEnd location)) (LocatedScript lastBase marker argument)]
        [] -> [LocatedMath location (LocatedScript base marker argument)]
refine node = [node]

symbol :: LocatedMath -> Text
symbol (LocatedMath _ (LocatedText text)) = text
symbol _ = ""

blank :: LocatedMath -> Bool
blank node = not (T.null (symbol node)) && T.all isSpace (symbol node)

trim :: [LocatedMath] -> [LocatedMath]
trim = reverse . dropWhile blank . reverse . dropWhile blank

spanOf :: [LocatedMath] -> Either String SourceSpan
spanOf [] = Left "Empty expression operand"
spanOf values@(LocatedMath first _ : _) = let LocatedMath final _ = last values in Right (SourceSpan (spanStart first) (spanEnd final))

sequenceMeaning :: MeaningEnv -> [LocatedMath] -> Either String Expr
sequenceMeaning env raw = do
  location <- spanOf (trim raw)
  sequenceMeaningAt env location raw

sequenceMeaningAt :: MeaningEnv -> SourceSpan -> [LocatedMath] -> Either String Expr
sequenceMeaningAt env location raw = do
  let (registered, original) = registeredSymbols env raw
      current = registered{envCurrentSpan = Just location}
  tokens <- sizedTokens original
  grouped <- realCasesMeaning current location tokens
  construction <- case grouped <|> sourceLogicMeaning current location tokens <|> finiteFamilyMeaning current tokens of Just result -> pure (Just result); Nothing -> naturalFamilyMeaning current location tokens
  fromMaybe (ordinarySequenceMeaningAt current location tokens) construction

-- Delimiter sizing has no mathematical action, but only a size command
-- attached to the matching source parenthesis may be erased.
sizedTokens :: [LocatedMath] -> Either String [LocatedMath]
sizedTokens [] = Right []
sizedTokens (token@(LocatedMath _ node) : rest) = case node of
  LocatedCommand name optional arguments
    | name `elem` ["big", "Big", "bigg", "Bigg", "bigl", "Bigl", "biggl", "Biggl", "bigr", "Bigr", "biggr", "Biggr"] -> do
        unless (isNothing optional && null arguments) (Left "Delimiter sizing supports no optional argument or macro operands")
        let delimiters
              | "l" `T.isSuffixOf` name = ["("]
              | "r" `T.isSuffixOf` name = [")"]
              | otherwise = ["(", ")"]
        unless (maybe False ((`elem` delimiters) . symbol) (listToMaybe (dropWhile blank rest))) (Left "Delimiter sizing requires the matching ordinary parenthesis")
        sizedTokens rest
  _ -> (token :) <$> sizedTokens rest

sourceLogicMeaning :: MeaningEnv -> SourceSpan -> [LocatedMath] -> Maybe (Either String Expr)
sourceLogicMeaning env@MeaningEnv{envBindings = bindings} location raw = case filter (not . blank) raw of
  [opening@(LocatedMath operator _), point, closing@(LocatedMath end _)]
    | commandIs True "{" opening
    , commandIs True "}" closing
    , sourceLetter point -> Just $ do
        value <- meaning env point
        pure (SingletonSet location operator end Nothing value)
  [first, comma@(LocatedMath commaSpan _), second, relation@(LocatedMath operator _), domain]
    | symbol comma == ","
    , commandIs True "in" relation
    , all sourceLetter [first, second] -> Just $ do
        unless (sourceCarrierTokens bindings [domain] || sourceSetExpression env [domain]) (Left "Shared membership requires a resolved carrier or set domain")
        domainSyntax <- sourceSequence [domain]
        values <-
          traverse
            ( \(member, point@(LocatedMath source _)) -> do
                pointSyntax <- sourceSequence [point]
                value <- meaning env pointSyntax
                target <- setMeaningIn env (Just pointSyntax) domainSyntax
                let clause = SourceSpan (spanStart source) (spanEnd location)
                pure (Derived (sharedMembership member) (SetExpression clause operator Member value target))
            )
            (zip [0 ..] [first, second])
        case values of
          [left, right] -> pure (Conjunction location (SourceSpan (spanStart commaSpan) (spanStart commaSpan + 1)) left right)
          _ -> Left "Shared membership requires two points"
  _ -> Nothing
 where
  sourceLetter (LocatedMath _ (LocatedText text)) = T.length text == 1 && T.all isAlpha text
  sourceLetter _ = False

finiteFamilyMeaning :: MeaningEnv -> [LocatedMath] -> Maybe (Either String Expr)
finiteFamilyMeaning env@MeaningEnv{envBindings = bindings} raw = case filter (not . blank) raw of
  tokens@[LocatedMath _ (LocatedScript firstBase "_" firstIndex), operator, continuation, separator, lastToken]
    | commandIs True "supseteq" operator && commandIs True "supseteq" separator && commandIs True "cdots" lastToken -> Just $ do
        (family, lower, origin) <- sourceFamily firstBase firstIndex
        (nextBase, nextIndex) <- indexed continuation
        (nextFamily, following, _) <- sourceFamily nextBase nextIndex
        unless (sameFamily family nextFamily && following == lower + 1) (Left "Decreasing family requires one family and consecutive literal indices")
        make tokens operator family (NaturalTail lower origin) (subscript firstIndex "chain-index" : subscript nextIndex "chain-index" : [component separator "chain-continuation", component lastToken "chain-continuation"])
    | any (\name -> commandIs True name operator && commandIs True name separator) ["cap", "cup"] && commandIs True "cdots" continuation -> Just $ do
        (family, lower, origin) <- sourceFamily firstBase firstIndex
        (lastBase, lastIndex) <- indexed lastToken
        other <- identity lastBase
        unless (sameFamily family other) (Left "Finite intersection endpoints must name the same resolved family")
        let upperAtom@(LocatedMath upperSpan upperNode) = sourceAtom lastIndex
            upperBinding = Map.lookup (spanStart upperSpan) bindings
            natural = maybe False ((`elem` ["Nat", "ℕ"]) . bindingType) upperBinding
            guaranteed = indexLowerBound bindings upperAtom <|> if natural then Just 0 else Nothing
        unless (maybe True ((`elem` ["Nat", "ℕ"]) . bindingType) upperBinding && maybe False (>= lower) guaranteed) (Left "Finite intersection needs ordered natural endpoints above the family origin")
        unless (case upperNode of LocatedText value -> not (T.null value); _ -> False) (Left "Finite intersection upper endpoint must be a source natural")
        upper <- meaning env lastIndex
        make tokens operator family (FiniteNaturalInterval lower origin upper) [subscript firstIndex "range-start-subscript", subscript lastIndex "range-end-subscript", component continuation "finite-range-ellipsis", component separator "range-separator"]
  _ -> Nothing
 where
  indexed (LocatedMath _ (LocatedScript base "_" index)) = Right (base, index)
  indexed _ = Left "Indexed family range requires indexed endpoints"
  identity (LocatedMath source _) = maybe (Left "Family range needs a resolved family") Right (Map.lookup (spanStart source) bindings)
  sourceFamily base index = do
    family <- identity base
    let (domain, result) = T.breakOn "→" (T.replace "->" "→" (bindingType family))
        origin = fromMaybe 0 (bindingIndexOrigin family)
        LocatedMath _ node = sourceAtom index
    unless (T.strip domain `elem` ["Nat", "ℕ"] && "Set " `T.isPrefixOf` T.stripStart (T.drop 1 result)) (Left "Family range requires a natural-indexed set family")
    lower <- case node of LocatedText value | not (T.null value) && T.all isDigit value -> Right (decimal value); _ -> Left "Family range requires a literal lower endpoint"
    unless (lower >= origin) (Left "Family range starts below its source index origin")
    pure (family, lower, origin)
  sameFamily left right = bindingContext left == bindingContext right && bindingName left == bindingName right && bindingIndexOrigin left == bindingIndexOrigin right
  component (LocatedMath source _) role = (source, role)
  subscript (LocatedMath source _) role = (SourceSpan (spanStart source - 1) (spanStart source), role)
  make tokens operator family range components = do
    location <- spanOf tokens
    let stem = (case range of NaturalTail{} -> "book_tail_index_"; FiniteNaturalInterval{} -> "book_finite_index_") <> T.pack (show (spanStart location))
        fresh name = if name `elem` envOccupied env then fresh (name <> "_") else name
        function = RangeFamily location (fresh stem) family range
        LocatedMath operationSpan _ = operator
    case range of
      NaturalTail first origin -> pure (DecreasingFamily location operationSpan components first origin function)
      FiniteNaturalInterval{} -> do
        plan <- foldPlan (SetBinary (if commandIs True "cap" operator then Intersection else Union)) AssociativeFold
        pure (RepeatedBinary location operationSpan components family range plan function)

-- Case recognition supplies source spans and fresh proof names. Branch proofs
-- remain scoped semantic inputs, and every actual transport is checked by Lean.
realCasesMeaning :: MeaningEnv -> SourceSpan -> [LocatedMath] -> Either String (Maybe (Either String Expr))
realCasesMeaning env@MeaningEnv{envConstructed = constructed} location raw = do
  found <- casesNode (object ["tree" .= locatedValue (LocatedMath location (LocatedSequence raw)), "occupied" .= envOccupied env])
  if found == Null
    then pure Nothing
    else do
      (tokens, replacements) <- parseEither grouped found
      pure
        ( Just
            ( do
                expressions <- traverse interpret replacements
                let definitions = Map.fromList [(spanStart source, (source, expression)) | ((source, _, _), expression) <- zip replacements expressions]
                sequenceMeaningAt env{envConstructed = definitions <> constructed} location tokens
            )
        )
 where
  interpret (source, opening, branches) = case branches of
    [first, second] -> do
      firstExpression <- branch first
      secondExpression <- branch second
      condition <- meaning env (caseCondition first)
      pure (DependentConditional source opening realConditional condition firstExpression secondExpression)
    _ -> Left "Cases require exactly two branches"
  branch shape = do
    condition <- meaning env (caseCondition shape)
    let scoped = if caseEquality shape then env{envBranchProof = Just (caseProofName shape)} else env
    body <- meaning scoped (caseBody shape)
    pure (CaseBranch (caseSpan shape) (caseSeparator shape) (caseProofName shape) (conditionalResult realConditional) condition body)
  grouped = withObject "grouped cases syntax" $ \fields -> do
    items <- fields .: "items" :: Parser [Value]
    parsed <- mapM item items
    pure (map fst parsed, [replacement | (_, Just replacement) <- parsed])
  item value =
    withObject
      "cases source token"
      ( \fields -> do
          kind <- fields .: "kind" :: Parser Text
          if kind /= "real-cases"
            then (,) <$> locatedSyntaxWith True value <*> pure Nothing
            else do
              source <- sourceSpan value
              opening <- fields .: "opening" >>= sourceSpan
              branches <- fields .: "branches" >>= mapM caseShape
              pure (LocatedMath source (LocatedRaw ""), Just (source, opening, branches))
      )
      value

data CaseShape = CaseShape
  { caseSpan :: SourceSpan
  , caseSeparator :: SourceSpan
  , caseProofName :: Text
  , caseEquality :: Bool
  , caseCondition :: LocatedMath
  , caseBody :: LocatedMath
  }

caseShape :: Value -> Parser CaseShape
caseShape = withObject "case branch candidate" $ \fields ->
  CaseShape <$> (SourceSpan <$> fields .: "start" <*> fields .: "end") <*> (fields .: "separator" >>= separatorSpan) <*> fields .: "proofName" <*> fields .: "equality" <*> (fields .: "condition" >>= locatedSyntaxWith True) <*> (fields .: "body" >>= locatedSyntaxWith True)
 where
  separatorSpan value = do LocatedMath location _ <- locatedSyntaxWith True value; pure location

-- Explicit whole-symbol bindings own decorated references. Collapsing their
-- exact source spans permits the ordinary grammar to handle applications too.
registeredSymbols :: MeaningEnv -> [LocatedMath] -> (MeaningEnv, [LocatedMath])
registeredSymbols env@MeaningEnv{envBindings = bindings, envConstructed = constructed} raw =
  let (tokens, expressions) = collapse raw
   in (env{envConstructed = Map.fromList expressions <> constructed}, tokens)
 where
  collapse [] = ([], [])
  collapse remaining@(first@(LocatedMath location _) : rest)
    | Just identity <- Map.lookup (spanStart location) bindings
    , isNothing (bindingIndexOrigin identity)
    , not (bindingNamedSubscript identity)
    , Just width <- bindingSourceWidth identity
    , width > spanEnd location - spanStart location
    , let end = spanStart location + width
          (parts, tailTokens) = span (\(LocatedMath source _) -> spanEnd source <= end) remaining
    , not (null parts)
    , let LocatedMath final _ = last parts
    , spanEnd final == end
    , Just symbol' <- spelling parts
    , bindingSourceSymbol identity == Just symbol' =
        let source = SourceSpan (spanStart location) end
            (tokens, expressions) = collapse tailTokens
         in (LocatedMath source (LocatedRaw "") : tokens, (spanStart source, (source, Reference source identity)) : expressions)
    | otherwise = let (tokens, expressions) = collapse rest in (first : tokens, expressions)
  spelling parts
    | all textNode parts
    , let name = T.concat (map symbol parts)
          (base, primes) = T.span isAlpha name
    , T.length base == 1
    , not (T.null primes)
    , T.all (== '\'') primes =
        Just name
    | LocatedMath _ (LocatedCommand "hat" Nothing []) : rest <- parts
    , [LocatedMath _ (LocatedText name)] <- trim rest
    , T.length name == 1
    , T.all isAlpha name =
        Just ("\\hat " <> name)
    | otherwise = Nothing
  textNode (LocatedMath _ LocatedText{}) = True
  textNode _ = False

-- Collapse grammar-owned source ranges into already typed semantic operands.
-- Placeholders are internal: the source JSON decoder rejects LocatedRaw nodes.
summationMeaning :: MeaningEnv -> SourceSpan -> [LocatedMath] -> Either String Expr
summationMeaning env@MeaningEnv{envBindings = bindings, envConstructed = constructed} location raw = do
  found <- summationChunks (locatedValue (LocatedMath location (LocatedSequence raw)))
  shapes <- parseEither parseShapes found
  case shapes of
    [] -> relationMeaning env raw
    first : _ -> do
      replacements <- traverse interpret shapes
      tokens <- parseEither (mapM (locatedSyntaxWith True)) (sumTokens first)
      let collapse (shape, expression) values = take (sumFirst shape) values <> [LocatedMath (sumSpan shape) (LocatedRaw "")] <> drop (sumLast shape) values
          collapsed = foldr collapse tokens (zip shapes replacements)
          definitions = Map.fromList [(spanStart (sumSpan shape), (sumSpan shape, expression)) | (shape, expression) <- zip shapes replacements]
      sequenceMeaningAt env{envConstructed = definitions <> constructed} location collapsed
 where
  parseShapes value = parseJSON value >>= mapM sumShape
  interpret shape = do
    identity <- maybe (Left "Unresolved sum index") Right (Map.lookup (sumIndex shape) bindings)
    unless (bindingLocalBinder identity) (Left "Sum index must be resolved lexically")
    body <- meaning env (sumBody shape)
    bound <- if sumKind shape == InfiniteSum then pure Nothing else Just <$> meaning env (sumBound shape)
    let LocatedMath bodySpan _ = sumBody shape
        function = SumFunction bodySpan identity (if sumKind shape == TailSum then bound else Nothing) body
    pure (Summation (sumSpan shape) (sumOperator shape) (sumComponents shape) (sumKind shape) bound function)

data SumShape = SumShape
  { sumSpan :: SourceSpan
  , sumOperator :: SourceSpan
  , sumIndex :: Int
  , sumBody :: LocatedMath
  , sumBound :: LocatedMath
  , sumKind :: SummationKind
  , sumComponents :: [(SourceSpan, Text)]
  , sumFirst :: Int
  , sumLast :: Int
  , sumTokens :: [Value]
  }

sumShape :: Value -> Parser SumShape
sumShape = withObject "summation candidate" $ \fields -> do
  script <- fields .: "script"
  scriptSpan <- sourceSpan script
  (operator, rangeStart) <- withObject "sum script" (\s -> (,) <$> (s .: "base" >>= sourceSpan) <*> (s .: "argument" >>= withObject "sum range" (.: "start"))) script
  index <- fields .: "binder" >>= withObject "sum binder" (.: "start")
  relation <- fields .: "relation" >>= withObject "sum relation" (\r -> do start <- r .: "start"; end <- r .:? "end" .!= (start + 1); pure (SourceSpan start end))
  body <- fields .: "body" >>= locatedSyntaxWith True
  bound <- fields .: "bound" >>= locatedSyntaxWith True
  mode <- fields .: "mode" :: Parser Text
  kind <- case mode of "finite" -> pure FiniteSum; "infinite" -> pure InfiniteSum; "tail" -> pure TailSum; _ -> fail "Unknown summation range"
  let LocatedMath bodySpan _ = body
      components = [(SourceSpan index (index + 1), "sum.lambda.binder"), (SourceSpan (rangeStart - 1) rangeStart, "sum.range"), (relation, "sum.range")]
  SumShape (SourceSpan (spanStart scriptSpan) (spanEnd bodySpan)) operator index body bound kind components <$> fields .: "first" <*> fields .: "last" <*> fields .: "tokens"

predicateSetMeaning :: MeaningEnv -> SourceSpan -> [LocatedMath] -> Either String Expr
predicateSetMeaning env@MeaningEnv{envBindings = bindings, envConstructed = constructed} location raw = do
  found <- predicateSets (locatedValue (LocatedMath location (LocatedSequence raw)))
  shapes <- parseEither (parseJSON >=> mapM predicateShape) found
  case shapes of
    [] -> summationMeaning env location raw
    first : _ -> do
      expressions <- traverse interpret shapes
      tokens <- parseEither (mapM (locatedSyntaxWith True)) (predicateTokens first)
      let collapse (shape, _) values = take (predicateFirst shape) values <> [LocatedMath (predicateSpan shape) (LocatedRaw "")] <> drop (predicateLast shape) values
          collapsed = foldr collapse tokens (zip shapes expressions)
          definitions = Map.fromList [(spanStart (predicateSpan shape), (predicateSpan shape, expression)) | (shape, expression) <- zip shapes expressions]
      sequenceMeaningAt env{envConstructed = definitions <> constructed} location collapsed
 where
  interpret shape = do
    identity <- maybe (Left "Unresolved set generator") Right (Map.lookup (predicateIndex shape) bindings)
    unless (bindingLocalBinder identity) (Left "Set generator requires a resolved lexical binder")
    context <- maybe (Left "Set generator requires a source-owned domain context") Right (bindingBinderContext identity)
    when (T.null context) (Left "Set generator requires a source-owned domain context")
    body <- meaning env (predicateBody shape)
    domain <- traverse (meaning env) (predicateDomain shape)
    let LocatedMath bodySpan _ = predicateBody shape
        function = BoundFunction bodySpan PredicateBody identity body
    pure (SetComprehension (predicateSpan shape) (predicateOperator shape) (predicateComponents shape) identity domain function)

data PredicateShape = PredicateShape
  { predicateSpan :: SourceSpan
  , predicateOperator :: SourceSpan
  , predicateIndex :: Int
  , predicateBody :: LocatedMath
  , predicateDomain :: Maybe LocatedMath
  , predicateComponents :: [(SourceSpan, Text)]
  , predicateFirst :: Int
  , predicateLast :: Int
  , predicateTokens :: [Value]
  }

predicateShape :: Value -> Parser PredicateShape
predicateShape = withObject "set comprehension candidate" $ \fields -> do
  opening <- fields .: "opening" >>= sourceSpan
  closing <- fields .: "closing" >>= sourceSpan
  binder <- fields .: "binder" >>= sourceSpan
  colon <- fields .: "colon" >>= sourceSpan
  body <- fields .: "body" >>= locatedSyntaxWith True
  domain <- fields .:? "domain" >>= traverse (locatedSyntaxWith True)
  relation <- fields .:? "domainRelation" >>= traverse sourceSpan
  let components = [(binder, "set.lambda.binder"), (colon, "set.lambda.body")] <> maybe [] (\source -> [(source, "set.lambda.domain")]) relation <> [(closing, "set.lambda.scope-end")]
  PredicateShape (SourceSpan (spanStart opening) (spanEnd closing)) opening (spanStart binder) body domain components <$> fields .: "first" <*> fields .: "last" <*> fields .: "tokens"

infimumMeaning :: MeaningEnv -> SourceSpan -> Value -> Either String Expr
infimumMeaning env@MeaningEnv{envBindings = bindings} location candidateValue = do
  (binder, relation, domainSyntax, bodySyntax, tokens) <- parseEither shape candidateValue
  identity <- maybe (Left "Unresolved infimum generator") Right (Map.lookup binder bindings)
  unless (bindingLocalBinder identity) (Left "Infimum generator must be resolved lexically")
  body <- meaning env bodySyntax
  domain <- meaning env domainSyntax
  let LocatedMath bodySpan _ = bodySyntax
      function = BoundFunction bodySpan ImageBody identity body
  imageSpan <- spanOf (drop 1 tokens)
  case tokens of
    LocatedMath operator _ : LocatedMath opening _ : _ ->
      let components = [(SourceSpan binder (binder + 1), "image.lambda.binder"), (relation, "image.domain")]
       in pure (Infimum location operator (ImageSet imageSpan opening components function domain))
    _ -> Left "Infimum requires its source image-set delimiters"
 where
  shape = withObject "bounded infimum candidate" $ \fields -> do
    binder <- fields .: "binder" >>= withObject "infimum binder" (.: "start")
    relation <- fields .: "relation" >>= sourceSpan
    domain <- fields .: "domain" >>= locatedSyntaxWith True
    body <- fields .: "body" >>= candidateSequence
    tokens <- fields .: "tokens" >>= mapM (locatedSyntaxWith True)
    pure (binder, relation, domain, body, tokens)

ordinarySequenceMeaningAt :: MeaningEnv -> SourceSpan -> [LocatedMath] -> Either String Expr
ordinarySequenceMeaningAt env@MeaningEnv{envBindings = bindings} location raw
  | [function, colon, domain, LocatedMath arrowSpan (LocatedCommand "to" Nothing []), codomain] <- filter (not . blank) raw
  , symbol colon == ":" = do
      unless (sourceCarrierTokens bindings [domain] && sourceCarrierTokens bindings [codomain]) (Left "Function declaration requires resolved domain and codomain carriers")
      source <- meaning env domain
      target <- meaning env codomain
      value <- meaning env function
      let LocatedMath colonSpan _ = colon
          functionType = FunctionType location arrowSpan ("book_arrow_input_" <> T.pack (show (spanStart arrowSpan))) source target
      pure (TypeDeclaration location (SourceSpan (spanStart colonSpan) (spanStart colonSpan + 1)) functionType value)
  | otherwise = case definitionPositions raw of
      [] -> do
        infimum <- boundedInfimum (locatedValue (LocatedMath location (LocatedSequence raw)))
        if infimum == Null then predicateSetMeaning env location raw else infimumMeaning env location infimum
      [position] -> do
        let left = take position raw
            remaining = drop (position + 2) raw
            right = if not (null remaining) && symbol (last remaining) `elem` [",", "."] then init remaining else remaining
        lhs <- sourceSequence left >>= meaning env
        rhs <- sourceSequence right >>= meaning env
        let LocatedMath colon _ = raw !! position
            LocatedMath equals _ = raw !! (position + 1)
        pure (DefiningEquality location (SourceSpan (spanStart colon) (spanStart equals + 1)) lhs rhs)
      _ -> Left "Chained local definitions are not registered"

-- The existing source grammar provides candidates; only the resolved lexical
-- index can turn one into a semantic binder. No generated Lean text is parsed.
naturalFamilyMeaning :: MeaningEnv -> SourceSpan -> [LocatedMath] -> Either String (Maybe (Either String Expr))
naturalFamilyMeaning env@MeaningEnv{envBindings = bindings} location raw = do
  shapes <- naturalFamilies (locatedValue (LocatedMath location (LocatedSequence raw)))
  candidates <- traverse (parseEither familyShape) shapes
  pure $ case filter shapeWhole candidates of
    shape : _ -> Just (interpret shape)
    [] -> case nonoverlapping (sortOn (spanStart . shapeOperator) (filter ((`elem` ["bigcap", "bigcup"]) . shapeName) candidates)) of
      [] -> Nothing
      selected -> Just $ do
        expressions <- traverse interpret selected
        let replacements = [(SourceSpan (spanStart (shapeOperator shape)) (shapeEnd shape), expression) | (shape, expression) <- zip selected expressions]
            definitions = Map.fromList [(spanStart source, (source, expression)) | (source, expression) <- replacements]
        sequenceMeaningAt env{envConstructed = definitions <> envConstructed env} location (collapse replacements raw)
 where
  nonoverlapping [] = []
  nonoverlapping (shape : rest) = shape : nonoverlapping (dropWhile ((< shapeEnd shape) . spanStart . shapeOperator) rest)
  collapse [] tokens = tokens
  collapse _ [] = []
  collapse replacements@((source, _) : rest) tokens@(token@(LocatedMath current _) : remaining)
    | spanStart current < spanStart source = token : collapse replacements remaining
    | spanStart current == spanStart source = LocatedMath source (LocatedRaw "") : collapse rest (dropWhile (\(LocatedMath span' _) -> spanStart span' < spanEnd source) tokens)
    | otherwise = tokens
  interpret shape = do
    identity <- maybe (Left "Indexed family has no resolved source index") Right (Map.lookup (shapeIndex shape) bindings)
    unless (bindingLocalBinder identity && bindingType identity == "ℕ") (Left "Indexed family needs a registered natural-number binder")
    value <- meaning env (shapeBody shape)
    let operator = shapeOperator shape
        name = shapeName shape
        LocatedMath bodySpan _ = shapeBody shape
        familySpan = SourceSpan (spanStart operator) (shapeEnd shape)
        familyBinding notation domain domainName = FamilyBinding notation identity domain domainName (shapeComponents shape)
    case name of
      "prod" -> do
        familyIdentity' <- sourceIdentity (shapeFamilyOffset shape)
        let setFamily = naturalSetFamily (bindingType familyIdentity')
            body = MultipleCalls value
            lowered = if setFamily then MultipleCalls (SubtypeType bodySpan (SourceSpan (fromMaybeOffset (shapeFamilyOffset shape)) (fromMaybeOffset (shapeFamilyOffset shape) + 1)) SetAsSubspace body) else body
        pure (FamilyLambda (SourceSpan (spanStart operator) (spanEnd bodySpan)) operator (familyBinding ProductFamily "ℕ" (Just "Nat") Nothing True) lowered)
      "ExternalDisjointUnion" -> do
        let family = FamilyLambda location operator (familyBinding FunctionFamily "ℕ" (Just "Nat") Nothing True) (MultipleCalls value)
        pure (DependentSum location operator family)
      _ -> do
        carrier <- case shapeCarrierOffset shape of
          Just offset -> do
            source <- maybe (Left "Indexed set has no source carrier") Right (Map.lookup offset bindings)
            pure (DirectCarrier (Reference (SourceSpan offset (offset + fromMaybeWidth source)) source))
          Nothing -> do
            source <- sourceIdentity (shapeFamilyOffset shape)
            let offset = fromMaybeOffset (shapeFamilyOffset shape)
            pure (IndexedPredicateCarrier (Reference (SourceSpan offset (offset + fromMaybeWidth source)) source))
        let lower = shapeLower shape
            domain = maybe "Nat" (\bound -> "{n : Nat // " <> bound <> " ≤ n}") lower
            declaration = shapeDeclaration shape
            family = FamilyLambda familySpan (SourceSpan declaration (declaration + 1)) (familyBinding FunctionFamily domain (if isNothing lower then Just "Nat" else Nothing) (Just carrier) False) value
        pure (IndexedSet familySpan operator (if name == "bigcap" then IndexedIntersection else IndexedUnion) lower family)
  sourceIdentity offset = maybe (Left "Indexed family needs a source family identity") Right (offset >>= (`Map.lookup` bindings))
  fromMaybeOffset = fromMaybe 0
  fromMaybeWidth = fromMaybe 1 . bindingSourceWidth
  naturalSetFamily ty =
    let (domain, target) = T.breakOn "→" (T.replace "->" "→" ty)
     in T.strip domain `elem` ["Nat", "ℕ"] && "Set " `T.isPrefixOf` T.stripStart (T.drop 1 target)

data FamilyShape = FamilyShape
  { shapeName :: Text
  , shapeOperator :: SourceSpan
  , shapeBody :: LocatedMath
  , shapeIndex :: Int
  , shapeDeclaration :: Int
  , shapeComponents :: [(SourceSpan, Text)]
  , shapeFamilyOffset :: Maybe Int
  , shapeCarrierOffset :: Maybe Int
  , shapeLower :: Maybe Text
  , shapeWhole :: Bool
  , shapeEnd :: Int
  }

familyShape :: Value -> Parser FamilyShape
familyShape = withObject "indexed family candidate" $ \fields -> do
  marker <- fields .: "marker"
  name <- withObject "family operator" (.: "name") marker
  operator <- sourceSpan marker
  body <- fields .: "family" >>= locatedSyntaxWith True
  index <- fields .: "index" >>= withObject "family index" (.: "start")
  binder <- fields .: "binder"
  (declaration, components, familyOffset, carrierOffset, lower) <- withObject "family binder" (\b -> (,,,,) <$> b .: "declarationOffset" <*> (b .: "components" >>= mapM component) <*> b .:? "familyOffset" <*> b .:? "carrierOffset" <*> b .:? "lowerBound") binder
  FamilyShape name operator body index declaration components familyOffset carrierOffset lower <$> fields .: "whole" <*> fields .: "end"
 where
  component value = (,) <$> sourceSpan value <*> withObject "binding component" (.: "target") value

sourceSpan :: Value -> Parser SourceSpan
sourceSpan = withObject "source span" $ \fields -> SourceSpan <$> fields .: "start" <*> fields .: "end"

definitionPositions :: [LocatedMath] -> [Int]
definitionPositions = scan 0 0
 where
  scan :: Int -> Int -> [LocatedMath] -> [Int]
  scan _ _ [] = []
  scan depth position (token@(LocatedMath _ node) : rest) =
    let text = symbol token
        brace = case node of LocatedCommand name Nothing [] -> name; _ -> ""
        delta
          | text == "(" || brace == "{" = 1
          | text == ")" || brace == "}" = -1
          | otherwise = 0
        nextEquals = case rest of next : _ -> symbol next == "="; [] -> False
     in [position | depth == 0 && text == ":" && nextEquals] <> scan (depth + delta) (position + 1) rest

relationMeaning :: MeaningEnv -> [LocatedMath] -> Either String Expr
relationMeaning env@MeaningEnv{envBindings = bindings} raw = do
  let tokens = trim raw
  location <- spanOf tokens
  case comparisonChoices tokens of
    [(equals, Equal)]
      | [member] <- topLevelCommands "in" tokens
      , member > equals
      , null (topLevelCommands "IncludedIn" tokens) -> do
          leftSyntax <- sourceSequence (take equals tokens)
          middleSyntax <- sourceSequence (take (member - equals - 1) (drop (equals + 1) tokens))
          domainSyntax <- sourceSequence (drop (member + 1) tokens)
          left <- meaning env leftSyntax
          middle <- meaning env middleSyntax
          domain <- setMeaning env domainSyntax
          let LocatedMath equalityOperator _ = tokens !! equals
              LocatedMath membershipOperator _ = tokens !! member
          pure (PropositionPair (MembershipEquality location equalityOperator left middle domain) (SetExpression location membershipOperator Member middle domain))
    [] -> do
      composition <- compositionMeaning env tokens
      maybe (setSequenceMeaning env tokens) pure composition
    [(position, AtMost)] | isJust (sourceDistanceCandidate env (take position tokens)) || isJust (sourceDistanceCandidate env (finishComparisonOperand env (drop (position + 1) tokens))) -> do
      leftSyntax <- sourceSequence (take position tokens)
      rightSyntax <- sourceSequence (finishComparisonOperand env (drop (position + 1) tokens))
      lhs <- sourceDistance env leftSyntax
      rhs <- sourceDistance env rightSyntax
      selected <- selectPointDomain env leftSyntax rightSyntax lhs rhs
      left <- maybe (meaning env leftSyntax) pure lhs
      right <- maybe (meaning env rightSyntax) pure rhs
      let LocatedMath operator _ = tokens !! position
      case selected of
        DistanceFunction _ kind witness -> pure (PointwiseComparison location operator kind witness left right)
        _ -> Left "Pointwise comparison needs a source distance domain"
    [(position, op)]
      | groups@(_ : _ : _) <- splitPoints (take position tokens) -> do
          unless (op `elem` [Less, Greater, AtMost, AtLeast] && all sourceLetterGroup groups) (Left "Comma comparison requires the reviewed variable-list convention")
          let right = finishComparisonOperand env (drop (position + 1) tokens)
              LocatedMath operator _ = tokens !! position
          rhs <- sourceSequence right >>= meaning env
          values <- traverse (\group -> do lhs <- sourceSequence group >>= meaning env; pure (Derived listedComparison (Compare location operator op lhs rhs))) groups
          pure (Comparisons values)
    [(position, op)]
      | op `elem` [Equal, Unequal]
      , Right rightSyntax <- sourceSequence (finishComparisonOperand env (drop (position + 1) tokens))
      , LocatedMath tupleSpan (LocatedCommand "Tuple" Nothing [LocatedMath _ (LocatedSequence children)]) <- sourceAtom rightSyntax -> do
          lhs <- sourceSequence (take position tokens) >>= meaning env
          let parts = splitPoints (concatMap refine children)
          unless (length parts >= 3) (Left "Repeated tuple needs two points and an ellipsis")
          ending <- sourceSequence (last parts)
          unless (commandIs True "ldots" ending) (Left "Repeated tuple needs a final ellipsis")
          points <- traverse (sourceSequence >=> meaning env) (init parts)
          let LocatedMath operator _ = tokens !! position
          pure (Compare location operator op lhs (RepeatedTuple tupleSpan (SourceSpan (spanStart tupleSpan) (spanStart tupleSpan + 6)) lhs points))
    [(position, op)]
      | op `elem` [Equal, Unequal]
      , let left = take position tokens
            right = finishComparisonOperand env (drop (position + 1) tokens)
      , sourceSetExpression env left && sourceCarrierTokens bindings right || sourceCarrierTokens bindings left && sourceSetExpression env right || isEmptyTokens left || isEmptyTokens right -> do
          leftSyntax <- sourceSequence left
          rightSyntax <- sourceSequence right
          lhs <- setMeaningIn env (Just rightSyntax) leftSyntax
          rhs <- setMeaningIn env (Just leftSyntax) rightSyntax
          let LocatedMath operator _ = tokens !! position
          pure (SetExpression location operator (if op == Equal then EqualSet else UnequalSet) lhs rhs)
    relations -> do
      let boundaries = [-1] <> map fst relations <> [length tokens]
          slices = zipWith (\before after -> take (after - before - 1) (drop (before + 1) tokens)) boundaries (drop 1 boundaries)
      comparisons <- traverse (comparison location tokens (length relations == 1)) (zip3 relations slices (drop 1 slices))
      pure $ case comparisons of [single] -> single; _ -> Comparisons comparisons
 where
  sourceLetterGroup [LocatedMath _ (LocatedText text)] = T.length text == 1 && T.all isAlpha text
  sourceLetterGroup _ = False
  splitPoints = split 0 []
   where
    split :: Int -> [LocatedMath] -> [LocatedMath] -> [[LocatedMath]]
    split _ previous [] = [reverse previous]
    split depth previous (token : rest)
      | depth == 0 && symbol token == "," = reverse previous : split depth [] rest
      | otherwise = split (depth + if symbol token == "(" then 1 else if symbol token == ")" then -1 else 0) (token : previous) rest
  comparison location tokens single ((position, op), left, originalRight) = do
    let right = finishComparisonOperand env originalRight
    let extended values = case trim values of
          LocatedMath source _ : _ -> maybe False ((`elem` ["ENNReal", "ℝ≥0∞"]) . bindingType) (Map.lookup (spanStart source) bindings)
          [] -> False
        useExtended = extended left || extended right
        operand values
          | not single, Just domain <- envNumericDomain env, all numericScalarToken values = numericOperandMeaning env domain values
          | otherwise = case trim values of
              [LocatedMath source (LocatedCommand "infty" Nothing [])] | useExtended -> Right (ExtendedTop source)
              [LocatedMath source (LocatedText number)] | useExtended && not (T.null number) && T.all isDigit number -> Right (Literal source source (InstanceLiteral extendedNumeral) number)
              _ -> sourceSequence values >>= meaning env
    lhs <- operand left
    ordinaryRight <- operand right
    realRight <- if single && realMetricResult bindings left then sourceSequence right >>= realScalarMeaning env else pure Nothing
    let rhs = fromMaybe ordinaryRight realRight
    when (mixedRelation left || mixedRelation right) (Left "Mixed comparisons require an explicit source relation rule")
    let LocatedMath operator _ = tokens !! position
    pure (if isJust realRight then Derived realScalarComparison (Compare location operator op lhs rhs) else Compare location operator op lhs rhs)
  -- Membership chains need their own conjunction rule. Do not reinterpret
  -- x=y\in A as equality between x and a proposition after broadening equality.
  mixedRelation = scan (0 :: Int)
   where
    scan _ [] = False
    scan depth (token@(LocatedMath _ node) : rest) =
      let delta
            | symbol token == "(" = 1
            | symbol token == ")" = -1
            | otherwise = 0
          relation = case node of LocatedCommand name _ _ -> name `elem` ["in", "IncludedIn"]; _ -> False
       in depth == 0 && relation || scan (depth + delta) rest

sourceDistanceCandidate :: MeaningEnv -> [LocatedMath] -> Maybe Expr
sourceDistanceCandidate env tokens = fromRight Nothing (sourceSequence tokens >>= sourceDistance env)

data SourceIdentity
  = SourceReference (Maybe Text) Text ReferenceAdaptation
  | SourceNumeral Text
  | SourceIndex IndexKind SourceIdentity SourceIdentity
  | SourceShift Integer SourceIdentity
  | SourceArithmetic Arithmetic SourceIdentity SourceIdentity
  deriving (Eq, Show)

data CarrierIdentity = StaticCarrier Text | AppliedCarrier SourceIdentity
  deriving (Eq, Show)

expressionIdentity :: Expr -> Maybe SourceIdentity
expressionIdentity expression = case expression of
  Scoped _ body -> expressionIdentity body
  Parenthesized _ body -> expressionIdentity body
  Reference _ identity -> Just (SourceReference (bindingContext identity) (fromMaybe (bindingName identity) (bindingConstant identity)) (bindingAdaptation identity))
  NamedReference _ _ _ identity -> expressionIdentity (Reference (SourceSpan 0 0) identity)
  Literal _ _ InferredLiteral number -> Just (SourceNumeral number)
  Index _ _ kind function index -> SourceIndex kind <$> expressionIdentity function <*> expressionIdentity index
  ShiftIndex _ origin index -> SourceShift origin <$> expressionIdentity index
  Scalar _ _ op left right -> SourceArithmetic op <$> expressionIdentity left <*> expressionIdentity right
  _ -> Nothing

selectPointDomain :: MeaningEnv -> LocatedMath -> LocatedMath -> Maybe Expr -> Maybe Expr -> Either String Expr
selectPointDomain env leftSyntax rightSyntax left right = case (left, right) of
  (Just lhs, Nothing) -> Right lhs
  (Nothing, Just rhs) -> Right rhs
  (Just lhs, Just rhs)
    | Just a <- key lhs, Just b <- key rhs, a == b -> Right lhs
    | originalMetric leftSyntax /= originalMetric rightSyntax -> Right (if originalMetric leftSyntax then rhs else lhs)
    | otherwise -> Left "Different metric domains require an explicit restriction convention"
  _ -> Left "Pointwise comparison needs a source distance domain"
 where
  originalMetric syntax = let LocatedMath location _ = sequenceAtom syntax in maybe False (T.isPrefixOf "MetricSpace " . bindingType) (Map.lookup (spanStart location) (envBindings env))
  key (DistanceFunction _ (BinaryDistance domain) _) = Just (StaticCarrier domain)
  key (DistanceFunction _ (MetricDistance (SourceMetricCarrier domain)) _) = Just (StaticCarrier domain)
  key (DistanceFunction _ (MetricDistance AppliedMetricCarrier) metric) = AppliedCarrier <$> expressionIdentity metric
  key _ = Nothing

sourceSequence :: [LocatedMath] -> Either String LocatedMath
sourceSequence values = do
  location <- spanOf (trim values)
  pure (LocatedMath location (LocatedSequence (trim values)))

setMeaning :: MeaningEnv -> LocatedMath -> Either String Expr
setMeaning env = setMeaningIn env Nothing

setMeaningIn :: MeaningEnv -> Maybe LocatedMath -> LocatedMath -> Either String Expr
setMeaningIn env@MeaningEnv{envConstants = constants, envBindings = bindings} ambient syntax@(LocatedMath location _)
  | Just emptySpan <- emptySourceSpan syntax = do
      witnessSyntax <- maybe (Left "Empty set needs a source set operand to determine its carrier") Right ambient
      when (isJust (emptySourceSpan witnessSyntax)) (Left "Empty set needs a source set operand to determine its carrier")
      witness <- setMeaning env witnessSyntax
      pure (Scoped location (EmptySet emptySpan witness))
  | commandIs True "QQ" syntax
  , maybe False (commandIs True "R") ambient = do
      unless (Map.lookup "R" constants == Just "ℝ" && Map.lookup "QQ" constants == Just "ℚ") (Left "Real/rational embedding requires its registered constants")
      pure (RationalImage location)
  | otherwise = do
      expression <- meaning env syntax
      pure (if sourceCarrierTokens bindings [syntax] then UniversalSet location expression else expression)

commandIs :: Bool -> Text -> LocatedMath -> Bool
commandIs trimWhitespace expected (LocatedMath _ node) = case node of
  LocatedSequence children -> case (if trimWhitespace then trim children else children) of [child] -> commandIs trimWhitespace expected child; _ -> False
  LocatedCommand name Nothing [] -> name == expected
  _ -> False

emptySourceSpan :: LocatedMath -> Maybe SourceSpan
emptySourceSpan (LocatedMath location node) = case node of
  LocatedSequence children -> case trim children of [child] -> emptySourceSpan child; _ -> Nothing
  LocatedCommand "emptyset" Nothing [] -> Just location
  _ -> Nothing

isEmptyTokens :: [LocatedMath] -> Bool
isEmptyTokens tokens = case trim tokens of [child] -> isJust (emptySourceSpan child); _ -> False

-- Carrier recognition uses resolved source types; grouped expressions keep their
-- own grammar rather than acquiring a new carrier interpretation implicitly.
sourceCarrierTokens :: Map.Map Int BindingIdentity -> [LocatedMath] -> Bool
sourceCarrierTokens bindings tokens
  | any ((`elem` ["prod", "ExternalDisjointUnion"]) . shapeName) (sourceFamilies tokens) = True
  | otherwise = case trim tokens of
      [LocatedMath _ (LocatedSequence children)] -> sourceCarrierTokens bindings (concatMap refine children)
      [LocatedMath location node] -> case node of
        LocatedText value | T.length value == 1 -> maybe False (typeCarrier . bindingType) (Map.lookup (spanStart location) bindings)
        LocatedCommand name Nothing [] -> name `elem` ["R", "QQ", "omega", "TwoPointSpace"]
        LocatedScript _ "_" _ -> case Map.lookup (spanStart location) bindings of
          Just identity ->
            let (domain, rest) = T.breakOn "→" (T.replace "->" "→" (bindingType identity))
             in T.strip domain `elem` ["Nat", "ℕ"] && typeCarrier (T.stripStart (T.drop 1 rest))
          Nothing -> False
        _ -> False
      _ -> False
 where
  typeCarrier ty = ty == "Type" || case T.stripPrefix "Type " ty of Just universe -> not (T.null universe) && T.all (not . isSpace) universe; _ -> False

sourceFamilies :: [LocatedMath] -> [FamilyShape]
sourceFamilies tokens = case do
  location <- spanOf tokens
  shapes <- naturalFamilies (locatedValue (LocatedMath location (LocatedSequence tokens)))
  traverse (parseEither familyShape) shapes of
  Right shapes -> filter shapeWhole shapes
  Left _ -> []

setSequenceMeaning :: MeaningEnv -> [LocatedMath] -> Either String Expr
setSequenceMeaning env@MeaningEnv{envBindings = bindings} tokens = case choices of
  [] -> case topLevelCommands "hookrightarrow" tokens of
    [] -> arithmeticMeaning env tokens
    [position] -> do
      let left = take position tokens
          right = drop (position + 1) tokens
      unless (sourceSetExpression env left && sourceSetExpression env right) (Left "Canonical inclusion requires two registered subsets of one ambient type")
      lhs <- sourceSequence left >>= setMeaning env
      rhs <- sourceSequence right >>= setMeaning env
      location <- spanOf tokens
      let LocatedMath operator _ = tokens !! position
      pure (InclusionMap location operator lhs rhs)
    _ -> Left "Inclusion requires one source and target set"
  level -> do
    when (any ((`elem` [Member, Included]) . snd) level && length level /= 1) (Left "Chained set relations require an explicit relation rule")
    let (position, op) = last level
        left = take position tokens
        right = if op `elem` [Member, Included, Intersection] then finishComparisonOperand env (drop (position + 1) tokens) else drop (position + 1) tokens
    when (op == Product && (length level /= 1 || not ((sourceSetExpression env left && (sourceSetExpression env right || sourceCarrierTokens bindings right)) || sourceCarrierTokens bindings left && sourceSetExpression env right))) (Left "Set product requires two registered set operands and explicit grouping")
    lhsSyntax <- sourceSequence left
    rhsSyntax <- sourceSequence right
    lhs <- if op == Member then meaning env lhsSyntax else setMeaningIn env (Just rhsSyntax) lhsSyntax
    rhs <- setMeaningIn env (Just lhsSyntax) rhsSyntax
    location <- spanOf (take (position + 1) tokens <> right)
    let LocatedMath operator _ = tokens !! position
    pure (SetExpression location operator op lhs rhs)
 where
  positions = scan 0 0 tokens
  levels = [[Member, Included], [Union], [Intersection], [Product]]
  choices = maybe [] (\level -> filter ((`elem` level) . snd) positions) (listToMaybe [level | level <- levels, any ((`elem` level) . snd) positions])
  scan :: Int -> Int -> [LocatedMath] -> [(Int, SetOperator)]
  scan _ _ [] = []
  scan depth position (token@(LocatedMath _ node) : rest) =
    let nextDepth = depth + if symbol token == "(" then 1 else if symbol token == ")" then -1 else 0
        found = case node of LocatedCommand name Nothing [] | depth == 0 -> [(position, op) | Just op <- [lookup name [("in", Member), ("IncludedIn", Included), ("cup", Union), ("cap", Intersection), ("times", Product)]]]; _ -> []
     in found <> scan nextDepth (position + 1) rest

finishComparisonOperand :: MeaningEnv -> [LocatedMath] -> [LocatedMath]
finishComparisonOperand env values
  | isJust (envRootSpan env)
  , envRootSpan env == envCurrentSpan env
  , let trimmed = trim values
  , not (null trimmed)
  , symbol (last trimmed) `elem` [".", ","] =
      init trimmed
  | otherwise = values

realMetricResult :: Map.Map Int BindingIdentity -> [LocatedMath] -> Bool
realMetricResult bindings tokens = case trim tokens of
  [LocatedMath _ (LocatedCommand "MetricDiameter" _ _)] -> True
  first : opening : rest | symbol opening == "(", not (null rest), symbol (last rest) == ")" -> isJust (sourceMetric bindings first)
  _ -> False

compositionMeaning :: MeaningEnv -> [LocatedMath] -> Either String (Maybe Expr)
compositionMeaning env@MeaningEnv{envBindings = bindings} tokens = case topLevelCommands "circ" tokens of
  [] -> Right Nothing
  [position] -> do
    left <- sourceSequence (take position tokens)
    right <- sourceSequence (drop (position + 1) tokens)
    candidateDistance <- sourceDistance env right
    let LocatedMath source _ = sequenceAtom left
        outerType = bindingType <$> Map.lookup (spanStart source) bindings
        distance = case candidateDistance of Just (DistanceFunction _ (BinaryDistance _) _) | outerType /= Just "ℝ → ℝ" -> Nothing; _ -> candidateDistance
    inner <- maybe (meaning env right) pure distance
    outer <- meaning env left
    location <- spanOf tokens
    let LocatedMath operator _ = tokens !! position
    pure (Just (Composition location operator outer inner))
  _ -> Left "Composition chains require explicit grouping"

topLevelCommands :: Text -> [LocatedMath] -> [Int]
topLevelCommands name = scan 0 0
 where
  scan :: Int -> Int -> [LocatedMath] -> [Int]
  scan _ _ [] = []
  scan depth position (token@(LocatedMath _ node) : rest) =
    let nextDepth = depth + if symbol token == "(" then 1 else if symbol token == ")" then -1 else 0
        selected = case node of LocatedCommand command Nothing [] -> depth == 0 && command == name; _ -> False
     in [position | selected] <> scan nextDepth (position + 1) rest

comparisonChoices :: [LocatedMath] -> [(Int, Comparison)]
comparisonChoices = go 0 0
 where
  go :: Int -> Int -> [LocatedMath] -> [(Int, Comparison)]
  go _ _ [] = []
  go depth position (token@(LocatedMath _ node) : rest) =
    let nextDepth = depth + if symbol token == "(" then 1 else if symbol token == ")" then -1 else 0
        relation = case node of
          LocatedText value -> lookup value [("=", Equal), ("<", Less), (">", Greater)]
          LocatedCommand name Nothing [] -> lookup name [("le", AtMost), ("ge", AtLeast), ("ne", Unequal)]
          _ -> Nothing
     in [(position, op) | depth == 0, Just op <- [relation]] <> go nextDepth (position + 1) rest

arithmeticMeaning :: MeaningEnv -> [LocatedMath] -> Either String Expr
arithmeticMeaning env tokens = do
  location <- spanOf tokens
  case arithmeticChoice tokens of
    Just (position, op) -> do
      let (left, tailTokens) = splitAt position tokens
      case tailTokens of
        LocatedMath operator _ : right -> do
          lhs <- operand left
          rhs <- operand right
          pure (Scalar location operator op lhs rhs)
        [] -> Left "Missing arithmetic operator"
    Nothing -> case tokens of
      LocatedMath operator (LocatedText "-") : rest -> Negate location operator <$> operand rest
      [single] -> meaning env single
      first : rest | symbol first == "(", not (null rest), symbol (last rest) == ")", enclosesTokens tokens -> Parenthesized location <$> operand (init rest)
      _
        | not (null tokens)
        , all (\t -> T.length (symbol t) == 1 && T.all isDigit (symbol t)) tokens ->
            Right (Literal location location InferredLiteral (T.concat (map symbol tokens)))
      _ -> applicationMeaning env tokens
 where
  operand values = do
    location <- spanOf (trim values)
    Scoped location <$> sequenceMeaning env values

arithmeticChoice :: [LocatedMath] -> Maybe (Int, Arithmetic)
arithmeticChoice tokens =
  let choices = arithmeticChoices tokens
   in listToMaybe (reverse [c | c@(_, op) <- choices, op `elem` [Add, Subtract]]) <|> listToMaybe (reverse choices)

enclosesTokens :: [LocatedMath] -> Bool
enclosesTokens values = all (> 0) (init (scanl (\depth t -> depth + delta t) 1 (drop 1 values))) && sum (map delta values) == 0
 where
  delta t
    | symbol t == "(" = 1
    | symbol t == ")" = -1
    | otherwise = 0

-- A source application has an explicitly resolved callee and a parenthesized,
-- nonempty argument list. Subtype/metric adapters have separate meaning rules.
applicationMeaning :: MeaningEnv -> [LocatedMath] -> Either String Expr
applicationMeaning env@MeaningEnv{envBindings = bindings} raw = case tokens of
  power@(LocatedMath powerSpan (LocatedScript (LocatedMath _ (LocatedText base)) "^" _)) : metric@(LocatedMath metricSpan _) : opening : _
    | not (T.null base)
    , T.all isDigit base
    , symbol opening == "("
    , Just identity <- Map.lookup (spanStart metricSpan) bindings
    , isJust (metricCarrier identity metric) -> do
        lhs <- meaning env power
        rhs <- sourceSequence (drop 1 tokens) >>= meaning env
        location <- spanOf tokens
        pure (ImplicitMultiply location (SourceSpan (spanEnd powerSpan) (spanEnd powerSpan)) lhs rhs)
  function@(LocatedMath functionSpan _) : opening : rest | symbol opening == "(" -> do
    identity <- maybe (Left "Application needs a resolved source callee") Right (Map.lookup (spanStart functionSpan) bindings)
    let ty = bindingType identity
    width <- maybe (Left "Missing function source span") Right (bindingSourceWidth identity)
    groups <- splitArguments 1 [] [] rest
    arguments <- traverse operand groups
    callee <- meaning env function
    location <- spanOf tokens
    let operator = SourceSpan (spanStart functionSpan) (spanStart functionSpan + width)
    case metricCarrier identity function of
      Just carrier -> case (groups, arguments) of
        ([_, rightSource], [left, right]) -> do
          let evaluation = if sourceSetExpression env rightSource then SetDistance else PointDistance
          pure (MetricApplication location operator carrier evaluation (envBranchProof env) callee left right)
        _ -> Left "Metric evaluation requires two points or a point and a set"
      Nothing -> do
        unless ("→" `T.isInfixOf` ty || "->" `T.isInfixOf` ty || "∀" `T.isPrefixOf` ty) (Left "Application requires a function binder")
        when ("MetricSpace " `T.isInfixOf` ty) (Left "Metric families require their source-domain adapter")
        case (groups, arguments) of
          ([source], [argument])
            | Just target <- sourceArgumentBinding bindings source
            , sourceSetExpression env source
            , "Set " `T.isPrefixOf` bindingType target
            , Just remainingType <- T.stripPrefix ("↑" <> bindingName target) ty
            , any (`T.isPrefixOf` T.stripStart remainingType) ["→", "->"] ->
                pure (SubtypeRange location operator (bindingName target) callee argument)
            | "↑" `T.isPrefixOf` ty -> pure (SubtypeApplication location operator identity callee argument)
          _ -> pure (Application location operator identity callee arguments)
  _ | any ((== ",") . symbol) tokens -> Left "Comma syntax needs a reviewed tuple, application or list rule"
  _ -> Left "Sequence needs construction recognition"
 where
  tokens = case filter (not . blank) raw of
    power@(LocatedMath _ (LocatedScript (LocatedMath _ (LocatedText base)) "^" _)) : metric : _
      | not (T.null base), T.all isDigit base, sourceMetricCandidate metric -> power : drop 1 (filter (not . blank) raw)
    metric : _ | sourceMetricCandidate metric -> filter (not . blank) raw
    _ -> raw
  sourceMetricCandidate syntax@(LocatedMath source _) = maybe False (\identity -> isJust (metricCarrier identity syntax)) (Map.lookup (spanStart source) bindings)
  operand values = do
    location <- spanOf (trim values)
    Scoped location <$> sequenceMeaning env values
  splitArguments :: Int -> [LocatedMath] -> [[LocatedMath]] -> [LocatedMath] -> Either String [[LocatedMath]]
  splitArguments _ _ _ [] = Left "Unclosed or empty function application"
  splitArguments depth current previous (token : rest)
    | symbol token == ")"
    , depth == 1 = do
        unless (null rest && not (null current)) (Left "Unclosed, empty or adjacent function application")
        pure (reverse (reverse current : previous))
    | symbol token == ","
    , depth == 1 = do
        when (null current) (Left "Empty function application argument")
        splitArguments depth [] (reverse current : previous) rest
    | otherwise =
        let nextDepth = depth + if symbol token == "(" then 1 else if symbol token == ")" then -1 else 0
         in splitArguments nextDepth (token : current) previous rest

sourceArgumentBinding :: Map.Map Int BindingIdentity -> [LocatedMath] -> Maybe BindingIdentity
sourceArgumentBinding bindings tokens = case trim tokens of
  [LocatedMath location _] -> Map.lookup (spanStart location) bindings
  _ -> Nothing

metricCarrier :: BindingIdentity -> LocatedMath -> Maybe MetricDomain
metricCarrier identity (LocatedMath location node) = case node of
  LocatedScript _ "_" _ | any (`T.isInfixOf` ty) ["→ MetricSpace ", "-> MetricSpace ", ", MetricSpace "] -> Just AppliedMetricCarrier
  LocatedScript{} -> Nothing
  _ | bindingSourceWidth identity == Just (spanEnd location - spanStart location), Just carrier <- T.stripPrefix "MetricSpace " ty -> Just (SourceMetricCarrier carrier)
  _ -> Nothing
 where
  ty = bindingType identity

-- This mirrors the source grammar's set classification, rather than asking the
-- elaborated application which overload it selected. Unported syntax still fails
-- semantic construction and is not silently accepted by this predicate.
sourceSetExpression :: MeaningEnv -> [LocatedMath] -> Bool
sourceSetExpression env@MeaningEnv{envBindings = bindings, envConstructed = constructed} tokens
  | shape : _ <- sourceFamilies tokens
  , shapeName shape `elem` ["bigcap", "bigcup"] = case shapeCarrierOffset shape of
      Just offset -> maybe False (typeCarrier . bindingType) (Map.lookup offset bindings)
      Nothing -> maybe False (naturalSet . bindingType) (shapeFamilyOffset shape >>= (`Map.lookup` bindings))
  | otherwise = case trim tokens of
      [LocatedMath _ (LocatedGroup body)] -> sourceSetExpression env [body]
      [LocatedMath _ (LocatedSequence children)] -> sourceSetExpression env (concatMap refine children)
      [LocatedMath location node] -> case node of
        LocatedText _ -> referenceSet location
        LocatedRaw _ -> referenceSet location || maybe False (setResult . snd) (Map.lookup (spanStart location) constructed)
        LocatedScript _ "_" _ -> case Map.lookup (spanStart location) bindings of
          Just identity ->
            let (domain, tailType) = T.breakOn "→" (T.replace "->" "→" (bindingType identity))
                result = T.stripStart (T.drop 1 tailType)
             in T.strip domain `elem` ["Nat", "ℕ"] && "Set " `T.isPrefixOf` result && not (T.null (T.drop 4 result))
          Nothing -> False
        LocatedCommand name Nothing arguments -> (name, length arguments) `elem` [("MetricBall", 3), ("Closure", 1), ("SetDifference", 2), ("Ball", 2), ("AmbientClosure", 2), ("ClosedInterval", 2), ("OpenInterval", 2), ("LeftClosedInterval", 2)]
        _ -> False
      _ -> False
 where
  setResult expression = case expression of
    Scoped _ body -> setResult body
    Parenthesized _ body -> setResult body
    SetComprehension{} -> True
    ImageSet{} -> True
    IndexedSet{} -> True
    _ -> False
  referenceSet location = case Map.lookup (spanStart location) bindings of
    Just identity -> "Set " `T.isPrefixOf` bindingType identity && bindingSourceWidth identity == Just (spanEnd location - spanStart location)
    Nothing -> False
  typeCarrier ty = ty == "Type" || "Type " `T.isPrefixOf` ty
  naturalSet ty = let (domain, target) = T.breakOn "→" (T.replace "->" "→" ty) in T.strip domain `elem` ["Nat", "ℕ"] && "Set " `T.isPrefixOf` T.stripStart (T.drop 1 target)

arithmeticChoices :: [LocatedMath] -> [(Int, Arithmetic)]
arithmeticChoices = go 0 Nothing 0
 where
  go :: Int -> Maybe Text -> Int -> [LocatedMath] -> [(Int, Arithmetic)]
  go _ _ _ [] = []
  go depth previous position (token : rest) =
    let text = symbol token
        following = if blank token then previous else Just (if T.null text then "operand" else text)
        nextDepth = depth + if text == "(" then 1 else if text == ")" then -1 else 0
        current = case lookup text [("+", Add), ("-", Subtract), ("*", Multiply), ("/", Divide)] of
          Just op | depth == 0, Just before <- previous, before `notElem` ["+", "-", "*", "/", "(", ","] -> [(position, op)]
          _ -> []
     in current <> go nextDepth following (position + 1) rest

translationRequest :: Value -> Parser Value
translationRequest = withObject "semantic translation batch" $ \fields -> do
  jobs <- fields .: "expressions" :: Parser [Object]
  environment <- fields .:? "environment" .!= KM.empty
  constants <- environment .:? "constants" .!= Map.empty
  conventions <- environment .:? "conventions" .!= Map.empty
  occupied <- environment .:? "occupied" .!= []
  sourceRecords <- environment .:? "records" .!= Map.empty
  records <- traverse sourceBinders sourceRecords
  bridgeRecords <- environment .:? "bridgeRecords" .!= toJSON (sourceRecords :: Map.Map Text Value)
  resolveContext <- environment .:? "resolveContext" .!= False
  standalone <- environment .:? "standalone" .!= False
  includeAST <- environment .:? "includeAST" .!= False
  results <- mapM (translateJob (constants, conventions, occupied, records, bridgeRecords, resolveContext, standalone, includeAST)) jobs
  pure (object ["results" .= results])
 where
  translateJob (sharedConstants, sharedConventions, sharedOccupied, sharedRecords, bridgeRecords, resolveContext, sharedStandalone, includeAST) fields = do
    tree <- fields .: "tree"
    variables <- fields .: "variables" :: Parser [Value]
    constants <- fields .:? "constants" .!= sharedConstants
    conventions <- fields .:? "conventions" .!= sharedConventions
    root <- fields .:? "root" .!= True
    standalone <- fields .:? "standalone" .!= sharedStandalone
    occupied <- fields .:? "occupied" .!= sharedOccupied
    initial <- fields .:? "firstMarker" .!= 0
    jobRecords <- fields .:? "records"
    records <- maybe (pure sharedRecords) (traverse sourceBinders) jobRecords
    when (initial < 0) (fail "Negative marker offset")
    let build = do
          let offsets = parseEither (mapM binding) variables
          resolved <- offsets
          unless (length resolved == Map.size (Map.fromList resolved)) (Left "Duplicate variable source offsets")
          expression <- annotatedMeaning (MeaningEnv constants (Map.fromList resolved) conventions Map.empty Nothing Nothing occupied Nothing records Nothing) root tree
          when (standalone && null (expressionContexts expression) && untypedNumeric expression) (Left "Standalone numeric expression has no reviewed ambient number type.")
          context <- if resolveContext then parseEither contextBridgeRequest (object ["names" .= expressionContexts expression, "records" .= bridgeRecords]) else Right Null
          pure (expression, context)
    pure $ case build of
      Left reason -> object ["supported" .= False, "reason" .= reason]
      Right (expression, context) ->
        object $
          [ "supported" .= True
          , "contexts" .= expressionContexts expression
          , "rendering" .= renderedValue (renderPair occupied initial (candidate expression))
          ]
            <> ["context" .= (case context of Object values -> KM.lookup "context" values; _ -> Nothing) | resolveContext]
            <> ["semanticAST" .= semanticValue expression | includeAST]

-- Numerals used as operands receive their type from the surrounding source
-- operation. A standalone arithmetic expression needs its own source witness.
untypedNumeric :: Expr -> Bool
untypedNumeric expression = case expression of
  Literal _ _ InferredLiteral _ -> True
  Scoped _ body -> untypedNumeric body
  Parenthesized _ body -> untypedNumeric body
  Scalar _ _ _ left right -> untypedNumeric left && untypedNumeric right
  Negate _ _ body -> untypedNumeric body
  Compare _ _ Equal left right -> untypedNumeric left && untypedNumeric right
  _ -> False

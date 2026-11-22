{-# LANGUAGE OverloadedStrings #-}

{- | Resolve explicit source-owned bindings against actual Lean telescope records.
Local lexical binding and interpretation approval are separate stages.
-}
module VariableResolution (outerResolutionRequest, lexicalResolutionRequest, domainResolutionRequest, resolutionRequest) where

import Control.Monad (foldM)
import Data.Aeson (Value (..), object, withObject, (.:), (.=))
import qualified Data.Aeson.Key as K
import qualified Data.Aeson.KeyMap as KM
import Data.Aeson.Types (Parser)
import Data.Char (isSpace)
import Data.Foldable (toList)
import Data.List (sortOn)
import Data.Maybe (catMaybes, fromMaybe)
import Data.Ord (Down (..))
import Data.Text (Text)
import qualified Data.Text as T

field :: Text -> Value -> Value
field key (Object fields) = fromMaybe Null (KM.lookup (K.fromText key) fields)
field _ _ = Null

has :: Text -> Value -> Bool
has key (Object fields) = KM.member (K.fromText key) fields
has _ _ = False

label :: Text -> Value -> Text
label key value = case field key value of String result -> result; _ -> ""

values :: Value -> [Value]
values (Array array) = toList array
values (Object fields) = KM.elems fields
values _ = []

patch :: Value -> [(Text, Value)] -> Value
patch (Object fields) changes = Object (foldr (uncurry (KM.insert . K.fromText)) fields changes)
patch value _ = value

resolved :: Value -> [(Text, Value)] -> Value
resolved original changes = case patch original (("status", String "resolved") : changes) of
  Object fields -> Object (KM.delete "reason" fields)
  other -> other

unresolved :: Value -> Text -> Value
unresolved value reason = patch value [("status", String "unresolved"), ("reason", String reason)]

number :: Int -> Value
number = Number . fromIntegral

position :: Text -> Value -> Parser Int
position key = withObject "source position" (.: K.fromText key)

outerResolutionRequest :: Value -> Parser Value
outerResolutionRequest = withObject "outer variable resolution" $ \fields -> do
  variables <- fields .: "variables" :: Parser [Value]
  scopes <- fields .: "scopes" :: Parser [Value]
  row <- fields .: "row"
  records <- fields .: "records"
  offset <- position "bodyStart" row
  rowStart <- position "start" row
  candidates <- mapM (\scope -> do a <- position "start" scope; b <- position "end" scope; pure (a, b, scope)) scopes
  let active = [scope | (a, b, scope) <- sortOn (Down . first) candidates, a <= rowStart && rowStart < b]
      first (a, _, _) = a
  results <- mapM (resolve offset active records) variables
  pure (object ["variables" .= results])
 where
  resolve offset active records variable = do
    begin <- position "start" variable
    end <- position "end" variable
    let initial = unresolved (patch variable [("start", number (offset + begin)), ("end", number (offset + end)), ("formulaOffset", number begin)]) "No Markdown-owned declaration in this scope."
    select offset records active initial
  select _ _ [] variable = pure variable
  select offset records (scope : rest) variable = do
    let occurrence
          | field "superscriptBase" variable == Bool True = "superscript-base"
          | field "subscriptBase" variable == Bool True = "subscript-base"
          | otherwise = "unsubscripted"
        selector binding = if has "occurrence" binding then label "occurrence" binding else "any"
        bindings = values (field "bindings" scope)
        matches = [b | b <- bindings, field "symbol" b == field "symbol" variable, selector b `elem` ["any", occurrence]]
        named = field "numericSubscriptName" variable
        namedMatches = [b | named /= Null, b <- bindings, field "symbol" b == field "symbol" named, selector b == "any"]
    prepared <-
      if null namedMatches
        then pure variable
        else do
          end <- position "end" named
          pure (patch variable [("symbol", field "symbol" named), ("end", number (offset + end)), ("namedSubscript", Bool True)])
    case if null namedMatches then matches else namedMatches of
      [] -> select offset records rest prepared
      binding : _ -> do
        let attributes = [(key, field key binding) | key <- ["indexOrigin", "indexOffset", "projection"], has key binding]
            identified = patch prepared (attributes <> [("occurrenceSelector", String (selector binding)), ("id", field "id" binding), ("scope", field "scope" scope), ("scopeStart", field "start" scope), ("scopeEnd", field "end" scope)])
            (prefix, name) = T.breakOnEnd "/" (label "target" binding)
            declaration = T.dropEnd 1 prefix
            record = field declaration records
        if has "reason" binding
          then pure (patch identified [("reason", field "reason" binding)])
          else
            if T.null prefix
              then fail "A source binding requires a qualified target"
              else
                if name == "@constant"
                  then
                    pure $
                      if has "indexOffset" identified || has "projection" identified
                        then unresolved identified "Shifted source indices require a natural-number binder."
                        else
                          if not (has "declarationType" record)
                            then unresolved identified ("Missing Lean constant evidence: " <> declaration)
                            else resolved identified [("declaration", Null), ("constantDeclaration", String declaration), ("leanName", String declaration), ("leanType", field "declarationType" record)]
                  else pure $ case [(slot, binder) | (slot, binder) <- zip [0 :: Int ..] (values (field "binders" record)), label "name" binder == name] of
                    [(slot, binder)] ->
                      let matched = resolved identified [("declaration", String declaration), ("leanName", String name), ("argumentPosition", number slot), ("leanType", field "type" binder)]
                          domains = [T.drop 4 (label "type" b) | b <- values (field "binders" record), Just subset <- [T.stripPrefix "↑" (label "leanType" matched)], label "name" b == subset, "Set " `T.isPrefixOf` label "type" b]
                          projected =
                            if not (has "projection" matched)
                              then matched
                              else case domains of
                                [domain] -> patch matched [("sourceLeanType", field "leanType" matched), ("leanType", String domain)]
                                _ -> unresolved matched "Subtype projection needs an original binder in a named subset."
                       in if has "indexOffset" projected && label "leanType" projected `notElem` ["ℕ", "Nat"] then unresolved projected "Shifted source indices require a natural-number binder." else projected
                    _ -> unresolved identified ("Missing or ambiguous Lean binder: " <> label "target" binding)

-- Local bindings supersede outer candidates, with source-stable hygienic names.
lexicalResolutionRequest :: Value -> Parser Value
lexicalResolutionRequest = withObject "local variable resolution" $ \fields -> do
  variables <- fields .: "variables" :: Parser [Value]
  effects <- fields .: "effects" :: Parser [Value]
  row <- fields .: "row"
  records <- fields .: "records"
  base <- position "bodyStart" row
  let occupied = [label "name" b | record <- values records, b <- values (field "binders" record)]
  (reversed, updated) <- foldM (resolve base row occupied) ([], effects) variables
  pure (object ["variables" .= reverse reversed, "effects" .= updated])
 where
  clean keys (Object fields) = Object (foldr (KM.delete . K.fromText) fields keys)
  clean _ value = value
  resolve base row occupied (previous, effects) variable = do
    relative <- position "formulaOffset" variable
    (bound, updated) <-
      if not (all (has "binder") effects)
        then pure (unresolved variable "Formula has an unreviewed binding effect; outer binding is only a candidate.", effects)
        else do
          candidates <- mapM (eligible relative variable) (zip [0 :: Int ..] effects)
          case catMaybes candidates of
            [] -> pure (variable, effects)
            first : rest -> do
              let selected = foldl (\best@(_, _, a) current@(_, _, b) -> if b > a then current else best) first rest
              bind base row occupied relative selected variable effects
    let ty = label "leanType" bound
        checked =
          if field "subscriptBase" bound == Bool True
            && field "namedSubscript" bound /= Bool True
            && label "status" bound == "resolved"
            && not ("→" `T.isInfixOf` ty || "->" `T.isInfixOf` ty || "∀" `T.isPrefixOf` ty)
            then unresolved bound "Indexed family must not resolve to a scalar or point binder."
            else bound
    pure (checked : previous, updated)
  eligible relative variable (slot, effect) = do
    begin <- position "start" effect
    end <- position "end" effect
    let binder = field "binder" effect
    allowed <-
      if label "command" effect /= "natural-sum"
        then pure True
        else do
          declaration <- position "declarationOffset" binder
          body <- position "bodyStart" binder
          pure (relative == declaration || relative >= body)
    pure $ if begin <= relative && relative < end && field "symbol" binder == field "symbol" variable && allowed then Just (slot, effect, begin) else Nothing
  bind base row occupied relative (slot, effect, begin) variable effects = do
    index <- position "index" row
    end <- position "end" effect
    let original = field "binder" effect
        command = label "command" effect
    declaration <- position "declarationOffset" original
    let inferred =
          if command `elem` ["mapsto", "predicate-set"]
            && relative == declaration
            && label "status" variable == "resolved"
            && not (T.null (label "declaration" variable))
            && not (has "domainOffset" original)
            then patch original [("leanType", field "leanType" variable), ("sourceContext", field "declaration" variable), ("sourceName", field "leanName" variable)]
            else original
    discriminator <- if has "nameDiscriminator" inferred then do value <- position "nameDiscriminator" inferred; pure (Just value) else pure Nothing
    let decimal = T.pack . show
        identity = "formula-" <> decimal index <> "/sequence-" <> decimal begin <> maybe "" (\value -> "/binder-" <> decimal value) discriminator
        initialName = "seq_index_" <> decimal (base + begin) <> maybe "" (("_" <>) . decimal) discriminator
        fresh name = if name `elem` occupied then fresh (name <> "_") else name
        ty = if has "leanType" inferred then field "leanType" inferred else String "unresolved"
        local =
          patch
            variable
            ( [ ("status", String "resolved")
              , ("id", String identity)
              , ("scope", String identity)
              , ("scopeStart", number (base + begin))
              , ("scopeEnd", number (base + end))
              , ("declaration", Null)
              , ("leanName", String (fresh initialName))
              , ("leanType", ty)
              , ("localBinder", Bool True)
              ]
                <> [("binderRole", String command) | "ball-generator-" `T.isPrefixOf` command]
            )
        contextual
          | command `notElem` ["mapsto", "predicate-set"] = local
          | has "sourceContext" inferred = patch local [("binderContext", field "sourceContext" inferred)]
          | has "domainOffset" inferred = local
          | otherwise = unresolved local (command <> " binder requires a source-owned Lean domain mapping.")
        cleared = clean (["argumentPosition", "constantDeclaration", "indexOrigin", "indexOffset", "projection", "sourceLeanType"] <> ["reason" | label "status" contextual == "resolved"]) contextual
        shifted = case field "indexOffset" inferred of
          Null -> cleared
          Number 0 -> cleared
          value -> patch cleared [("indexOffset", value)]
        updated = [if position' == slot then patch e [("binder", inferred)] else e | (position', e) <- zip [0 ..] effects]
    pure (shifted, updated)

-- Domain checks operate after local shadowing. Each pass sees preceding updates,
-- matching the source-order dependency of carrier/family witnesses.
domainResolutionRequest :: Value -> Parser Value
domainResolutionRequest = withObject "variable domain checks" $ \fields -> do
  variables <- fields .: "variables" :: Parser [Value]
  effects <- fields .: "effects" :: Parser [Value]
  row <- fields .: "row"
  base <- position "bodyStart" row
  result <- foldM (check base) variables effects
  pure (object ["variables" .= result])
 where
  known value = label "status" value == "resolved"
  local scope variable = field "localBinder" variable == Bool True && field "scopeStart" variable == number scope
  check base variables effect = do
    begin <- position "start" effect
    let scope = base + begin
        binder = field "binder" effect
        command = label "command" effect
        lookupOffset value = fromMaybe Null (lookup value [(field "formulaOffset" v, v) | v <- reverse variables])
        domain key = lookupOffset (field key binder)
        update predicate transform = map (\v -> if predicate v then transform v else v) variables
        updateLocal = update (local scope)
        reject reason = updateLocal (`unresolved` reason)
        carrier = domain "domainOffset"
        isType value = known value && "Type" `T.isPrefixOf` label "leanType" value
        isSet value = known value && "Set " `T.isPrefixOf` label "leanType" value
        inherit ty = patchForCarrier ty carrier
        patchForCarrier ty value variable = patch variable [("leanType", ty), ("binderContext", field "declaration" value)]
    if "ball-generator-" `T.isPrefixOf` command
      then
        pure $
          update
            (\v -> field "binderRole" v == String command && field "scopeStart" v == number scope)
            (if isType carrier then inherit (if "point" `T.isSuffixOf` command then field "leanName" carrier else String "ℝ") else (`unresolved` "Ball generator requires a resolved point carrier."))
      else
        if command == "predicate-set" && has "domainOffset" binder
          then
            pure $
              if isType carrier then updateLocal (inherit (field "leanName" carrier)) else reject "Explicit set generator needs a resolved carrier type."
          else
            if command == "typed-map"
              then
                pure $
                  if isSet carrier then updateLocal (inherit (String ("Subtype «" <> label "leanName" carrier <> "»"))) else reject "Typed map requires a registered source subset."
              else
                if command `elem` ["natural-type-family", "natural-set-family"]
                  then
                    if has "carrierOffset" binder
                      then
                        pure $
                          if isType (domain "carrierOffset") then variables else reject "Indexed predicate set needs a resolved carrier type."
                      else do
                        let offsets = if has "familyOffsets" binder then values (field "familyOffsets" binder) else [field "familyOffset" binder]
                            familyValid offset = let value = lookupOffset offset in known value && naturalArrow (command == "natural-set-family") (field "setCarrierAllowed" effect == Bool True) (label "leanType" value)
                            typed variable = patch variable ([("leanType", String "ℕ")] <> [("indexLowerBound", field "lowerBound" binder) | has "lowerBound" binder])
                        pure $ if all familyValid offsets then updateLocal typed else reject "Indexed construction requires a registered Nat-indexed family of the appropriate kind."
                  else
                    if command == "bounded-infimum"
                      then
                        pure $
                          if isSet carrier then updateLocal (\v -> patch v [("leanType", String (T.drop 4 (label "leanType" carrier)))]) else reject "Infimum binder requires a resolved set domain."
                      else
                        if command /= "sequence-limit" || not (has "binder" effect)
                          then pure variables
                          else do
                            let families = map lookupOffset (values (field "familyOffsets" binder))
                                valid value = known value && T.strip (fst (T.breakOn "→" (label "leanType" value))) `elem` ["ℕ", "Nat"]
                            if not (all valid families)
                              then pure (reject "Convergence requires natural-number-indexed families.")
                              else do
                                origins <- mapM (\v -> if has "indexOrigin" v then position "indexOrigin" v else pure 0) families
                                let origin = maximum (0 : origins)
                                pure $ if origin == 0 then variables else updateLocal (\v -> patch v [("indexOffset", number origin)])
  naturalArrow setFamily allowSet ty = case T.stripPrefix "Nat" ty `orElse` T.stripPrefix "ℕ" ty of
    Nothing -> False
    Just suffix -> case T.stripPrefix "→" (dropSpace suffix) `orElse` T.stripPrefix "->" (dropSpace suffix) of
      Nothing -> False
      Just after -> let codomain = dropSpace after in if setFamily then setType codomain else universe codomain || allowSet && setType codomain
  dropSpace = T.dropWhile whitespace
  whitespace char = isSpace char || char `elem` ['\x1c', '\x1d', '\x1e', '\x1f']
  setType value = case T.stripPrefix "Set " value of Just body -> not (T.null body) && not ("\n" `T.isInfixOf` body); Nothing -> False
  universe value = value == "Type" || case T.stripPrefix "Type " value of Just level -> not (T.null level) && not (T.any whitespace level); Nothing -> False
  orElse (Just value) _ = Just value
  orElse Nothing other = other

-- One transport transaction for the complete variable-resolution pipeline.
resolutionRequest :: Value -> Parser Value
resolutionRequest value =
  withObject
    "variable resolution"
    ( \fields -> do
        outer <- outerResolutionRequest value >>= withObject "outer result" (.: "variables")
        lexical <- lexicalResolutionRequest (Object (KM.insert "variables" outer fields))
        withObject
          "lexical result"
          ( \result -> do
              variables <- result .: "variables"
              effects <- result .: "effects"
              domainResolutionRequest (Object (KM.insert "variables" variables (KM.insert "effects" effects fields)))
                >>= withObject
                  "checked variables"
                  ( \checked -> do
                      final <- checked .: "variables" :: Parser Value
                      pure (object ["variables" .= final, "effects" .= (effects :: Value)])
                  )
          )
          lexical
    )
    value

{-# LANGUAGE OverloadedStrings #-}

module OperatorProbe (probeRequest, preludeRequest) where

import Data.Aeson (Object, Value (..), object, withObject, (.!=), (.:), (.:?), (.=))
import qualified Data.Aeson.KeyMap as KM
import Data.Aeson.Types (Parser)
import Data.Text (Text)
import qualified Data.Text as T
import ProbeTemplates
import ProofContexts (definitionRequest, quote)

preludeRequest :: Text -> Value -> Parser Value
preludeRequest action = withObject "probe prelude request" $ \fields -> do
  source <- case action of
    "metricPrelude" -> pure metricPrelude
    "operatorLean" -> pure operatorPrelude
    "operatorHeader" -> do
      imports <- fields .: "imports"
      opens <- fields .: "opens"
      pure (imports <> opens <> "set_option autoImplicit false\nset_option linter.unusedVariables false\n" <> metricPrelude <> operatorPrelude)
    _ -> fail "Unknown probe prelude"
  pure (object ["source" .= source])

expectation :: Object -> Parser Text
expectation mapping = do
  marker <- mapping .: "marker"
  operands <- mapping .: "expectedOperands" :: Parser [Object]
  implicit <- mapping .: "expectedImplicitArguments" :: Parser [Object]
  callee <- mapping .:? "expectedCallee" .!= ""
  arguments <- mapM (fmap (quote False) . (.: "candidate")) operands
  implicitArgs <-
    mapM
      ( \o -> do
          position <- o .: "argumentPosition" :: Parser Int
          term <- o .: "candidate"
          pure ("(" <> T.pack (show position) <> ", " <> quote False term <> ")")
      )
      implicit
  pure ("(" <> quote True marker <> ", #[" <> T.intercalate ", " arguments <> "], #[" <> T.intercalate ", " implicitArgs <> "], " <> quote False callee <> ")")

probeRequest :: Value -> Parser Value
probeRequest = withObject "operator probe" $ \fields -> do
  mappings <- fields .: "mappings" :: Parser [Object]
  suffix <- fields .: "suffix" :: Parser Text
  reference <- fields .: "reference" >>= definitionRequest >>= withObject "definition" (.: "source")
  expression <- fields .: "expression" >>= definitionRequest >>= withObject "definition" (.: "source")
  expected <- mapM expectation mappings
  let expressionName = "OperatorProbe.expression" <> suffix
      referenceName = "OperatorProbe.reference" <> suffix
      expectationsName = "operandExpectations" <> suffix
      template =
        T.replace
          "\"operators\""
          ("\"operators" <> suffix <> "\"")
          (T.replace "operandExpectations" expectationsName (T.replace "OperatorProbe.reference" referenceName (T.replace "OperatorProbe.expression" expressionName probeTemplate)))
      source = reference <> expression <> "def " <> expectationsName <> " : Array (String × Array String × Array (Nat × String) × String) := #[" <> T.intercalate ", " expected <> "]\n" <> template
  consumers <- mapM (consumer suffix) mappings
  pure (object ["mappings" .= map fst consumers, "source" .= (source <> T.concat (map snd consumers))])
 where
  consumer suffix mapping = case KM.lookup "consumer" mapping of
    Nothing -> pure (mapping, "")
    Just value ->
      withObject
        "literal consumer"
        ( \info -> do
            marker <- mapping .: "marker"
            candidate <- mapping .: "candidate"
            declaration <- info .: "declaration"
            callee <- info .: "callee"
            position <- info .: "argumentPosition" :: Parser Int
            let key = "consumer" <> suffix <> "_" <> marker
                command =
                  "\nrun_cmd liftTermElabM do\n  let evidence ← checkConsumerArgument ``"
                    <> declaration
                    <> " ``"
                    <> callee
                    <> " "
                    <> T.pack (show position)
                    <> " "
                    <> quote False candidate
                    <> "\n"
                    <> "  logInfo m!\"BOOK_LEAN_EXPORT {(Json.mkObj [(\"declaration\", toJson "
                    <> quote True key
                    <> "), (\"evidence\", evidence)]).compress}\"\n"
            pure (KM.insert "consumerKey" (String key) mapping, command)
        )
        value

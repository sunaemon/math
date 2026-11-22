{-# LANGUAGE OverloadedStrings #-}

{- | Aeson owns JSON syntax/value decoding. This second lexical pass preserves
duplicate-key rejection and the integer-token contracts of source metadata.
-}
module SourceJSON (decodeSourceJSON) where

import Control.Monad (unless, when)
import Data.Aeson (Value, eitherDecodeStrict')
import Data.Char (isDigit)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE

decodeSourceJSON :: Text -> Either String Value
decodeSourceJSON source = do
  decoded <- eitherDecodeStrict' (TE.encodeUtf8 source)
  trailing <- value [] source
  unless (T.null (space trailing)) (Left "Trailing source JSON")
  pure decoded
 where
  space = T.dropWhile (`elem` [' ', '\t', '\r', '\n'])
  value path input = case T.uncons (space input) of
    Just ('{', rest) -> members path Set.empty (space rest)
    Just ('[', rest) -> elements path (space rest)
    Just ('"', _) -> snd <$> string (space input)
    Just (first, _) ->
      let (token, rest) = T.span (\c -> c `notElem` [' ', '\t', '\r', '\n', ',', ']', '}']) (space input)
       in if T.null token
            then Left "Missing source JSON value"
            else do
              when
                ((first == '-' || isDigit first) && integerPath path && T.any (`elem` ['.', 'e', 'E']) token)
                (Left "Source index/argument position must use an integer JSON token")
              pure rest
    Nothing -> Left "Missing source JSON value"
  integerPath ["bindings", _, key] = key `elem` ["indexOrigin", "indexOffset"]
  integerPath ["literalInterpretations", "#", "consumer", "argumentPosition"] = True
  integerPath _ = False
  members path seen input
    | Just rest <- T.stripPrefix "}" input = Right rest
    | otherwise = do
        (key, afterKey) <- string input
        when (Set.member key seen) (Left ("Duplicate source identity/key: " <> T.unpack key))
        afterColon <- maybe (Left "Missing source JSON colon") Right (T.stripPrefix ":" (space afterKey))
        afterValue <- space <$> value (path <> [key]) afterColon
        case T.uncons afterValue of
          Just (',', next) -> members path (Set.insert key seen) (space next)
          Just ('}', rest) -> Right rest
          _ -> Left "Missing source JSON object delimiter"
  elements path input
    | Just rest <- T.stripPrefix "]" input = Right rest
    | otherwise = do
        after <- space <$> value (path <> ["#"]) input
        case T.uncons after of
          Just (',', next) -> elements path (space next)
          Just (']', rest) -> Right rest
          _ -> Left "Missing source JSON array delimiter"
  string input = case T.uncons input of
    Just ('"', rest) -> do
      count <- endString 1 False rest
      let (token, after) = T.splitAt count input
      decoded <- eitherDecodeStrict' (TE.encodeUtf8 token) :: Either String Text
      pure (decoded, after)
    _ -> Left "Expected source JSON string"
  endString :: Int -> Bool -> Text -> Either String Int
  endString count escaped input = case T.uncons input of
    Nothing -> Left "Unclosed source JSON string"
    Just (char, rest)
      | escaped -> endString (count + 1) False rest
      | char == '\\' -> endString (count + 1) True rest
      | char == '"' -> Right (count + 1)
      | otherwise -> endString (count + 1) False rest

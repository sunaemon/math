{-# LANGUAGE OverloadedStrings #-}

-- Lossless source identity; never match a PDF formula by rendered text.
module FormulaAnchors (formulaTag, formulaMarkers, formulaAnchorsRequest) where

import ChapterPreparation (formulaLocations)
import Data.Aeson (Value, object, withObject, (.:), (.=))
import Data.Aeson.Types (Parser)
import Data.Bits (xor)
import Data.Char (ord)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Word (Word64)
import Numeric (showHex)

formulaTag :: Text -> Text -> Int -> Text
formulaTag source text start = formulaPrefix source text <> "-" <> T.pack (show start)

formulaPrefix :: Text -> Text -> Text
formulaPrefix source text = "BookFormula-" <> T.intercalate "." [T.pack (showHex (ord c) "") | c <- T.unpack source] <> "-" <> T.pack (showHex fingerprint "")
 where
  fingerprint = T.foldl' (\hash c -> (hash `xor` fromIntegral (ord c)) * 1099511628211) (14695981039346656037 :: Word64) text

formulaMarkers :: Text -> Text -> [(Int, Text)]
formulaMarkers source text =
  concat
    [ [(start, "\\BookFormulaStart{" <> prefix <> "-" <> T.pack (show start) <> "}"), (end, "\\BookFormulaEnd{}")]
    | (start, end) <- formulaLocations text
    ]
 where
  prefix = formulaPrefix source text

formulaAnchorsRequest :: Value -> Parser Value
formulaAnchorsRequest = withObject "formula anchors" $ \fields -> do
  source <- fields .: "source"
  text <- fields .: "text"
  let prefix = formulaPrefix source text
  pure (object ["formulas" .= [object ["bodyStart" .= start, "bodyEnd" .= end, "pdfTag" .= (prefix <> "-" <> T.pack (show start))] | (start, end) <- formulaLocations text]])

{-# LANGUAGE OverloadedStrings #-}

module MathSyntaxCLI (mathSyntaxMain, syntaxRecord) where

import Data.Aeson (Value, eitherDecode, encode, object, (.=))
import qualified Data.ByteString.Lazy as BL
import Data.Text (Text)
import LocatedMath
import MathSyntax
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)

-- The correspondence checker consumes this syntax tree, never the Sort audit's
-- inferred vocabulary. LocatedMath derives positions from the lossless tree.
-- A round-trip failure is retained as unsupported syntax, not silently accepted.
mathSyntaxMain :: Bool -> IO ()
mathSyntaxMain withLocations = do
  input <- BL.getContents
  case eitherDecode input :: Either String [Text] of
    Left message -> hPutStrLn stderr message >> exitFailure
    Right formulas -> BL.putStr (encode (map (syntaxRecord withLocations) formulas))

syntaxRecord :: Bool -> Text -> Value
syntaxRecord withLocations formula =
  let expr = parseMathExpr formula
   in object
        [ "source" .= formula
        , "roundtrip" .= (renderMathExpr expr == formula)
        , "problems" .= (["Unmatched grouping brace" :: Text | not (balancedBraces 0 (tokenizeMath formula))])
        , "tree" .= (if withLocations then locatedValue (locateMath 0 expr) else syntaxValue expr)
        ]
 where
  balancedBraces :: Int -> [MathToken] -> Bool
  balancedBraces depth [] = depth == 0
  balancedBraces depth (TokLBrace : rest) = balancedBraces (depth + 1) rest
  balancedBraces depth (TokRBrace : rest) = depth > 0 && balancedBraces (depth - 1) rest
  balancedBraces depth (_ : rest) = balancedBraces depth rest
  syntaxValue expr = case expr of
    MathSeq items -> object ["kind" .= ("sequence" :: Text), "items" .= map syntaxValue items]
    MathCommand name optional args ->
      object ["kind" .= ("command" :: Text), "name" .= name, "optional" .= fmap syntaxValue optional, "args" .= map syntaxValue args]
    MathGroup body -> object ["kind" .= ("group" :: Text), "body" .= syntaxValue body]
    MathScript base marker arg ->
      object ["kind" .= ("script" :: Text), "base" .= syntaxValue base, "marker" .= marker, "argument" .= syntaxValue arg]
    MathText body -> object ["kind" .= ("text" :: Text), "text" .= body]
    MathRaw body -> object ["kind" .= ("raw" :: Text), "text" .= body]

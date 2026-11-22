{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE OverloadedStrings #-}

{- | Character offsets are half-open and relative to the formula's source.
They count Unicode code points, as do the Markdown and Lean bridge reports.
-}
module LocatedMath (SourceSpan (..), LocatedMath (..), LocatedNode (..), locateMath, locatedValue) where

import Data.Aeson (Value, object, (.=))
import Data.Aeson.Types (Pair)
import Data.Data (Data)
import Data.Text (Text)
import qualified Data.Text as T
import MathSyntax (MathExpr (..))

data SourceSpan = SourceSpan {spanStart :: Int, spanEnd :: Int}
  deriving (Eq, Show, Data)

data LocatedMath = LocatedMath SourceSpan LocatedNode
  deriving (Eq, Show, Data)

data LocatedNode
  = LocatedSequence [LocatedMath]
  | LocatedCommand Text (Maybe LocatedMath) [LocatedMath]
  | LocatedGroup LocatedMath
  | LocatedScript LocatedMath Text LocatedMath
  | LocatedText Text
  | LocatedRaw Text
  deriving (Eq, Show, Data)

locateMath :: Int -> MathExpr -> LocatedMath
locateMath start expression =
  let (node, end) = case expression of
        MathText text -> (LocatedText text, start + T.length text)
        MathRaw text -> (LocatedRaw text, start + T.length text)
        MathSeq items ->
          let (children, stop) = locateMany 0 start items
           in (LocatedSequence children, stop)
        MathGroup body ->
          let child = locateMath (start + 1) body
           in (LocatedGroup child, endOf child + 1)
        MathScript base marker argument ->
          let base' = locateMath start base
              argument' = locateMath (endOf base' + T.length marker) argument
           in (LocatedScript base' marker argument', endOf argument')
        MathCommand name optional arguments ->
          let afterName = start + 1 + T.length name
              optional' = fmap (locateMath (afterName + 1)) optional
              afterOptional = maybe afterName ((+ 1) . endOf) optional'
              (arguments', stop) = locateMany 1 afterOptional arguments
           in (LocatedCommand name optional' arguments', stop)
   in LocatedMath (SourceSpan start end) node
 where
  locateMany _ offset [] = ([], offset)
  locateMany delimiters offset (item : rest) =
    let child = locateMath (offset + delimiters) item
        (children, stop) = locateMany delimiters (endOf child + delimiters) rest
     in (child : children, stop)

endOf :: LocatedMath -> Int
endOf (LocatedMath sourceSpan _) = spanEnd sourceSpan

locatedValue :: LocatedMath -> Value
locatedValue (LocatedMath sourceSpan node) =
  object $
    ["start" .= spanStart sourceSpan, "end" .= spanEnd sourceSpan] <> fields node
 where
  kind :: Text -> [Pair]
  kind name = ["kind" .= name]
  fields (LocatedSequence items) = kind "sequence" <> ["items" .= map locatedValue items]
  fields (LocatedCommand name optional arguments) =
    kind "command"
      <> ["name" .= name, "optional" .= fmap locatedValue optional, "args" .= map locatedValue arguments]
  fields (LocatedGroup body) = kind "group" <> ["body" .= locatedValue body]
  fields (LocatedScript base marker argument) =
    kind "script"
      <> ["base" .= locatedValue base, "marker" .= marker, "argument" .= locatedValue argument]
  fields (LocatedText body) = kind "text" <> ["text" .= body]
  fields (LocatedRaw body) = kind "raw" <> ["text" .= body]

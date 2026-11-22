{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

{- | Read-only inspection of the actual semantic value. This is deliberately
separate from interpretation and review: the viewer cannot submit this tree
as a replacement expression or use it to approve a correspondence.
-}
module SemanticInspection (semanticValue) where

import Data.Aeson (Value (..), object, toJSON, (.=))
import qualified Data.Aeson.Key as K
import Data.Data (Data, constrFields, gmapQ, showConstr, toConstr)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Typeable (cast)
import LocatedMath (SourceSpan (..))
import SemanticAST (Expr)

semanticValue :: Expr -> Value
semanticValue = inspectValue

inspectValue :: forall a. (Data a) => a -> Value
inspectValue value
  | Just text <- cast value :: Maybe Text = String text
  | Just text <- cast value :: Maybe String = String (T.pack text)
  | Just number <- cast value :: Maybe Int = toJSON number
  | Just number <- cast value :: Maybe Integer = toJSON number
  | Just boolean <- cast value :: Maybe Bool = Bool boolean
  | Just (SourceSpan start end) <- cast value = object ["start" .= start, "end" .= end]
  | otherwise = case (name, children) of
      ("[]", []) -> toJSON ([] :: [Value])
      (":", [first, Array rest]) -> toJSON (first : foldr (:) [] rest)
      ("Nothing", []) -> Null
      ("Just", [child]) -> child
      _ -> object $ ["node" .= name] <> if null fields then ["arguments" .= children | not (null children)] else ["fields" .= object [K.fromString field .= child | (field, child) <- zip fields children]]
 where
  constructor = toConstr value
  name = T.pack (showConstr constructor)
  fields = constrFields constructor
  children = gmapQ inspectValue value

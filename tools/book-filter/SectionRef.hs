{-# LANGUAGE OverloadedStrings #-}

{- | The cross-reference syntax @§{id}@, shared by the lint pass
('sectionRefsInLine'), the section-reference resolver ('expandStr',
'expandRawTexSecRefs'), and the dependency graph ('sectionRefsInText').
A single tokenizer so those scanners cannot drift apart.
-}
module SectionRef (
  nextSectionRef,
) where

import Data.Text (Text)
import qualified Data.Text as T

{- | The next @§{id}@ reference in the text: the text before it, the id, and the
text after the closing brace. 'Nothing' when no complete @§{...}@ remains.

The id runs up to the first @}@, matching the original hand-rolled scanners:
an unbalanced @§{@ swallows up to the next @}@, and a @§{@ with no later @}@
yields 'Nothing'. The id may be empty (for @§{}@); callers decide whether to
skip it.
-}
nextSectionRef :: Text -> Maybe (Text, Text, Text)
nextSectionRef txt =
  case T.breakOn sectionRefOpen txt of
    (_, after)
      | T.null after -> Nothing
    (before, after) ->
      case T.breakOn "}" (T.drop (T.length sectionRefOpen) after) of
        (_, rest)
          | T.null rest -> Nothing
        (hid, rest) -> Just (before, hid, T.drop 1 rest)

-- @§{@: a section sign (U+00A7, \167) followed by an opening brace.
sectionRefOpen :: Text
sectionRefOpen = "\167{"

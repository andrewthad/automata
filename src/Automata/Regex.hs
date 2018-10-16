module Automata.Regex
  ( Regex(..)
  ) where

data Regex t
  = RegexLiteral t t
    -- ^ Inclusive low and high
  | RegexEmpty
  | RegexRejection
  | RegexUnion (Regex t) (Regex t)
  | RegexAppend (Regex t) (Regex t)
  | RegexStar (Regex t)



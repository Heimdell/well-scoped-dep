module Text.Parsing where

import Control.Applicative
import Control.Monad
import Data.Set (Set)
import Data.Set qualified as Set
import Data.List.NonEmpty qualified as NE

newtype Parser e l a = Parser
  { unParser :: [l] -> (Maybe a, Set e, Int)
  }

instance Ord e => Functor (Parser e l) where
  fmap = liftM

instance Ord e => Applicative (Parser e l) where
  pure a = Parser (const (Just a, mempty, 0))
  (<*>)  = ap

instance Ord e => Monad (Parser e l) where
  Parser ma >>= k = Parser \s -> do
    let (res, errs, d) = ma s
    case res of
      Nothing -> (Nothing, errs, d)
      Just a  -> do
        let (res', errs', d') = (k a).unParser (drop d s)
        if d' > 0
        then (res', errs', d + d')
        else (res', errs <> errs', d)

runParser :: Ord e => Parser e l a -> [l] -> Either (Set e, l) a
runParser parser input =
  case parser.unParser input of
    (Just a,  _,      _)    -> pure a
    (Nothing, report, rest) -> Left (report, input !! rest)

handle :: (Ord e) => Parser e l a -> (Set e -> Parser e l a) -> Parser e l a
handle ma handler = Parser \s ->
  case ma.unParser s of
    (Nothing, errs, 0) -> (handler errs).unParser s
    other              -> other

die :: (Ord e) => Set e -> Parser e l a
die msgs = Parser (const (Nothing, msgs, 0))

instance (Ord e) => Alternative (Parser e l) where
  empty = die mempty

  l <|> r =
    handle l \lerrs ->
    handle r \rerrs ->
      die (lerrs <> rerrs)

project :: Ord e => (l -> a) -> Parser e l a
project f = Parser \case
  [] -> error "[]"
  l : _ -> (Just (f l), mempty, 0)

match :: (Ord e) => e -> (l -> Maybe a) -> Parser e l a
match err proj = Parser \case
  [] -> error "[]"
  (proj -> Just a) : _ -> (Just a,  mempty,            1)
  _                    -> (Nothing, Set.singleton err, 0)

sepBy  :: (Ord e) => Parser e l a -> Parser e l sep -> Parser e l [a]
sepBy1 :: (Ord e) => Parser e l a -> Parser e l sep -> Parser e l (NE.NonEmpty a)
sepBy  p sep' = NE.toList <$>sepBy1 p sep' <|> pure []
sepBy1 p sep' = (NE.:|) <$> p <*> many (sep' *> p)

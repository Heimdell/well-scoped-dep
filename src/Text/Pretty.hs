module Text.Pretty
  ( module Text.PrettyPrint.HughesPJClass
  , PrettyInContext (pic)
  , (\\)
  , (<.>)
  , list
  , block
  ) where

import Text.PrettyPrint.HughesPJClass

import Data.Vec
import Data.Name
import Data.Pos
import Data.Maybe

class PrettyInContext p where
  pic :: Vec n Name -> p n -> Doc

instance Pretty Name where
  pPrint = text . (.raw)

infixr 1 \\
(\\) :: Doc -> Doc -> Doc
a \\ b = hang a 2 b

infixl 6 <.>
(<.>) :: Doc -> Doc -> Doc
(<.>) = (Text.PrettyPrint.HughesPJClass.<>)

list :: [Doc] -> Doc
list = fsep . punctuate comma

block :: [Doc] -> Doc
block = vcat . punctuate "\n"

instance Pretty Pos where
  pPrint Pos{line, col, filename, source} =
    vcat
      [ text filename <.> ":" <.> int line <.> ":" <.> int col
      , text (' ' <$ prefix) <.> " |"
      , text         prefix  <.> " | " <.> text sourceLine
      , text (' ' <$ prefix) <.> " |"  <.> text (replicate col ' ') <.> "^"
      ]
    where
      prefix = show line

      sourceLine = fromMaybe "" $ listToMaybe $ drop (line - 1) $ lines source

newtype ShortPos = ShortPos {pos :: Pos}

instance Pretty ShortPos where
  pPrint ShortPos {pos = Pos {line, col, filename}} =
    text filename <.> ":" <.> int line <.> ":" <.> int col

instance Pretty LocatedName where
  pPrint LocatedName {name} =
    pPrint name <+> "@" <+> pPrint (ShortPos name.pos)
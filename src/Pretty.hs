{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}

module Pretty
  ( module Text.PrettyPrint.HughesPJClass
  , PrettyInContext (pic)
  , (\\)
  , (<.>)
  , list
  , block
  ) where

import Text.PrettyPrint.HughesPJClass

import Vec
import Name

class PrettyInContext p where
  pic :: Vec n Name -> p n -> Doc

instance Pretty Name where
  pPrint = text . (.rawName)

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
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DuplicateRecordFields #-}

module Phase.Runtime.Value.Pretty where

import Prelude hiding (fst, snd)

import Data.Vec
import Text.Pretty

import Phase.Runtime.Value.Structure

instance PrettyInContext Value where
  pic names = \case
    ValueNeutral neutral -> pic names neutral
    ValueU -> "Type"
    ValuePi {argName, argTy, resTy} ->
      parens (pPrint argName <+> ":" <+> pic names argTy) <+> "->" \\
        pic (argName :> names) resTy

    ValueSigma  {fstName, fstTy, sndTy} ->
      braces (pPrint fstName <+> ":" <+> pic names fstTy <.> "," \\
        pic (fstName :> names) sndTy)

    ValueEq {x, y} ->
      parens (pic names x <+> "=" <+> pic names y)

    ValueLam {argName, body} ->
      "\\" <.> pPrint argName <+> "->" \\
        pic (argName :> names) body

    ValuePair {fst, snd} ->
      parens (pic names fst <.> "," \\
        pic names snd)

    ValueRefl -> "refl"

instance PrettyInContext Neutral where
  pic names = \case
    NeutralVar var -> pPrint (index var names)
    NeutralApp {f, x} -> parens (pic names f <+> pic names x)
    NeutralUncurry {fstName, sndName, pair, consume} ->
      ("let" <+> pPrint fstName <.> "," <+> pPrint sndName <+> "=" \\ pic names pair)
        $$ pic (sndName :> fstName :> names) consume
    NeutralTransp {a, x, y, p, px, eq} ->
      "transp" <.> parens (list [pic names a, pic names x, pic names y, pic names p, pic names px, pic names eq])

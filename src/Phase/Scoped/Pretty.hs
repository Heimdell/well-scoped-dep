{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoFieldSelectors #-}
{-# LANGUAGE DuplicateRecordFields #-}

module Phase.Scoped.Pretty () where

import Prelude hiding (fst, snd, zip)

import Data.Vec
import Data.Foldable
import Data.Functor ((<&>))
import Text.Pretty

import Phase.Scoped.Structure

instance PrettyInContext Expr where
  pic names = \case
    ExprVar var -> pPrint (index var names)

    ExprU -> "Type"

    ExprPi {argName, argTy, resTy} ->
      brackets (pPrint argName <+> ":" <+> pic names argTy) \\
        pic (argName :> names) resTy

    ExprSigma {fstName, fstTy, sndTy} ->
      braces (pPrint fstName <+> ":" <+> pic names fstTy <.> "," \\
        pic (fstName :> names) sndTy)

    ExprEq {x, y} ->
      parens (pic names x <+> "==" <+> pic names y)

    ExprLam {argName, body} ->
      "\\" <.> pPrint argName <.> "." \\
        pic (argName :> names) body

    ExprPair {fst, snd} ->
      parens (pic names fst <.> "," \\
        pic names snd)

    ExprRefl -> "refl"

    ExprApp {f, x} -> parens (pic names f <+> pic names x)

    ExprUncurry {fstName, sndName, pair, consume} ->
      ("let" <+> pPrint fstName <.> "," <+> pPrint sndName <+> "=" \\ pic names pair)
        $$ pic (sndName :> fstName :> names) consume

    ExprTransp {a, x, y, p, px, eq} ->
      "transp" <.> parens (list [pic names a, pic names x, pic names y, pic names p, pic names px, pic names eq])

    ExprHole name -> "?" <+> pPrint name

    ExprLetRec {declNames, declTys, declVals, rest} ->
      ("let" <+> "rec" \\
        block (toList (picDecl <$> zip declNames (zip declTys declVals))))
      $$ pic names' rest
      where
        names' = declNames +++ names

        picDecl (name, (ty, val)) =
          (pPrint name
            \\ ":" <+> pic names ty)
            \\ "=" <+> pic names' val
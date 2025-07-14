{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoFieldSelectors #-}
{-# LANGUAGE DuplicateRecordFields #-}

module Phase.Scoped.Pretty () where

import Prelude hiding (fst, snd)

import Pretty
import Vec

import Phase.Scoped.Structure
import Data.Foldable
import Data.Functor ((<&>))

instance PrettyInContext Expr where
  pic names = \case
    ExprVar var -> pPrint (index var names)

    ExprU -> "Type"

    ExprPi {argName, argTy, resTy} ->
      parens (pPrint argName <+> ":" <+> pic names argTy) <+> "->" \\
        pic (argName :> names) resTy

    ExprSigma {fstName, fstTy, sndTy} ->
      braces (pPrint fstName <+> ":" <+> pic names fstTy <.> "," \\
        pic (fstName :> names) sndTy)

    ExprEq {x, y} ->
      parens (pic names x <+> "=" <+> pic names y)

    ExprLam {argName, body} ->
      "\\" <.> pPrint argName <+> "->" \\
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

    ExprLetRec {decls, rest} ->
      ("let" <+> "rec" \\
        block (toList (picDecl <$> decls)))
      $$ pic names' rest
      where
        delta = decls <&> \(name, _ty, _val) -> name
        names' = delta +++ names

        picDecl (name, ty, val) =
          pPrint name
            \\ ":" <+> pic names ty
            \\ "=" <+> pic names' val
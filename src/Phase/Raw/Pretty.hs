{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Phase.Raw.Pretty () where

import Prelude hiding (fst, snd)

import Phase.Raw.Structure

import Pretty

instance Pretty Expr where
  pPrint = \case
    ExprVar var -> pPrint var

    ExprU -> "Type"

    ExprPi {argName, argTy, resTy} ->
      brackets (pPrint argName <+> ":" <+> pPrint argTy) \\
        pPrint resTy

    ExprSigma {fstName, fstTy, sndTy} ->
      braces (pPrint fstName <+> ":" <+> pPrint fstTy <.> "," \\
        pPrint sndTy)

    ExprEq {x, y} ->
        parens (pPrint x <+> "==" <+> pPrint y)

    ExprLam {argName, body} ->
      "\\" <.> pPrint argName <.> "." \\
        pPrint body

    ExprPair {fst, snd} ->
      parens (pPrint fst <.> "," \\
        pPrint snd)

    ExprRefl -> "refl"

    ExprApp {f, x} -> parens (pPrint f <+> pPrint x)

    ExprUncurry {fstName, sndName, pair, consume} ->
      ("let" <+> pPrint fstName <.> "," <+> pPrint sndName <+> "=" \\ pPrint pair)
        $$ pPrint consume

    ExprTransp {a, x, y, p, px, eq} ->
      "transp" <.> parens (list [pPrint a, pPrint x, pPrint y, pPrint p, pPrint px, pPrint eq])

    ExprLetRec {decls, rest} ->
      ("let" <+> "rec" \\
        block (picDecl <$> decls))
      $$ pPrint rest
      where
        picDecl (name, ty, val) =
          (pPrint name
            \\ ":" <+> pPrint ty)
            \\ "=" <+> pPrint val
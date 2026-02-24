{-# LANGUAGE OverloadedStrings #-}

module FitchToMM.Nonfree
  ( proveNfWff,
    proveNfLst,
    proveNfCtx,
    proveNfTrm,
  )
where

import qualified Control.Monad.Writer.Strict as W
import qualified Data.Text as T
import FitchToMM.Declarations
import FitchToMM.FitchProof (Context)
import FitchToMM.Matcher
import FitchToMM.Parser
import FitchToMM.ProofWriter
import FitchToMM.SyntaxProver

proveNfCtx :: AllowedSubs -> T.Text -> Context -> ProofWriter
proveNfCtx allowed x ctx
  -- A variable that does not occur is not free
  | not $ any (occursInWff allowed x) ctx = do
      reqDisjointFor (VarHyp x) (varsInCtx ctx)
      ctxPrf <- proveCtx ctx
      xPrf <- proveVar x
      proveMMStep "nf.ctx-none" [ctxPrf, xPrf]
proveNfCtx allowed x (ph : ctx) = do
  ctxPrf <- proveCtx ctx
  phPrf <- proveWff ph
  xPrf <- proveVar x
  nfPrf1 <- proveNfCtx allowed x ctx
  nfPrf2 <- proveNfWff allowed x ph
  proveMMStep "nf.ctx" [ctxPrf, phPrf, xPrf, nfPrf1, nfPrf2]
proveNfCtx _ _ _ = W.lift $ Left Inapplicable

proveNfWff :: AllowedSubs -> T.Text -> Wff -> ProofWriter
-- A variable that does not occur is not free
proveNfWff allowed x ph
  | not $ occursInWff allowed x ph = do
      reqDisjointFor (VarHyp x) (varsInWff ph)
      phPrf <- proveWff ph
      xPrf <- proveVar x
      proveMMStep "nf.wff-none" [phPrf, xPrf]
-- Case for binary connectives
proveNfWff allowed x (WffBinOp op ph ps) = do
  phPrf <- proveWff ph
  psPrf <- proveWff ps
  xPrf <- proveVar x
  nfPrf1 <- proveNfWff allowed x ph
  nfPrf2 <- proveNfWff allowed x ps
  let label OpAnd = "nf.wff-and"
      label OpOr = "nf.wff-or"
      label OpImplies = "nf.wff-implies"
      label OpIff = "nf.wff-iff"
  proveMMStep (label op) [phPrf, psPrf, xPrf, nfPrf1, nfPrf2]
-- Case for negation
proveNfWff allowed x (WffNot ph) = do
  phPrf <- proveWff ph
  xPrf <- proveVar x
  nfPrf <- proveNfWff allowed x ph
  proveMMStep "nf.wff-not" [phPrf, xPrf, nfPrf]
-- Case for predicates
proveNfWff allowed x (WffAtom p args) = do
  xPrf <- proveVar x
  pPrf <- proveStep $ prdStep p
  argsPrf <- proveLst args
  nfPrf <- proveNfLst allowed x args
  proveMMStep "nf.wff-prd" [xPrf, pPrf, argsPrf, nfPrf]
-- Case for quantifiers
proveNfWff allowed x (WffQnt q y ph)
  | x == y = do
      phPrf <- proveWff ph
      xPrf <- proveVar x
      qPrf <- proveStep $ qntStep q
      proveMMStep "nf.wff-qnt-1" [phPrf, xPrf, qPrf]
  | x /= y = do
      reqDisjoint (VarHyp x) (VarHyp y)
      phPrf <- proveWff ph
      xPrf <- proveVar x
      yPrf <- proveVar y
      qPrf <- proveStep $ qntStep q
      nfPrf <- proveNfWff allowed x ph
      proveMMStep "nf.wff-qnt-2" [phPrf, xPrf, yPrf, qPrf, nfPrf]
-- Case for substitution
proveNfWff allowed x (WffSub t y ph)
  | x == y = do
      phPrf <- proveWff ph
      xPrf <- proveVar x
      tPrf <- proveTrm t
      nfPrf <- proveNfTrm allowed x t
      proveMMStep "nf.wff-sub-1" [phPrf, xPrf, tPrf, nfPrf]
  | x /= y = do
      reqDisjoint (VarHyp x) (VarHyp y)
      phPrf <- proveWff ph
      xPrf <- proveVar x
      yPrf <- proveVar y
      tPrf <- proveTrm t
      nfPrf1 <- proveNfTrm allowed x t
      nfPrf2 <- proveNfWff allowed x ph
      proveMMStep "nf.wff-sub-2" [phPrf, xPrf, yPrf, tPrf, nfPrf1, nfPrf2]
proveNfWff _ _ _ = W.lift $ Left $ Inapplicable

proveNfLst :: AllowedSubs -> T.Text -> [Term] -> ProofWriter
proveNfLst allowed x l
  -- A variable that does not occur is not free
  | not $ any (occursInTrm allowed x) l = do
      reqDisjointFor (VarHyp x) (varsInLst l)
      xPrf <- proveVar x
      tsPrf <- proveLst l
      proveMMStep "nf.lst-none" [xPrf, tsPrf]
proveNfLst allowed x l =
  let proveItems [t] = proveNfTrm allowed x t
      proveItems (t : ts) = do
        xPrf <- proveVar x
        tPrf <- proveTrm t
        tsPrf <- provePrependLst ts
        nfPrf1 <- proveNfTrm allowed x t
        nfPrf2 <- proveItems ts
        proveMMStep "nf.lst" [xPrf, tPrf, tsPrf, nfPrf1, nfPrf2]
      proveItems [] = W.lift $ Left $ EmptyList
   in proveItems $ reverse l

proveNfTrm :: AllowedSubs -> T.Text -> Term -> ProofWriter
-- A variable that does not occur is not free
proveNfTrm allowed x t
  | not $ occursInTrm allowed x t = do
      reqDisjointFor (VarHyp x) (varsInTrm t)
      xPrf <- proveVar x
      tPrf <- proveTrm t
      proveMMStep "nf.trm-none" [xPrf, tPrf]
-- Case for functions
proveNfTrm allowed x (TrmFunc f args) = do
  xPrf <- proveVar x
  fPrf <- proveStep $ funcStep f
  argsPrf <- proveLst args
  nfPrf <- proveNfLst allowed x args
  proveMMStep "nf.trm-func" [xPrf, fPrf, argsPrf, nfPrf]
-- Case for substitution
proveNfTrm allowed x (TrmSub t1 y t2)
  | x == y = do
      xPrf <- proveVar x
      t1Prf <- proveTrm t1
      t2Prf <- proveTrm t2
      nfPrf <- proveNfTrm allowed x t1
      proveMMStep "nf.trm-sub-1" [xPrf, t1Prf, t2Prf, nfPrf]
  | x /= y = do
      reqDisjoint (VarHyp x) (VarHyp y)
      xPrf <- proveVar x
      yPrf <- proveVar y
      t1Prf <- proveTrm t1
      t2Prf <- proveTrm t2
      nfPrf1 <- proveNfTrm allowed x t1
      nfPrf2 <- proveNfTrm allowed x t2
      proveMMStep "nf.trm-sub-2" [xPrf, yPrf, t1Prf, t2Prf, nfPrf1, nfPrf2]
proveNfTrm _ _ _ = W.lift $ Left $ Inapplicable

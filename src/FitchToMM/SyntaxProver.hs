{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : FitchToMM.SyntaxProver
-- Description : Generates Metamath proofs for syntactic structures
--
-- This module provides functions for generating Metamath proofs that syntactic
-- structures are well-formed.
module FitchToMM.SyntaxProver
  ( proveWff,
    proveCtx,
    proveTrm,
    qntStep,
    proveLst,
   -- provePrependLst,
    funcStep,
    prdStep,
    constStep,
    occursInWff,
    occursInTrm,
    occursInCtx,
    proveFHyp,
  )
where

import qualified Data.Text as T
import FitchToMM.Parser
import FitchToMM.ProofWriter
import FitchToMM.Matcher 
import FitchToMM.Context (Context(..))
import FitchToMM.Variable

-- | Generate a syntax proof for a well-formed formula (WFF).
proveWff :: Wff -> ProofWriter
-- Handle binary connectives
proveWff (WffBinOp op ph ps) = do
  phPrf <- proveWff ph
  psPrf <- proveWff ps
  let label OpAnd = "wff.and"
      label OpOr = "wff.or"
      label OpImplies = "wff.implies"
      label OpIff = "wff.iff"
  proveMMStep (label op) [phPrf, psPrf]
-- Handle negation
proveWff (WffNot ph) = do
  phPrf <- proveWff ph
  proveMMStep "wff.not" [phPrf]
-- Handle logical constants (true and false)
proveWff WffTrue = proveMMStep "wff.true" []
proveWff WffFalse = proveMMStep "wff.false" []
-- Handle quantified formulas
proveWff (WffQnt qnt x ph) = do
  phPrf <- proveWff ph
  xPrf <- proveVar x
  qPrf <- proveStep $ qntStep qnt
  proveMMStep "wff.qnt" [phPrf, xPrf, qPrf]
-- Handle atomic formulas formed by a predicate
proveWff (WffAtom p args) = do
  pPrf <- proveStep $ prdStep p
  argsPrf <- proveLst args
  proveMMStep "wff.atm" [pPrf, argsPrf]
-- Handle metavariable representing an arbitrary WFF
proveWff (WffMetavar var) = proveWffMetavar var
-- Handle substitution
proveWff (WffSub t x ph) = do
  phPrf <- proveWff ph
  xPrf <- proveVar x
  tPrf <- proveTrm t
  proveMMStep "wff.sub" [phPrf, xPrf, tPrf]

-- | Generate a syntax proof for a list of terms.
proveLst :: [Term] -> ProofWriter
proveLst [term] = do
  trmPrf <- proveTrm term
  proveMMStep "lst.singleton" [trmPrf]
proveLst (term : terms) = do
  trmPrf <- proveTrm term
  lstPrf <- proveLst terms
  proveMMStep "lst.prepend" [trmPrf, lstPrf]
proveLst _ = fromMistake EmptyList

-- | Generate a Metamath proof for a term.
proveTrm :: Term -> ProofWriter
proveTrm (TrmVar x) = do
  varPrf <- proveVar x
  proveMMStep "trm.var" [varPrf]
proveTrm (TrmFunc f args) = do
  fPrf <- proveStep $ funcStep f
  argsPrf <- proveLst args
  proveMMStep "trm.func" [fPrf, argsPrf]
proveTrm (TrmConst c) = proveStep $ constStep c
proveTrm (TrmMetavar var) = proveTrmMetavar var
proveTrm (TrmSub t1 x t2) = do
  xPrf <- proveVar x
  t1Prf <- proveTrm t1
  t2Prf <- proveTrm t2
  proveMMStep "trm.sub" [xPrf, t1Prf, t2Prf]

-- | Generate a syntax proof for a context.
proveCtx :: Context -> ProofWriter
proveCtx (RelContext []) = proveEllipsis
proveCtx (AbsContext []) = proveMMStep "ctx.empty" []
proveCtx (AbsContext [ph]) = do
  phPrf <- proveWff ph
  proveMMStep "ctx.singleton" [phPrf]
proveCtx (RelContext (ph : ctx)) = proveCtxAppend RelContext ctx ph
proveCtx (AbsContext (ph : ctx)) = proveCtxAppend AbsContext ctx ph

proveCtxAppend :: ([Wff] -> Context) -> [Wff] -> Wff -> ProofWriter
proveCtxAppend toCtx wffs phi = do
  ctxPrf <- proveCtx $ toCtx wffs
  phPrf <- proveWff phi
  proveMMStep "ctx.append" [ctxPrf, phPrf]

-- | Generate a syntax proof for a floating hypothesis.
proveFHyp :: Substitution -> FHyp -> ProofWriter
proveFHyp sub (WffHyp hyp) | Just wff <- lookupWff hyp sub = proveWff wff
proveFHyp sub (VarHyp hyp) | Just var <- lookupVar hyp sub = proveVar var
proveFHyp sub (TrmHyp hyp) | Just trm <- lookupTrm hyp sub = proveTrm trm
proveFHyp sub (CtxHyp hyp) | Just ctx <- lookupCtx hyp sub = proveCtx ctx
proveFHyp _ hyp = proveMetavar $ markInternal hyp

-- | Check whether a variable occurs in a context.
occursInCtx :: AllowedSubs -> T.Text -> Context -> Bool
occursInCtx a x ctx = any (occursInWff a x) (ctxWffs ctx)

-- | Check whether a variable occurs in a well-formed formula.
occursInWff :: AllowedSubs -> T.Text -> Wff -> Bool
occursInWff a x (WffBinOp _ lhs rhs) = occursInWff a x lhs || occursInWff a x rhs
occursInWff a x (WffNot wff) = occursInWff a x wff
occursInWff a x (WffQnt _ y wff) = x == y || occursInWff a x wff
occursInWff a x (WffAtom _ args) = any (occursInTrm a x) args
occursInWff a x (WffMetavar var) = x `elem` a var
occursInWff a x (WffSub trm var wff) = x == var || occursInTrm a x trm || occursInWff a x wff
occursInWff _ _ WffTrue = False
occursInWff _ _ WffFalse = False

-- | Check whether a variable occurs in a term.
occursInTrm :: AllowedSubs -> T.Text -> Term -> Bool
occursInTrm _ x (TrmVar y) = x == y
occursInTrm a x (TrmFunc _ args) = any (occursInTrm a x) args
occursInTrm _ _ (TrmConst _) = False
occursInTrm a x (TrmMetavar var) = x `elem` a var
occursInTrm a x (TrmSub t1 var t2) = occursInTrm a x t1 || x == var || occursInTrm a x t2

-- | Create a Metamath proof step for a quantifier.
qntStep :: Quantifier -> RpnStep
qntStep QntForall = RpnStep 0 "qnt.forall"
qntStep QntExists = RpnStep 0 "qnt.exists"
qntStep QntUnique = RpnStep 0 "qnt.unique"

-- | Create a Metamath proof step for a function.
funcStep :: T.Text -> RpnStep
funcStep funcName = RpnStep 0 $ "func." <> funcName

-- | Create a Metamath proof step for a predicate.
prdStep :: T.Text -> RpnStep
prdStep prdName = RpnStep 0 $ "prd." <> prdName

-- | Create a Metamath proof step for a term constant.
constStep :: T.Text -> RpnStep
constStep constName = RpnStep 0 $ "trm." <> constName
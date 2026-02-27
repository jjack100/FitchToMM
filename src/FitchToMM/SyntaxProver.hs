{-# LANGUAGE OverloadedStrings #-}

module FitchToMM.SyntaxProver
  ( proveWff,
    proveCtx,
    proveTrm,
    qntStep,
    proveLst,
    provePrependLst,
    funcStep,
    prdStep,
    constStep,
    occursInWff,
    occursInTrm,
    occursInCtx,
  )
where

import Control.Monad.Writer.Strict
import qualified Data.Text as T
import FitchToMM.Declarations (AllowedSubs)
import FitchToMM.Parser
import FitchToMM.ProofWriter

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

proveLst :: [Term] -> ProofWriter
proveLst [term] = do
  trmPrf <- proveTrm term
  proveMMStep "lst.singleton" [trmPrf]
proveLst (term : terms) = do
  trmPrf <- proveTrm term
  lstPrf <- proveLst terms
  proveMMStep "lst.prepend" [trmPrf, lstPrf]
proveLst _ = lift $ Left EmptyList

provePrependLst :: [Term] -> ProofWriter
provePrependLst [term] = do
  trmPrf <- proveTrm term
  proveMMStep "lst.singleton" [trmPrf]
provePrependLst (term : terms) = do
  trmPrf <- proveTrm term
  lstPrf <- provePrependLst terms
  proveMMStep "lst.append" [trmPrf, lstPrf]
provePrependLst _ = lift $ Left EmptyList

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

occursInCtx :: AllowedSubs -> T.Text -> Context -> Bool
occursInCtx a x ctx = any (occursInWff a x) (ctxWffs ctx)

occursInWff :: AllowedSubs -> T.Text -> Wff -> Bool
occursInWff a x (WffBinOp _ lhs rhs) = occursInWff a x lhs || occursInWff a x rhs
occursInWff a x (WffNot wff) = occursInWff a x wff
occursInWff a x (WffQnt _ y wff) = x == y || occursInWff a x wff
occursInWff a x (WffAtom _ args) = any (occursInTrm a x) args
occursInWff a x (WffMetavar var) = x `elem` a var
occursInWff a x (WffSub trm var wff) = x == var || occursInTrm a x trm || occursInWff a x wff
occursInWff _ _ WffTrue = False
occursInWff _ _ WffFalse = False

occursInTrm :: AllowedSubs -> T.Text -> Term -> Bool
occursInTrm _ x (TrmVar y) = x == y
occursInTrm a x (TrmFunc _ args) = any (occursInTrm a x) args
occursInTrm _ _ (TrmConst _) = False
occursInTrm a x (TrmMetavar var) = x `elem` a var
occursInTrm a x (TrmSub t1 var t2) = occursInTrm a x t1 || x == var || occursInTrm a x t2

qntStep :: Quantifier -> RpnStep
qntStep QntForall = RpnStep 0 "qnt.forall"
qntStep QntExists = RpnStep 0 "qnt.exists"
qntStep QntUnique = RpnStep 0 "qnt.unique"

funcStep :: T.Text -> RpnStep
funcStep funcName = RpnStep 0 $ "func." <> funcName

prdStep :: T.Text -> RpnStep
prdStep prdName = RpnStep 0 $ "prd." <> prdName

constStep :: T.Text -> RpnStep
constStep constName = RpnStep 0 $ "trm." <> constName
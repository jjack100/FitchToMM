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
    binOpStep,
  )
where

import Control.Monad.Writer.Strict
import qualified Data.Text as T
import FitchToMM.Parser
import FitchToMM.ProofWriter

proveWff :: Wff -> ProofWriter
-- Handle binary connectives
proveWff (WffBinOp op phi psi) = do
  phiPrf <- proveWff phi
  psiPrf <- proveWff psi
  wffPrf <- proveStep $ binOpStep op
  return $ phiPrf <> psiPrf <> wffPrf
-- Handle negation
proveWff (WffNot phi) = do
  phiPrf <- proveWff phi
  wffPrf <- proveStep wffNotStep
  return $ phiPrf <> wffPrf
-- Handle logical constants (true and false)
proveWff WffTrue = proveStep wffTrueStep
proveWff WffFalse = proveStep wffFalseStep
-- Handle quantified formulas
proveWff (WffQnt qnt var phi) = do
  phiPrf <- proveWff phi
  varPrf <- proveVar var
  qntPrf <- proveStep $ qntStep qnt
  wffPrf <- proveStep wffQntStep
  return $ phiPrf <> varPrf <> qntPrf <> wffPrf
-- Handle atomic formulas formed by a predicate
proveWff (WffAtom p args) = do
  predPrf <- proveStep $ prdStep p
  lstPrf <- proveLst args
  wffPrf <- proveStep wffAtmStep
  return $ predPrf <> lstPrf <> wffPrf
-- Handle metavariable representing an arbitrary WFF
proveWff (WffMetavar var) = proveWffMetavar var

-- Metamath expects a list to be built by appending rather than prepending,
-- so we must reverse the items first
proveLst :: [Term] -> ProofWriter
proveLst = provePrependLst . reverse

provePrependLst :: [Term] -> ProofWriter
provePrependLst [term] = do
  trmPrf <- proveTrm term
  singlePrf <- proveStep lstSingleStep
  return $ trmPrf <> singlePrf
provePrependLst (term : terms) = do
  trmPrf <- proveTrm term
  lstPrf <- provePrependLst terms
  appendPrf <- proveStep lstAppendStep
  return $ trmPrf <> lstPrf <> appendPrf
provePrependLst _ = lift $ Left EmptyList

proveTrm :: Term -> ProofWriter
proveTrm (TrmVar x) = do
  varPrf <- proveVar x
  trmPrf <- proveStep trmVarStep
  return $ varPrf <> trmPrf
proveTrm (TrmFunc f args) = do
  funcPrf <- proveStep $ funcStep f
  lstPrf <- proveLst args
  trmPrf <- proveStep trmFuncStep
  return $ funcPrf <> lstPrf <> trmPrf
proveTrm (TrmConst name) = proveStep $ constStep name
proveTrm (TrmMetavar var) = proveTrmMetavar var

proveCtx :: [Wff] -> ProofWriter
proveCtx [] = proveEllipsis
proveCtx (phi : rest) = do
  ctxPrf <- proveCtx rest
  wffPrf <- proveWff phi
  appendPrf <- proveStep ctxAppendStep
  return $ ctxPrf <> wffPrf <> appendPrf

-- Define the labels and number of mandatory hypotheses they take as they
-- appear in the Metamath database:

ctxAppendStep :: RpnStep
ctxAppendStep = RpnStep 2 "ctx.append"

binOpStep :: BinOp -> RpnStep
binOpStep OpAnd = RpnStep 2 "wff.and"
binOpStep OpOr = RpnStep 2 "wff.or"
binOpStep OpImplies = RpnStep 2 "wff.implies"
binOpStep OpIff = RpnStep 2 "wff.iff"

wffNotStep :: RpnStep
wffNotStep = RpnStep 1 "wff.not"

wffTrueStep :: RpnStep
wffTrueStep = RpnStep 0 "wff.true"

wffFalseStep :: RpnStep
wffFalseStep = RpnStep 0 "wff.false"

qntStep :: Quantifier -> RpnStep
qntStep QntForall = RpnStep 0 "qnt.forall"
qntStep QntExists = RpnStep 0 "qnt.exists"
qntStep QntUnique = RpnStep 0 "qnt.unique"

wffQntStep :: RpnStep
wffQntStep = RpnStep 3 "wff.qnt"

trmVarStep :: RpnStep
trmVarStep = RpnStep 1 "trm.var"

trmFuncStep :: RpnStep
trmFuncStep = RpnStep 2 "trm.func"

wffAtmStep :: RpnStep
wffAtmStep = RpnStep 2 "wff.atm"

lstSingleStep :: RpnStep
lstSingleStep = RpnStep 1 "lst.single"

lstAppendStep :: RpnStep
lstAppendStep = RpnStep 2 "lst.append"

funcStep :: T.Text -> RpnStep
funcStep funcName = RpnStep 0 $ "func." <> funcName

prdStep :: T.Text -> RpnStep
prdStep prdName = RpnStep 0 $ "prd." <> prdName

constStep :: T.Text -> RpnStep
constStep constName = RpnStep 0 $ "trm." <> constName
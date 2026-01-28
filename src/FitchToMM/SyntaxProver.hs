{-# LANGUAGE OverloadedStrings #-}

module FitchToMM.SyntaxProver
  ( proveWff,
    proveCtx,
    proveTrm,
    qntLabel,
    proveLst,
    provePrependLst,
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
  wffPrf <- proveLabel $ binOpLabel op
  return $ phiPrf <> psiPrf <> wffPrf
-- Handle negation
proveWff (WffNot phi) = do
  phiPrf <- proveWff phi
  wffPrf <- proveLabel "wff.not"
  return $ phiPrf <> wffPrf
-- Handle logical constants (true and false)
proveWff WffTrue = proveLabel "wff.true"
proveWff WffFalse = proveLabel "wff.false"
-- Handle quantified formulas
proveWff (WffQnt qnt var phi) = do
  phiPrf <- proveWff phi
  varPrf <- proveVar var
  qntPrf <- proveLabel $ qntLabel qnt
  wffPrf <- proveLabel "wff.qnt"
  return $ phiPrf <> varPrf <> qntPrf <> wffPrf
-- Handle atomic formulas formed by a predicate
proveWff (WffAtom p args) = do
  predPrf <- proveLabel $ "prd." <> p
  lstPrf <- proveLst args
  wffPrf <- proveLabel "wff.atm"
  return $ predPrf <> lstPrf <> wffPrf
-- Handle metavariable representing an arbitrary WFF
proveWff (WffMetavar var) = proveWffMetavar var

-- Metamath expects a list to be built by appending rather than prepending,
-- so we must reverse the items first
proveLst :: [Term] -> ProofWriter
proveLst = provePrependLst .reverse

provePrependLst :: [Term] -> ProofWriter
provePrependLst [term] = do
  trmPrf <- proveTrm term
  singlePrf <- proveLabel "lst.single"
  return $ trmPrf <> singlePrf
provePrependLst (term : terms) = do
  trmPrf <- proveTrm term
  lstPrf <- provePrependLst terms
  appendPrf <- proveLabel "lst.append"
  return $ trmPrf <> lstPrf <> appendPrf
provePrependLst _ = lift $ Left EmptyList

proveTrm :: Term -> ProofWriter
proveTrm (TrmVar x) = do
  varPrf <- proveVar x
  trmPrf <- proveLabel "trm.var"
  return $ varPrf <> trmPrf
proveTrm (TrmFunc f args) = do
  funcPrf <- proveLabel $ "func." <> f
  lstPrf <- proveLst args
  trmPrf <- proveLabel "trm.func"
  return $ funcPrf <> lstPrf <> trmPrf
proveTrm (TrmConst name) = proveLabel $ "trm." <> name
proveTrm (TrmMetavar var) = proveTrmMetavar var

proveCtx :: [Wff] -> ProofWriter
proveCtx [] = proveEllipsis
proveCtx (phi : rest) = do
  ctxPrf <- proveCtx rest
  wffPrf <- proveWff phi
  appendPrf <- proveLabel "ctx.append"
  return $ ctxPrf <> wffPrf <> appendPrf

binOpLabel :: BinOp -> T.Text
binOpLabel OpAnd = "wff.and"
binOpLabel OpOr = "wff.or"
binOpLabel OpImplies = "wff.implies"
binOpLabel OpIff = "wff.iff"

qntLabel :: Quantifier -> T.Text
qntLabel QntForall = "qnt.forall"
qntLabel QntExists = "qnt.exists"
qntLabel QntUnique = "qnt.unique"
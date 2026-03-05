{-# LANGUAGE OverloadedStrings #-}

module FitchToMM.Equivalence
  ( EquivProof (..),
    proveEquiv,
  )
where

import qualified Data.Set as S
import FitchToMM.Declarations
import FitchToMM.FitchProof
import FitchToMM.Matcher
import FitchToMM.Parser
import FitchToMM.ProofWriter
import FitchToMM.SyntaxProver
import Data.Maybe (isJust)

proveEquiv :: EquivFact -> Label -> Context -> Wff -> Wff -> ProofWriter
proveEquiv eqv eqvLabel (AbsContext []) lhs rhs
  | Just (fHyps, dvrs) <- matchEqv eqv lhs rhs = do
      mapM_ applyDVR dvrs
      fHypPrfs <- fHyps
      proveMMStep eqvLabel fHypPrfs
proveEquiv eqv eqvLabel ctx lhs rhs
  | isJust $ matchEqv eqv lhs rhs = do
      ctx1Prf <- proveCtx $ AbsContext []
      ctx2Prf <- proveCtx ctx
      phPrf <- proveWff $ WffBinOp OpIff lhs rhs
      eqvPrf <- proveEquiv eqv eqvLabel (AbsContext []) lhs rhs
      proveMMStep "axm.thin" [ctx1Prf, ctx2Prf, phPrf, eqvPrf]
proveEquiv _ _ ctx ph ph'
  | ph == ph' = do
      ctxPrf <- proveCtx ctx
      phPrf <- proveWff ph
      proveMMStep "thm.eqv-id" [ctxPrf, phPrf]
proveEquiv eqv eqvLabel ctx (WffBinOp op ph1 ps1) (WffBinOp op' ph2 ps2)
  | op == op' = do
      ctxPrf <- proveCtx ctx
      ph1Prf <- proveWff ph1
      ps1Prf <- proveWff ps1
      ph2Prf <- proveWff ph2
      ps2Prf <- proveWff ps2
      eqvPrf1 <- proveEquiv eqv eqvLabel (AbsContext []) ph1 ph2
      eqvPrf2 <- proveEquiv eqv eqvLabel (AbsContext []) ps1 ps2
      let label OpAnd = "thm.eqv-and"
          label OpOr = "thm.eqv-or"
          label OpImplies = "thm.eqv-implies"
          label OpIff = "thm.eqv-iff"
      proveMMStep (label op) [ctxPrf, ph1Prf, ps1Prf, ph2Prf, ps2Prf, eqvPrf1, eqvPrf2]
proveEquiv eqv eqvLabel ctx (WffNot ph) (WffNot ps) = do
  ctxPrf <- proveCtx ctx
  phPrf <- proveWff ph
  psPrf <- proveWff ps
  eqvPrf <- proveEquiv eqv eqvLabel (AbsContext []) ph ps
  proveMMStep "thm.eqv-not" [ctxPrf, phPrf, psPrf, eqvPrf]
proveEquiv eqv eqvLabel ctx (WffQnt q x ph) (WffQnt q' x' ps)
  | q == q',
    x == x' = do
      ctxPrf <- proveCtx ctx
      phPrf <- proveWff ph
      psPrf <- proveWff ps
      xPrf <- proveVar x
      eqvPrf <- proveEquiv eqv eqvLabel (AbsContext []) ph ps
      let label QntForall = "thm.eqv-forall"
          label QntExists = "thm.eqv-exists"
          label QntUnique = "thm.eqv-unique"
      proveMMStep (label q) [ctxPrf, phPrf, psPrf, xPrf, eqvPrf]
proveEquiv eqv eqvLabel ctx (WffSub t x ph) (WffSub t' x' ps)
  | t == t',
    x == x' = do
      ctxPrf <- proveCtx ctx
      phPrf <- proveWff ph
      psPrf <- proveWff ps
      xPrf <- proveVar x
      tPrf <- proveTrm t
      eqvPrf <- proveEquiv eqv eqvLabel (AbsContext []) ph ps
      proveMMStep "thm.eqv-sub" [ctxPrf, phPrf, psPrf, xPrf, tPrf, eqvPrf]
proveEquiv _ _ _ _ _ = fromMistake Inapplicable

matchEqv :: EquivFact -> Wff -> Wff -> Maybe (ProofWriterM [RpnStack], S.Set DVR)
matchEqv (EquivFact lhs rhs fHyps fromDVRs) lhs' rhs' = do
  lhsSub <- lhs' `matchTo` lhs
  rhsSub <- rhs' `matchTo` rhs
  sub <- merge lhsSub rhsSub
  toDVRs <- checkDisjoints sub fromDVRs
  let fHypPrfs = mapM (proveFHyp sub) fHyps
  return (fHypPrfs, toDVRs)
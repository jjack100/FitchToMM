{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : FitchToMM.Variable
-- Description : Handling of variables and floating hypotheses in proofs
--
-- This module provides utilities for working with variables and floating hypotheses
-- in the context of proof formalization. It handles:
--
-- - Representation of floating hypotheses (variables, terms, well-formed formulas, and contexts)
-- - Disjoint variable restriction (DVR) inference and management
-- - Extraction of variables from formulas and terms
-- - Variable sorting according to a predefined declaration order
module FitchToMM.Variable where

import Data.Containers.ListUtils (nubOrd)
import Data.Foldable
import Data.List (elemIndex, sortOn)
import Data.Maybe (fromMaybe)
import qualified Data.Set as S
import qualified Data.Text as T
import FitchToMM.Context (Context (..))
import FitchToMM.Parser
import qualified Data.Map.Strict as M

-- | A variable name
type Var = T.Text

-- | Floating hypothesis, that is, a hypothesis that a metavariable ranges over
-- a specific grammatical type.
data FHyp
  = VarHyp {fHypName :: Var}
  | TrmHyp {fHypName :: Var}
  | WffHyp {fHypName :: Var}
  | CtxHyp {fHypName :: Var}
  deriving (Ord, Eq, Show)

-- | A disjoint variable restriction (DVR) specifies that two metavariables
-- (identified by their floating hypotheses) must have no variables in common
-- when instantiated.
data DVR = DVR FHyp FHyp
  deriving (Show, Eq, Ord)

-- | A compound DVR represents a group of metavariables that must all be pairwise disjoint.
type CompoundDVR = S.Set FHyp

-- | A function mapping variable names to those variables that are allowed to occur in the
-- WFF or term substituted in.
--
-- E.g., to represent that variables @x@ and @y@ may occur in @φ@ (often denoted with the
-- notation @φ(x,y)@), this should map @"phi"@ to @["x", "y"]@.
type AllowedSubs = Var -> [Var]

-- | Given 'AllowedSubs', determines disjoint variable restrictions (DVRs) for a
-- a WFF.
--
-- A metavariable within the scope of a bound variable should be disjoint from it
-- unless such a subsitution is explicitly allowed by the @AllowedSubs@ function.
--
-- This function also introduces DVRs between all setvars. That is, it enforces a
-- convention against so-called "bundling", which is typically unnecessary for us
-- (compared to e.g., setmm) because our formalization also includes metavariables
-- ranging over terms (of which single variables are a special case) which may
-- contain the same variables.
inferDVRs :: AllowedSubs -> Wff -> [DVR]
inferDVRs allowed wff = nubOrd $ setvarDVRs <> wffDVRs [] wff
  where
    fHyps = S.toList $ varsInWff wff
    setvars = filter isSetvar fHyps
    setvarDVRs = [mkDVR v1 v2 | v1 <- setvars, v2 <- setvars, v1 < v2]
    wffDVRs bound (WffBinOp _ lhs rhs) = wffDVRs bound lhs <> wffDVRs bound rhs
    wffDVRs bound (WffNot expr) = wffDVRs bound expr
    wffDVRs bound (WffMetavar m) = [mkDVR (WffHyp m) (VarHyp v) | v <- bound, v `notElem` allowed m]
    wffDVRs bound (WffQnt _ v expr) = wffDVRs (v : bound) expr
    wffDVRs bound (WffAtom _ args) = foldMap' (trmDVRs bound) args
    wffDVRs bound (WffSub t v expr) = trmDVRs bound t <> wffDVRs (v : bound) expr
    wffDVRs _ WffTrue = []
    wffDVRs _ WffFalse = []
    trmDVRs bound (TrmMetavar m) = [mkDVR (TrmHyp m) (VarHyp v) | v <- bound, v `notElem` allowed m]
    trmDVRs bound (TrmFunc _ args) = foldMap' (trmDVRs bound) args
    trmDVRs bound (TrmSub t v expr) = trmDVRs bound t <> trmDVRs (v : bound) expr
    trmDVRs _ (TrmConst _) = []
    trmDVRs _ (TrmVar _) = []

-- | Group a list of disjoint variable pairs into compound DVRs
--
-- Assumes that the given DVRs adhere to the convention that all setvars are pairwise disjoint
compoundDVRs :: [DVR] -> [CompoundDVR]
compoundDVRs dvrs = filter (\x -> S.size x > 1) $ setvarDVRs : metavarDVRs
  where
    pair (DVR x y) = S.fromList [x, y]
    fHyps = S.unions (map pair dvrs)
    setvarDVRs = S.filter isSetvar fHyps
    metavarDVRs = M.elems $ foldl' insertDVR M.empty dvrs
    
    insertDVR dvrMap dvr@(DVR x y)
      | not $ isSetvar x = M.insertWith S.union x (pair dvr) dvrMap
      | not $ isSetvar y = M.insertWith S.union y (pair dvr) dvrMap
      | otherwise = dvrMap
    

-- | Create a disjoint variable restriction between two floating hypotheses,
-- ensuring consistent canonical ordering
mkDVR :: FHyp -> FHyp -> DVR
mkDVR v1 v2 = if v1 <= v2 then DVR v1 v2 else DVR v2 v1

-- | Extract all floating hypotheses from a context.
--
-- For a relative context (containing the wildcard), includes the context metavariable "...".
-- For an absolute context, returns all hypotheses from all formulas in it.
varsInCtx :: Context -> S.Set FHyp
varsInCtx (RelContext ctx) = S.insert (CtxHyp "...") (foldMap' varsInWff ctx)
varsInCtx (AbsContext ctx) = foldMap' varsInWff ctx

-- | Extract all floating hypotheses from a well-formed formula.
--
-- Returns the set of all variables, term metavariables, and WFF metavariables
-- that appear in the formula.
varsInWff :: Wff -> S.Set FHyp
varsInWff (WffBinOp _ lhs rhs) = varsInWff lhs <> varsInWff rhs
varsInWff (WffNot wff) = varsInWff wff
varsInWff WffTrue = S.empty
varsInWff WffFalse = S.empty
varsInWff (WffQnt _ x wff) = S.insert (VarHyp x) (varsInWff wff)
varsInWff (WffAtom _ args) = varsInLst args
varsInWff (WffMetavar var) = S.singleton $ WffHyp var
varsInWff (WffSub trm x wff) =
  S.insert (VarHyp x) (varsInTrm trm <> varsInWff wff)

-- | Extract all floating hypotheses from a list of terms.
varsInLst :: [Term] -> S.Set FHyp
varsInLst = foldMap' varsInTrm

-- | Extract all floating hypotheses from a term.
varsInTrm :: Term -> S.Set FHyp
varsInTrm (TrmVar x) = S.singleton $ VarHyp x
varsInTrm (TrmFunc _ args) = varsInLst args
varsInTrm (TrmConst _) = S.empty
varsInTrm (TrmMetavar var) = S.singleton $ TrmHyp var
varsInTrm (TrmSub t1 x t2) = (varsInTrm t1) <> (S.singleton $ VarHyp x) <> (varsInTrm t2)

-- | Variables pre-declared globally in our Metamath database
preDeclaredVars :: [FHyp]
preDeclaredVars =
  map CtxHyp ["...", "..._1", "..._2"]
    ++ map WffHyp ["phi", "psi", "chi", "phi_1", "psi_1", "chi_1", "phi_2", "psi_2", "chi_2"]
    ++ map (VarHyp . T.singleton) ['a' .. 'z']
    ++ map TrmHyp ["trm_1", "trm_2", "trm_3", "trm_4", "trm_5"]
    ++ [VarHyp "_a", VarHyp "_x", VarHyp "_trm_1"]

-- | Sort floating hypotheses according to the declaration order in the Metamath database
--
-- Pre-declared variables are sorted first, followed by any other variables in their natural order.
sortVars :: [FHyp] -> [FHyp]
sortVars = sortOn $ \x -> (pos x, x)
  where
    pos x = fromMaybe end (elemIndex x preDeclaredVars)
    end = length preDeclaredVars

isSetvar :: FHyp -> Bool
isSetvar (VarHyp _) = True
isSetvar _ = False

isMetavar :: FHyp -> Bool
isMetavar (WffHyp _) = True
isMetavar (TrmHyp _) = True
isMetavar _ = False

isCtx :: FHyp -> Bool
isCtx (CtxHyp _) = True
isCtx _ = False
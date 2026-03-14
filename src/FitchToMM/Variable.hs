{-# LANGUAGE OverloadedStrings #-}

module FitchToMM.Variable where

import qualified Data.Text as T
import FitchToMM.Context (Context(..))
import qualified Data.Set as S
import FitchToMM.Parser
import Data.Foldable
import Data.List (sortOn, elemIndex, unfoldr)
import Data.Maybe (fromMaybe)
import Data.Containers.ListUtils (nubOrd)
import Data.Ord
import Data.Algorithm.MaximalCliques (getMaximalCliques)

type Var = T.Text

-- Floating hypothesis
data FHyp
  = VarHyp {fHypName :: Var}
  | TrmHyp {fHypName :: Var}
  | WffHyp {fHypName :: Var}
  | CtxHyp {fHypName :: Var}
  deriving (Ord, Eq, Show)

-- Disjoint variable restriction
data DVR = DVR FHyp FHyp
  deriving (Show, Eq, Ord)

type CompoundDVR = S.Set FHyp

type AllowedSubs = T.Text -> [T.Text]

inferDVRs :: AllowedSubs -> Wff -> [DVR]
inferDVRs allowed wff = nubOrd $ setvarDVRs <> wffDVRs [] wff
  where
    fHyps = S.toList $ varsInWff wff
    setvars = filter isSetvar fHyps
    -- Include disjoint variable restrictions between all setvars (that is, we
    -- do not support so-called "bundling" of setvars).
    setvarDVRs = [mkDVR v1 v2 | v1 <- setvars, v2 <- setvars, v1 < v2]
    -- Include disjoint variable restrictions for each metavariable within the
    -- scope of a quantifier or substitution if the bound variable is not
    -- explicitly allowed to occur in the metavariable
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

compoundDVRs :: [FHyp] -> [DVR] -> [CompoundDVR]
compoundDVRs fhyps dvrs = groups ++ S.toList ungrouped
  where
    groups = unfoldr go S.empty
    coveredDVRs = S.unions $ map (cover . S.toList) groups
    remaining = S.difference dvrSet coveredDVRs
    ungrouped = S.map (\(DVR l r) -> S.fromList [l, r]) remaining

    dvrSet = S.fromList dvrs

    cliques =
      sortOn (Down . length) $
        filter (\x -> length x >= 3) $
          getMaximalCliques (\l r -> (mkDVR l r) `S.member` dvrSet) fhyps

    cover :: [FHyp] -> S.Set DVR
    cover xs = S.fromList [mkDVR x y | x <- xs, y <- xs, x < y]

    go :: S.Set DVR -> Maybe (CompoundDVR, S.Set DVR)
    go covered = do
      grouping <- find (\x -> covered `S.disjoint` cover x) cliques
      let newCover = covered <> cover grouping
      return (S.fromList grouping, newCover)

mkDVR :: FHyp -> FHyp -> DVR
mkDVR v1 v2 = if v1 <= v2 then DVR v1 v2 else DVR v2 v1

varsInCtx :: Context -> S.Set FHyp
varsInCtx (RelContext ctx) = S.insert (CtxHyp "...") (foldMap' varsInWff ctx)
varsInCtx (AbsContext ctx) = foldMap' varsInWff ctx

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

varsInLst :: [Term] -> S.Set FHyp
varsInLst = foldMap' varsInTrm

varsInTrm :: Term -> S.Set FHyp
varsInTrm (TrmVar x) = S.singleton $ VarHyp x
varsInTrm (TrmFunc _ args) = varsInLst args
varsInTrm (TrmConst _) = S.empty
varsInTrm (TrmMetavar var) = S.singleton $ TrmHyp var
varsInTrm (TrmSub t1 x t2) = (varsInTrm t1) <> (S.singleton $ VarHyp x) <> (varsInTrm t2)

preDeclaredVars :: [FHyp]
preDeclaredVars =
  map CtxHyp ["...", "..._1", "..._2"]
    ++ map WffHyp ["phi", "psi", "chi", "phi_1", "psi_1", "chi_1", "phi_2", "psi_2", "chi_2"]
    ++ map (VarHyp . T.singleton) ['a' .. 'z']
    ++ map TrmHyp ["trm_1", "trm_2", "trm_3", "trm_4", "trm_5"]
    ++ [VarHyp "_a", VarHyp "_x", VarHyp "_trm_1"]

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
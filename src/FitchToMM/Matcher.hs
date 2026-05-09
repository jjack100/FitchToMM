{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : FitchToMM.Matcher
-- Description : Pattern matching of WFFs against schemas
--
-- This module implements pattern matching for well-formed formulas against schemas (that is, formulas
-- containing metavariables), and handles the resulting substitutions
module FitchToMM.Matcher
  ( Substitution,
    matchTo,
    merge,
    lookupWff,
    lookupTrm,
    lookupVar,
    lookupCtx,
    checkDisjoint,
    singletonVar,
    singletonTrm,
    singletonCtx,
    singletonWff,
    varsInWff,
    varsInTrm,
    varsInLst,
    varsInCtx,
    checkDisjoints,
    mergeFold,
  )
where

import Control.Monad
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.Text as T
import FitchToMM.Parser
import FitchToMM.Variable
import FitchToMM.Context

data Expression = ExprWff Wff | ExprTrm Term | ExprVar T.Text | ExprCtx Context
  deriving (Show, Eq, Ord)

-- | Represents what expressions (e.g., WFFs or terms) are to be substituted for which metavariables
-- in the instantiation of a schema
newtype Substitution = Substitution (M.Map T.Text Expression)
  deriving (Show)

-- | Matches a WFF to a schema, returning just a substitution of metavariables to expressions
-- on success, or nothing on failure.
matchTo :: Wff -> Wff -> Maybe Substitution
-- Any WFF may match to a metavariable
matchTo wff (WffMetavar metavar) = Just $ singletonWff metavar wff
-- Constant symbols must match exactly
matchTo WffTrue WffTrue = Just empty
matchTo WffFalse WffFalse = Just empty
-- Handle subexpressions recursively
matchTo (WffNot w) (WffNot w') = matchTo w w'
matchTo (WffBinOp op w1 w2) (WffBinOp op' w1' w2') | op == op' = do
  lhs <- matchTo w1 w1'
  rhs <- matchTo w2 w2'
  merge lhs rhs
matchTo (WffQnt q v w) (WffQnt q' v' w') | q == q' = do
  wffSub <- matchTo w w'
  merge wffSub (singletonVar v' v)
matchTo (WffAtom p args) (WffAtom p' args') | p == p' = do
  argSubs <- zipWithM matchToTrm args args'
  mergeFold argSubs
matchTo (WffSub t v w) (WffSub t' v' w') = do
  trmSub <- matchToTrm t t'
  let varSub = singletonVar v' v
  wffSub <- matchTo w w'
  mergeFold [trmSub, varSub, wffSub]
-- Otherwise the match fails
matchTo _ _ = Nothing

-- | Matches a term to a schema, returning just a substitution of metavariables to expressions
-- on success, or nothing on failure.
matchToTrm :: Term -> Term -> Maybe Substitution
-- Any term may match to a term metavariable
matchToTrm trm (TrmMetavar metavar) = Just $ singletonTrm metavar trm
-- Any variable may match to a variable
matchToTrm (TrmVar v) (TrmVar v') = Just $ singletonVar v' v
-- Constant symbols must match exactly
matchToTrm (TrmConst c) (TrmConst c') | c == c' = Just empty
-- Handle subexpressions recursively
matchToTrm (TrmFunc f args) (TrmFunc f' args') | f == f' = do
  argSubs <- zipWithM matchToTrm args args'
  mergeFold argSubs
matchToTrm (TrmSub t1 v t2) (TrmSub t1' v' t2') = do
  t1Sub <- matchToTrm t1 t1'
  let varSub = singletonVar v' v
  t2Sub <- matchToTrm t2 t2'
  mergeFold [t1Sub, varSub, t2Sub]
-- Otherwise the match fails
matchToTrm _ _ = Nothing

-- | Returns just the union of two substitutions if the are compatible, or nothing if they are incompatible.
--
-- Two substitutions are incompatible if they map the same metavariable to different expressions.
merge :: Substitution -> Substitution -> Maybe Substitution
merge (Substitution u1) (Substitution u2) = do
  guard $ and $ M.intersectionWith (==) u1 u2
  return $ Substitution $ u1 <> u2

mergeFold :: [Substitution] -> Maybe Substitution
mergeFold = foldM merge empty

-- | Check that a substitution satisfies a disjoint variable restriction (DVR), and if so,
-- returns the set of DVRs that should be propogated.
--
-- If not, returns nothing.
checkDisjoint :: Substitution -> DVR -> Maybe (S.Set DVR)
checkDisjoint (Substitution u) (DVR v1 v2)
  | Just e1 <- u M.!? fHypName v1,
    Just e2 <- u M.!? fHypName v2 = do
      let vars1 = varsInExpr e1
      let vars2 = varsInExpr e2
      guard $ S.disjoint vars1 vars2
      return $ S.map (uncurry mkDVR) (S.cartesianProduct vars1 vars2)
checkDisjoint _ _ = Just S.empty

checkDisjoints :: Substitution -> [DVR] -> Maybe (S.Set DVR)
checkDisjoints sub = fmap mconcat . traverse (checkDisjoint sub)

-- | The empty substitution, mapping no metavaribles to any expressions
empty :: Substitution
empty = Substitution M.empty

singletonWff :: Var -> Wff -> Substitution
singletonWff x wff = Substitution $ M.singleton x (ExprWff wff)

singletonTrm :: Var -> Term -> Substitution
singletonTrm x trm = Substitution $ M.singleton x (ExprTrm trm)

singletonVar :: Var -> Var -> Substitution
singletonVar x var = Substitution $ M.singleton x (ExprVar var)

singletonCtx :: Context -> Substitution
singletonCtx ctx = Substitution $ M.singleton "..." (ExprCtx ctx)

lookupWff :: T.Text -> Substitution -> Maybe Wff
lookupWff metavar (Substitution u)
  | Just (ExprWff wff) <- M.lookup metavar u = Just wff
  | otherwise = Nothing

lookupTrm :: T.Text -> Substitution -> Maybe Term
lookupTrm metavar (Substitution u)
  | Just (ExprTrm trm) <- M.lookup metavar u = Just trm
  | otherwise = Nothing

lookupVar :: T.Text -> Substitution -> Maybe T.Text
lookupVar metavar (Substitution u)
  | Just (ExprVar var) <- M.lookup metavar u = Just var
  | otherwise = Nothing

lookupCtx :: T.Text -> Substitution -> Maybe Context
lookupCtx metavar (Substitution u)
  | Just (ExprCtx ctx) <- M.lookup metavar u = Just ctx
  | otherwise = Nothing

-- Find the set of all variables used in an expression
varsInExpr :: Expression -> S.Set FHyp
varsInExpr (ExprWff wff) = varsInWff wff
varsInExpr (ExprTrm trm) = varsInTrm trm
varsInExpr (ExprVar var) = S.singleton $ VarHyp var
varsInExpr (ExprCtx ctx) = varsInCtx ctx
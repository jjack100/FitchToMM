{-# LANGUAGE OverloadedStrings #-}

module FitchToMM.Replacement
  ( proveReplWff,
    solveForTrm,
    solveForWff,
  )
where

import Control.Monad (guard, zipWithM)
import qualified Control.Monad.Writer.Strict as W
import Data.Monoid (First (..))
import qualified Data.Text as T
import FitchToMM.FitchProof (AllowedSubs)
import FitchToMM.Matcher (varsInLst, varsInTrm, varsInWff)
import FitchToMM.Parser
import FitchToMM.ProofWriter
import FitchToMM.SyntaxProver

-- Given two formulae P and Q, and a variable x, determine what (if any) term
-- t exists such that P replaces x in Q with t
solveForTrm :: AllowedSubs -> Wff -> Wff -> T.Text -> Maybe Term
solveForTrm freeIn wff1 wff2 x = do
  candidate <- findSub wff1 wff2 >>= getFirst
  guard $ succeeded $ proveReplWff freeIn wff1 x wff2 candidate
  return candidate
  where
    findSub :: Wff -> Wff -> Maybe (First Term)
    findSub (WffBinOp op lhs rhs) (WffBinOp op' lhs' rhs') | op == op' = do
      l <- findSub lhs lhs'
      r <- findSub rhs rhs'
      return $ l <> r
    findSub (WffNot w) (WffNot w') = findSub w w'
    findSub WffTrue WffTrue = Just mempty
    findSub WffFalse WffFalse = Just mempty
    findSub (WffAtom p args) (WffAtom p' args')
      | p == p' = mconcat <$> zipWithM findSubTrm args args'
    findSub (WffQnt q y w) (WffQnt q' y' w')
      | q == q', y == y', y /= x = findSub w w'
      | q == q', y == y', y == x, w == w' = Just mempty
    findSub (WffMetavar m) (WffMetavar m') | m == m' = Just mempty
    findSub (WffSub t _ w) w' | w == w' = Just $ First $ Just t
    findSub (WffSub t y w) (WffSub t' y' w') | y == y' = do
      trmSub <- findSubTrm t t'
      wffSub <- findSub w w'
      return $ trmSub <> wffSub
    findSub _ _ = Nothing

    findSubTrm :: Term -> Term -> Maybe (First Term)
    findSubTrm t (TrmVar y) | x == y = Just $ First $ Just t
    findSubTrm (TrmVar y) (TrmVar y') | y == y' = Just mempty
    findSubTrm (TrmFunc f args) (TrmFunc f' args')
      | f == f' = mconcat <$> zipWithM findSubTrm args args'
    findSubTrm (TrmConst c) (TrmConst c') | c == c' = Just mempty
    findSubTrm (TrmMetavar t) (TrmMetavar t') | t == t' = Just mempty
    findSubTrm _ _ = Nothing

-- Given two formulae P and Q, two terms t1 and t2, and a variable x, determine
-- what (if any) formula R exists that has the variable x in those locations
-- where Q swaps t1 for t2 compared to P. I.e., x serves as a placeholder to
-- account for those differences between P and Q.
solveForWff :: AllowedSubs -> Wff -> Wff -> Term -> Term -> T.Text -> Maybe Wff
solveForWff freeIn wff1 wff2 t1 t2 x = do
  candidate <- findSub wff1 wff2
  guard $ succeeded $ proveReplWff freeIn wff1 x candidate t1
  guard $ succeeded $ proveReplWff freeIn wff2 x candidate t2
  return candidate
  where
    findSub :: Wff -> Wff -> Maybe Wff
    findSub w w' | w == w' = Just w
    findSub (WffBinOp op lhs rhs) (WffBinOp op' lhs' rhs') | op == op' = do
      l <- findSub lhs lhs'
      r <- findSub rhs rhs'
      return $ WffBinOp op l r
    findSub (WffNot w) (WffNot w') = WffNot <$> findSub w w'
    findSub (WffAtom p args) (WffAtom p' args')
      | p == p' = WffAtom p <$> zipWithM findSubTrm args args'
    findSub (WffQnt q y w) (WffQnt q' y' w')
      | q == q', y == y' = WffQnt q y <$> findSub w w'
    findSub (WffSub t y w) (WffSub t' y' w')
      | y == y' = do
          trmSub <- findSubTrm t t'
          wffSub <- findSub w w'
          return $ (WffSub trmSub y wffSub)
    findSub _ _ = Nothing

    findSubTrm :: Term -> Term -> Maybe Term
    findSubTrm t t' | t == t1, t' == t2 = Just $ TrmVar x
    findSubTrm t t' | t == t' = Just t
    findSubTrm (TrmFunc f args) (TrmFunc f' args')
      | f == f' = TrmFunc f <$> zipWithM findSubTrm args args'
    findSubTrm _ _ = Nothing

-- Functions to prove a replacement statement once the substitution is known

proveReplWff :: AllowedSubs -> Wff -> T.Text -> Wff -> Term -> ProofWriter
-- Handle trivial case where a variable is replaced with itself
proveReplWff _ w x w' (TrmVar y)
  | x == y,
    w == w' = do
      wPrf <- proveWff w
      xPrf <- proveVar x
      sPrf <- proveStep subIdStep
      return $ wPrf <> xPrf <> sPrf
-- Handle case for where the variable to be replaced does not occur
proveReplWff freeIn w x w' withTrm
  | w == w',
    not $ occursInWff freeIn x w = do
      reqDisjointFor (VarHyp x) (varsInWff w)
      wPrf <- proveWff w
      vPrf <- proveVar x
      tPrf <- proveTrm withTrm
      sPrf <- proveStep subNoneWffStep
      return $ wPrf <> vPrf <> tPrf <> sPrf
-- Handle binary connectives
proveReplWff freeIn (WffBinOp op w1 w2) x (WffBinOp op' w1' w2') withTrm
  | op == op' = do
      ph1Prf <- proveWff w1
      ps1Prf <- proveWff w2
      ph2Prf <- proveWff w1'
      ps2Prf <- proveWff w2'
      vPrf <- proveVar x
      tPrf <- proveTrm withTrm
      let fHyps = ph1Prf <> ps1Prf <> ph2Prf <> ps2Prf <> vPrf <> tPrf
      r1Prf <- proveReplWff freeIn w1 x w1' withTrm
      r2Prf <- proveReplWff freeIn w2 x w2' withTrm
      subPrf <- proveStep $ subBinOpStep op
      return $ fHyps <> r1Prf <> r2Prf <> subPrf
-- Handle the unary connective (negation)
proveReplWff freeIn (WffNot w) x (WffNot w') withTrm = do
  ph1Prf <- proveWff w
  ph2Prf <- proveWff w'
  vPrf <- proveVar x
  tPrf <- proveTrm withTrm
  let fHyps = ph1Prf <> ph2Prf <> vPrf <> tPrf
  rPrf <- proveReplWff freeIn w x w' withTrm
  sPrf <- proveStep subNotStep
  return $ fHyps <> rPrf <> sPrf
-- Handle quantifiers
proveReplWff freeIn (WffQnt q y w) x (WffQnt q' y' w') withTrm
  | q == q',
    y == y',
    y /= x,
    not $ occursInTrm freeIn y withTrm = do
      reqDisjoint (VarHyp y) (VarHyp x)
      reqDisjointFor (VarHyp y) (varsInTrm withTrm)
      phPrf <- proveWff w
      psPrf <- proveWff w'
      xPrf <- proveVar x
      yPrf <- proveVar y
      qPrf <- proveStep $ qntStep q
      tPrf <- proveTrm withTrm
      let fHyps = phPrf <> psPrf <> xPrf <> yPrf <> qPrf <> tPrf
      rPrf <- proveReplWff freeIn w x w' withTrm
      sPrf <- proveStep subQntStep
      return $ fHyps <> rPrf <> sPrf
-- Handle case where the variable is bound
proveReplWff _ (WffQnt q x w) v (WffQnt q' x' w') withTrm
  | q == q',
    x == x',
    w == w',
    x == v = do
      phPrf <- proveWff w
      xPrf <- proveVar x
      qPrf <- proveStep $ qntStep q
      tPrf <- proveTrm withTrm
      sPrf <- proveStep subQntBoundStep
      return $ phPrf <> xPrf <> qPrf <> tPrf <> sPrf
-- Handle predicates
proveReplWff freeIn (WffAtom p args) v (WffAtom p' args') t
  | p == p' = do
      vPrf <- proveVar v
      pPrf <- proveStep $ prdStep p
      tPrf <- proveTrm t
      args1Prf <- proveLst args
      args2Prf <- proveLst args'
      rPrf <- proveReplLst freeIn args v args' t
      subPrf <- proveStep subPrdStep
      return $ vPrf <> pPrf <> tPrf <> args1Prf <> args2Prf <> rPrf <> subPrf
-- Handle substitution
proveReplWff _ (WffSub t x w) x' w' t'
  | t == t',
    x == x',
    w == w' = do
      wPrf <- proveWff w
      xPrf <- proveVar x
      tPrf <- proveTrm t
      sPrf <- proveStep subSub1Step
      return $ wPrf <> xPrf <> tPrf <> sPrf
proveReplWff freeIn ph y (WffSub (TrmVar y') x ph') (TrmVar x')
  | ph == ph',
    x == x',
    y == y',
    not $ occursInWff freeIn y ph =
      do
        reqDisjointFor (VarHyp y) (varsInWff ph)
        phPrf <- proveWff ph
        xPrf <- proveVar x
        yPrf <- proveVar y
        sPrf <- proveStep subSub2Step
        return $ phPrf <> xPrf <> yPrf <> sPrf
proveReplWff freeIn (WffSub t1 y ph) x (WffSub t2 z ps) t3 =
  do
    phPrf <- proveWff ph
    psPrf <- proveWff ps
    xPrf <- proveVar x
    yPrf <- proveVar y
    zPrf <- proveVar z
    t1Prf <- proveTrm t1
    t2Prf <- proveTrm t2
    t3Prf <- proveTrm t3
    let fHyps = phPrf <> psPrf <> xPrf <> yPrf <> zPrf <> t1Prf <> t2Prf <> t3Prf
    r1Prf <- proveReplTrm freeIn t1 x t2 t3
    r2Prf <- proveReplWff freeIn (WffQnt QntFor y ph) x (WffQnt QntFor z ps) t3
    sPrf <- proveStep subSub3Step
    return $ fHyps <> r1Prf <> r2Prf <> sPrf
proveReplWff _ _ _ _ _ = W.lift $ Left Inapplicable

proveReplLst :: AllowedSubs -> [Term] -> T.Text -> [Term] -> Term -> ProofWriter
-- Case for where the variable to be replaced does not occur
proveReplLst freeIn l x l' withTrm
  | l == l',
    not $ any (occursInTrm freeIn x) l = do
      reqDisjointFor (VarHyp x) (varsInLst l)
      vPrf <- proveVar x
      tPrf <- proveTrm withTrm
      lPrf <- proveLst l
      sPrf <- proveStep subNoneTrmStep
      return $ vPrf <> tPrf <> lPrf <> sPrf
-- Recursive case
proveReplLst freeIn lst1 v lst2 withTrm =
  let proveItems [t1] [t2] = proveReplTrm freeIn t1 v t2 withTrm
      proveItems (t1 : ts1) (t2 : ts2) = do
        vPrf <- proveVar v
        t1prf <- proveTrm t1
        t2prf <- proveTrm t2
        t3prf <- proveTrm withTrm
        l1Prf <- provePrependLst ts1
        l2Prf <- provePrependLst ts2
        r1Prf <- proveItems [t1] [t2]
        r2Prf <- proveItems ts1 ts2
        sPrf <- proveStep subTrmStep
        return $ vPrf <> t1prf <> t2prf <> t3prf <> l1Prf <> l2Prf <> r1Prf <> r2Prf <> sPrf
      proveItems _ _ = W.lift $ Left EmptyList
   in -- Reverse the lists before recursing over them because metamath expects
      -- them to be built by appending rather than prepending
      proveItems (reverse lst1) (reverse lst2)

proveReplTrm :: AllowedSubs -> Term -> T.Text -> Term -> Term -> ProofWriter
proveReplTrm freeIn trm1 v trm2 withTrm
  | trm1 == trm2,
    not $ occursInTrm freeIn v trm1 = do
      reqDisjointFor (VarHyp v) (varsInTrm trm1)
      vPrf <- proveVar v
      tPrf <- proveTrm withTrm
      lPrf <- proveLst [trm1]
      sPrf <- proveStep subNoneTrmStep
      return $ vPrf <> tPrf <> lPrf <> sPrf

-- Case where the term is the variable being replaced
proveReplTrm _ trm v (TrmVar x) withTrm
  | trm == withTrm,
    v == x = do
      xPrf <- proveVar x
      tPrf <- proveTrm trm
      rPrf <- proveStep subRepStep
      return $ xPrf <> tPrf <> rPrf
-- Case for where the term is a function of other terms
proveReplTrm freeIn (TrmFunc f args) v (TrmFunc f' args') t
  | f == f' = do
      xPrf <- proveVar v
      fPrf <- proveStep $ funcStep f
      tPrf <- proveTrm t
      args1Prf <- proveLst args
      args2Prf <- proveLst args'
      rPrf <- proveReplLst freeIn args v args' t
      sPrf <- proveStep subFuncStep
      return $ xPrf <> fPrf <> tPrf <> args1Prf <> args2Prf <> rPrf <> sPrf
proveReplTrm _ _ _ _ _ = W.lift $ Left Inapplicable

occursInWff :: AllowedSubs -> T.Text -> Wff -> Bool
occursInWff f x (WffBinOp _ lhs rhs) = occursInWff f x lhs || occursInWff f x rhs
occursInWff f x (WffNot wff) = occursInWff f x wff
occursInWff f x (WffQnt _ y wff) = x == y || occursInWff f x wff
occursInWff f x (WffAtom _ args) = any (occursInTrm f x) args
occursInWff f x (WffMetavar var) = x `elem` f var
occursInWff f x (WffSub trm var wff) = x == var || occursInTrm f x trm || occursInWff f x wff
occursInWff _ _ WffTrue = False
occursInWff _ _ WffFalse = False

occursInTrm :: AllowedSubs -> T.Text -> Term -> Bool
occursInTrm _ x (TrmVar y) = x == y
occursInTrm f x (TrmFunc _ args) = any (occursInTrm f x) args
occursInTrm _ _ (TrmConst _) = False
occursInTrm f x (TrmMetavar var) = x `elem` f var

-- Define the labels and number of mandatory hypotheses they take as they
-- appear in the Metamath database:

subRepStep :: RpnStep
subRepStep = RpnStep 2 "sub.rep"

subNoneWffStep :: RpnStep
subNoneWffStep = RpnStep 3 "sub.none-wff"

subNoneTrmStep :: RpnStep
subNoneTrmStep = RpnStep 3 "sub.none-trm"

subIdStep :: RpnStep
subIdStep = RpnStep 2 "sub.id"

subBinOpStep :: BinOp -> RpnStep
subBinOpStep OpAnd = RpnStep 8 "sub.and"
subBinOpStep OpOr = RpnStep 8 "sub.or"
subBinOpStep OpImplies = RpnStep 8 "sub.implies"
subBinOpStep OpIff = RpnStep 8 "sub.iff"

subNotStep :: RpnStep
subNotStep = RpnStep 5 "sub.not"

subQntStep :: RpnStep
subQntStep = RpnStep 7 "sub.qnt"

subQntBoundStep :: RpnStep
subQntBoundStep = RpnStep 4 "sub.qnt-bound"

subPrdStep :: RpnStep
subPrdStep = RpnStep 6 "sub.prd"

subFuncStep :: RpnStep
subFuncStep = RpnStep 6 "sub.func"

subTrmStep :: RpnStep
subTrmStep = RpnStep 8 "sub.trm"

subSub1Step :: RpnStep
subSub1Step = RpnStep 3 "sub.sub-1"

subSub2Step :: RpnStep
subSub2Step = RpnStep 3 "sub.sub-2"

subSub3Step :: RpnStep
subSub3Step = RpnStep 10 "sub.sub-3"
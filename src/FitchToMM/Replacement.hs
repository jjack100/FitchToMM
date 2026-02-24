{-# LANGUAGE OverloadedStrings #-}

module FitchToMM.Replacement
  ( proveReplWff,
    proveReplTrm,
    solveForTrm,
    solveForWff,
  )
where

import Control.Monad (guard, zipWithM)
import qualified Control.Monad.Writer.Strict as W
import Data.Monoid (First (..))
import qualified Data.Text as T
import FitchToMM.Declarations (AllowedSubs)
import FitchToMM.Nonfree
import FitchToMM.Parser
import FitchToMM.ProofWriter
import FitchToMM.SyntaxProver

type Var = T.Text

-- Given two formulae P and Q, and a variable x, determine what (if any) term
-- t exists such that P replaces x in Q with t
solveForTrm :: AllowedSubs -> Wff -> Wff -> Var -> Maybe Term
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
    findSubTrm (TrmSub t1 _ t2) t2' | t2 == t2' = Just $ First $ Just t1
    findSubTrm (TrmSub t1 y t2) (TrmSub t1' y' t2') | y == y' = do
      trmSub <- findSubTrm t1 t1'
      wffSub <- findSubTrm t2 t2'
      return $ trmSub <> wffSub
    findSubTrm _ _ = Nothing

-- Given two formulae P and Q, two terms t1 and t2, and a variable x, determine
-- what (if any) formula R exists that has the variable x in those locations
-- where Q swaps t1 for t2 compared to P. I.e., x serves as a placeholder to
-- account for those differences between P and Q.
solveForWff :: AllowedSubs -> Wff -> Wff -> Term -> Term -> Var -> Maybe Wff
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

proveReplWff :: AllowedSubs -> Wff -> Var -> Wff -> Term -> ProofWriter
-- Nothing is replaced in a WFF when there are no free occurrences
proveReplWff allowed ph x ph' t
  | ph == ph',
    let nfResult = proveNfWff allowed x ph,
    succeeded nfResult = do
      phPrf <- proveWff ph
      xPrf <- proveVar x
      tPrf <- proveTrm t
      nfPrf <- nfResult
      proveMMStep "sub.wff-none" [phPrf, xPrf, tPrf, nfPrf]
-- Replacing a variable with itself changes nothing
proveReplWff _ ph x ph' (TrmVar x')
  | ph == ph',
    x == x' = do
      phPrf <- proveWff ph
      xPrf <- proveVar x
      proveMMStep "sub.wff-id" [phPrf, xPrf]
-- Case for binary connectives
proveReplWff allowed (WffBinOp op ph1 ps1) x (WffBinOp op' ph2 ps2) t
  | op == op' = do
      ph1Prf <- proveWff ph1
      ps1Prf <- proveWff ps1
      ph2Prf <- proveWff ph2
      ps2Prf <- proveWff ps2
      xPrf <- proveVar x
      tPrf <- proveTrm t
      rPrf1 <- proveReplWff allowed ph1 x ph2 t
      rPrf2 <- proveReplWff allowed ps1 x ps2 t
      let label OpAnd = "sub.wff-and"
          label OpOr = "sub.wff-or"
          label OpImplies = "sub.wff-implies"
          label OpIff = "sub.wff-iff"
      proveMMStep (label op) [ph1Prf, ps1Prf, ph2Prf, ps2Prf, xPrf, tPrf, rPrf1, rPrf2]
-- Case for negation
proveReplWff allowed (WffNot ph1) x (WffNot ph2) t = do
  ph1Prf <- proveWff ph1
  ph2Prf <- proveWff ph2
  xPrf <- proveVar x
  tPrf <- proveTrm t
  rPrf <- proveReplWff allowed ph1 x ph2 t
  proveMMStep "sub.wff-not" [ph1Prf, ph2Prf, xPrf, tPrf, rPrf]
-- Case for predicates
proveReplWff allowed (WffAtom p ts) x (WffAtom p' us) t
  | p == p' = do
      xPrf <- proveVar x
      pPrf <- proveStep $ prdStep p
      tPrf <- proveTrm t
      tsPrf <- proveLst ts
      usPrf <- proveLst us
      rPrf <- proveReplLst allowed ts x us t
      proveMMStep "sub.wff-prd" [xPrf, pPrf, tPrf, tsPrf, usPrf, rPrf]
-- Case for quantifiers
proveReplWff allowed (WffQnt q y ph) x (WffQnt q' y' ps) t
  | q == q',
    y == y',
    x /= y = do
      reqDisjoint (VarHyp x) (VarHyp y)
      phPrf <- proveWff ph
      psPrf <- proveWff ps
      xPrf <- proveVar x
      yPrf <- proveVar y
      qPrf <- proveStep $ qntStep q
      tPrf <- proveTrm t
      nfPrf <- proveNfTrm allowed y t
      rPrf <- proveReplWff allowed ph x ps t
      proveMMStep "sub.wff-qnt" [phPrf, psPrf, xPrf, yPrf, qPrf, tPrf, nfPrf, rPrf]
-- Case for substitution (where variables are the same)
proveReplWff allowed (WffSub t1 x ph) x' (WffSub t2 x'' ph') t3
  | x == x',
    x == x'',
    ph == ph' = do
      phPrf <- proveWff ph
      xPrf <- proveVar x
      t1Prf <- proveTrm t1
      t2Prf <- proveTrm t2
      t3Prf <- proveTrm t3
      rPrf <- proveReplTrm allowed t1 x t2 t3
      proveMMStep "sub.wff-sub-1" [phPrf, xPrf, t1Prf, t2Prf, t3Prf, rPrf]
-- Case for substitution (where variables are distinct)
proveReplWff allowed (WffSub t1 y ph) x (WffSub t2 y' ps) t3
  | y == y',
    x /= y = do
      reqDisjoint (VarHyp x) (VarHyp y)
      phPrf <- proveWff ph
      psPrf <- proveWff ps
      xPrf <- proveVar x
      yPrf <- proveVar y
      t1Prf <- proveTrm t1
      t2Prf <- proveTrm t2
      t3Prf <- proveTrm t3
      nfPrf <- proveNfTrm allowed y t3
      rPrf1 <- proveReplTrm allowed t1 x t2 t3
      rPrf2 <- proveReplWff allowed ph x ps t3
      proveMMStep "sub.wff-sub-2" [phPrf, psPrf, xPrf, yPrf, t1Prf, t2Prf, t3Prf, nfPrf, rPrf1, rPrf2]
-- Case for substitution introduction
proveReplWff _ (WffSub t x ph) x' ph' t'
  | t == t',
    x == x',
    ph == ph' = do
      phPrf <- proveWff ph
      xPrf <- proveVar x
      tPrf <- proveTrm t
      proveMMStep "sub.wff-intr" [phPrf, xPrf, tPrf]
-- Case for substitution elimination
proveReplWff allowed ph y (WffSub (TrmVar y') x ph') (TrmVar x')
  | y == y',
    x == x',
    ph == ph' = do
      phPrf <- proveWff ph
      xPrf <- proveVar x
      yPrf <- proveVar y
      nfPrf <- proveNfWff allowed y ph
      proveMMStep "sub.wff-elim" [phPrf, xPrf, yPrf, nfPrf]
proveReplWff _ _ _ _ _ = W.lift $ Left Inapplicable

proveReplLst :: AllowedSubs -> [Term] -> Var -> [Term] -> Term -> ProofWriter
proveReplLst allowed lst1 x lst2 t3 =
  let proveItems [t1] [t2] = proveReplTrm allowed t1 x t2 t3
      proveItems (t1 : ts) (t2 : us) = do
        xPrf <- proveVar x
        t1Prf <- proveTrm t1
        t2Prf <- proveTrm t2
        t3Prf <- proveTrm t3
        tsPrf <- provePrependLst ts
        usPrf <- provePrependLst us
        rPrf1 <- proveReplTrm allowed t1 x t2 t3
        rPrf2 <- proveItems ts us
        proveMMStep "sub.lst" [xPrf, t1Prf, t2Prf, t3Prf, tsPrf, usPrf, rPrf1, rPrf2]
      proveItems _ _ = W.lift $ Left EmptyList
   in proveItems (reverse lst1) (reverse lst2)

proveReplTrm :: AllowedSubs -> Term -> Var -> Term -> Term -> ProofWriter
-- Replacing a single variable with a term just yields that term
proveReplTrm _ t x (TrmVar x') t'
  | t == t',
    x == x' = do
      xPrf <- proveVar x
      tPrf <- proveTrm t
      proveMMStep "sub.trm-rep" [xPrf, tPrf]
proveReplTrm allowed t1 x t1' t2
  | t1 == t1',
    let nfResult = proveNfTrm allowed x t1,
    succeeded nfResult = do
      xPrf <- proveVar x
      t1Prf <- proveTrm t1
      t2Prf <- proveTrm t2
      nfPrf <- nfResult
      proveMMStep "sub.trm-none" [xPrf, t1Prf, t2Prf, nfPrf]
proveReplTrm _ t x t' (TrmVar x')
  | t == t',
    x == x' = do
      xPrf <- proveVar x
      tPrf <- proveTrm t
      proveMMStep "sub.trm-id" [xPrf, tPrf]
proveReplTrm allowed (TrmFunc f ts) x (TrmFunc f' us) t
  | f == f' = do
      xPrf <- proveVar x
      fPrf <- proveStep $ funcStep f
      tPrf <- proveTrm t
      tsPrf <- proveLst ts
      usPrf <- proveLst us
      rPrf <- proveReplLst allowed ts x us t
      proveMMStep "sub.trm-func" [xPrf, fPrf, tPrf, tsPrf, usPrf, rPrf]
-- Replacement over the substitution operator (case where variables are the same)
proveReplTrm allowed (TrmSub t1 x t3) x' (TrmSub t2 x'' t3') t4
  | x == x',
    x == x'',
    t3 == t3' = do
      xPrf <- proveVar x
      t1Prf <- proveTrm t1
      t2Prf <- proveTrm t2
      t3Prf <- proveTrm t3
      t4Prf <- proveTrm t4
      rPrf <- proveReplTrm allowed t1 x t2 t4
      proveMMStep "sub.trm-sub-1" [xPrf, t1Prf, t2Prf, t3Prf, t4Prf, rPrf]
-- Replacement over the substitution operator (case where variables are distinct)
proveReplTrm allowed (TrmSub t1 y t3) x (TrmSub t2 y' t4) t5
  | y == y',
    x /= y = do
      reqDisjoint (VarHyp x) (VarHyp y)
      xPrf <- proveVar x
      yPrf <- proveVar y
      t1Prf <- proveTrm t1
      t2Prf <- proveTrm t2
      t3Prf <- proveTrm t3
      t4Prf <- proveTrm t4
      t5Prf <- proveTrm t5
      nfPrf <- proveNfTrm allowed y t5
      rPrf1 <- proveReplTrm allowed t1 x t2 t5
      rPrf2 <- proveReplTrm allowed t3 x t4 t5
      proveMMStep "sub.trm-sub-2" [xPrf, yPrf, t1Prf, t2Prf, t3Prf, t4Prf, t5Prf, nfPrf, rPrf1, rPrf2]
-- Case for substitution introduction
proveReplTrm _ (TrmSub t1 x t2) x' t2' t1'
  | t1 == t1',
    t2 == t2',
    x == x' = do
      xPrf <- proveVar x
      t1Prf <- proveTrm t1
      t2Prf <- proveTrm t2
      proveMMStep "sub.trm-intr" [xPrf, t1Prf, t2Prf]
-- Case for substitution elimination
proveReplTrm allowed t y (TrmSub (TrmVar y') x t') (TrmVar x')
  | t == t',
    x == x',
    y == y' = do
      xPrf <- proveVar x
      yPrf <- proveVar y
      tPrf <- proveTrm t
      nfPrf <- proveNfTrm allowed y t
      proveMMStep "sub.trm-elim" [xPrf, yPrf, tPrf, nfPrf]
proveReplTrm _ _ _ _ _ = W.lift $ Left Inapplicable
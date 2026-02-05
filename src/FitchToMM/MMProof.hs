{-# LANGUAGE OverloadedStrings #-}

module FitchToMM.MMProof (Fact (..), MMProof (..), fromFitchProof) where

import Control.Applicative ((<|>))
import Control.Monad
import Control.Monad.Writer.Strict
import Data.List
import qualified Data.Map.Strict as M
import Data.Maybe
import qualified Data.Set as S
import qualified Data.Text as T
import qualified Data.Vector as V
import FitchToMM.Axioms
import FitchToMM.Fact
import FitchToMM.FitchProof
import FitchToMM.Matcher
import FitchToMM.Parser
import FitchToMM.ProofWriter
import FitchToMM.Replacement
import FitchToMM.SyntaxProver

data MMProof
  = MMProof
  { proofLabel :: T.Text,
    -- The "fact" being proved should contain what is necessary for another proof to
    -- reference it (only mandatory hypotheses and disjoint variable restrictions)
    proofFact :: Fact,
    -- All floating hypotheses and disjoint variable restrictions (including optional ones)
    proofFHyps :: [FHyp],
    proofDvrs :: [DVR],
    -- The stack of labels in reverse Polish notation
    proofStack :: RpnStack,
    -- List of mistakes paired with the (0-based) line numbers at which they occur
    proofMistakes :: [(Int, Mistake)]
  }
  deriving (Show)

fromFitchProof :: (T.Text -> Maybe Fact) -> FitchProof -> Maybe MMProof
fromFitchProof lookupThm proof@(FitchProof prfName allowedSubs prems fitchSteps) = do
  -- Return nothing on empty proof
  guard $ not $ null fitchSteps
  return $
    MMProof
      ("thm." <> prfName)
      ( Fact
          finalClaim
          (sortVars $ S.elems mandFHyps)
          prems
          (S.toList mandDVRs)
      )
      (sortVars $ S.elems allFHyps)
      (S.toList dvrs)
      finalRpnStack
      mistakesList
  where
    -- We will build a table containing the subproofs corresponding to each step
    flatProof = V.fromList $ flattenProof proof
    table = V.generate (V.length flatProof) (\i -> step i (flatProof V.! i))

    -- Extract information from the table once it is built
    FlatStep _ finalClaim _ _ _ = V.last flatProof
    finalProof = do
      -- Include those disjoint variable restrictions implied by the omission of
      -- any declared allowed substitutions (in addition to those incurred along
      -- the course of the proof)
      mapM_ (inferDVRsCond allowedSubs) prems
      inferDVRs S.empty allowedSubs finalClaim
      V.last table
    -- Get details relevant to just the fact (the non-extended frame)
    mandFHyps = foldMap varsInCond prems <> varsInWff finalClaim <> (S.singleton $ CtxHyp "...")
    -- Collect any mistakes present among the steps
    mistakes = V.indexed $ fmap getMistake table
    mistakesList = mapMaybe sequence (V.toList mistakes)
    -- Get details from the proof itself
    (finalRpnStack, ProofProps optFHyps dvrs) = runProofWriter finalProof
    allFHyps = mandFHyps <> optFHyps
    -- Identify the mandatory disjoint variable restrictions (those that apply to mandatory vars)
    mandDVRs =
      S.filter
        (\(DVR v1 v2) -> (v1 `S.member` mandFHyps) && (v2 `S.member` mandFHyps))
        dvrs

    -- Function for actually generating the proof at each step
    step :: Int -> FlatStep -> ProofWriter
    -- The proof should not end with any undischarged assumptions
    step i (FlatStep ctx _ _ _ _)
      | i + 1 == V.length flatProof,
        not $ null ctx =
          lift $ Left LeftUndischarged
    -- Handle premises
    step _ (FlatStep _ _ (Premise num) _ _) =
      proveStep $
        RpnStep
          0
          ("thm." <> prfName <> "." <> T.pack (show $ num + 1))
    -- Handle assumptions
    step _ (FlatStep (assump : ctx) wff Assumption _ _) | assump == wff = do
      ctxPrf <- proveCtx ctx
      wffPrf <- proveWff wff
      assumePrf <- proveStep $ RpnStep 2 "axm.assume"
      return $ ctxPrf <> wffPrf <> assumePrf
    step _ (FlatStep _ _ Assumption _ _) = lift $ Left BadAssumption
    -- Handle reiteration
    step i (FlatStep ctx expr Reiteration [citation] _)
      | Line _ <- citation = do
          FlatStep _ cited _ _ _ <- lift $ lookupStep i ctx citation
          unless (expr == cited) (lift $ Left Inapplicable)
          lookupProof i ctx citation
      | otherwise = lift $ Left Inapplicable
    step _ (FlatStep _ _ Reiteration _ _) = lift $ Left BadCiteCount
    -- For rules that have two versions, provide an alias that tries both alternatives
    step i (FlatStep ctx expr (Reference "axm.or-intr") cites pos) =
      let res1 = step i (FlatStep ctx expr (Reference "axm.or-intr-1") cites pos)
          res2 = step i (FlatStep ctx expr (Reference "axm.or-intr-2") cites pos)
       in if succeeded res1 then res1 else res2
    step i (FlatStep ctx expr (Reference "axm.and-elim") cites pos) =
      let res1 = step i (FlatStep ctx expr (Reference "axm.and-elim-1") cites pos)
          res2 = step i (FlatStep ctx expr (Reference "axm.and-elim-2") cites pos)
       in if succeeded res1 then res1 else res2
    step i (FlatStep ctx expr (Reference "axm.iff-elim") cites pos) =
      let res1 = step i (FlatStep ctx expr (Reference "axm.iff-elim-1") cites pos)
          res2 = step i (FlatStep ctx expr (Reference "axm.iff-elim-2") cites pos)
       in if succeeded res1 then res1 else res2
    step i (FlatStep ctx expr (Reference "axm.eq-elim") cites pos) =
      let res1 = step i (FlatStep ctx expr (Reference "axm.eq-elim-1") cites pos)
          res2 = step i (FlatStep ctx expr (Reference "thm.eq-elim-2") cites pos)
       in if succeeded res1 then res1 else res2
    -- Handle application of a referenced rule
    step i (FlatStep ctx wff (Reference ref) citations _) = do
      Fact claim fHyps eHyps dConds <- try (lookupFact ref) UnrecognizedFact
      -- Verify we are citing the correct number of lines for the fact we are referencing
      unless (length citations == length eHyps) (lift $ Left BadCiteCount)
      citedSteps <- lift $ mapM (lookupStep i ctx) citations
      -- See if a valid substitution exists
      let ctxSub = singletonCtx ctx
      stmtSub <- try (wff `matchTo` claim) Inapplicable
      hypSubs <- try (zipWithM verifyEHyp citedSteps eHyps) Inapplicable
      merged <- try (mergeFold $ ctxSub : stmtSub : hypSubs) Inapplicable
      -- Handle rules requiring replacement statements as special cases
      let result = case ref of
            "axm.forall-intr" -> proveForallI allowedSubs merged
            "axm.exists-intr" -> proveExistsI allowedSubs merged
            "axm.forall-elim" -> proveForallE allowedSubs merged
            "axm.exists-elim" -> proveExistsE allowedSubs merged
            "axm.eq-elim-1" -> proveEqE allowedSubs merged
            "thm.eq-elim-2" -> proveEqE allowedSubs merged
            _ -> Just (merged, [])
      (fullSub, replacements) <- try result Inapplicable
      applyDConds fullSub dConds
      fHypPrfs <- mapM (proveFHyp fullSub) fHyps
      replPrfs <- sequence replacements
      eHypPrfs <- mapM (lookupProof i ctx) citations
      let numMandHyps = length fHyps + length eHyps + length replacements
      labelProof <- proveStep $ RpnStep numMandHyps ref
      return $
        mconcat fHypPrfs
          <> mconcat replPrfs
          <> mconcat eHypPrfs
          <> labelProof

    -- Lookup a past step given a citation
    lookupStep :: Int -> Context -> Citation -> Either Mistake FlatStep
    lookupStep i ctx cite@(Line line)
      | Just err <- checkAccessibility flatProof i cite = Left err
      | otherwise =
          -- Update the context with the given one
          let FlatStep _ wff rule cites pos = flatProof V.! line
           in Right $ FlatStep ctx wff rule cites pos
    lookupStep i _ cite@(Range _ to)
      | Just err <- checkAccessibility flatProof i cite = Left err
      | otherwise = Right $ flatProof V.! to

    -- Lookup the proof of a past step given a citation
    lookupProof :: Int -> Context -> Citation -> ProofWriter
    lookupProof i ctx cite@(Line line)
      | Just err <- checkAccessibility flatProof i cite = lift $ Left err
      | otherwise = do
          -- Try to thin it into the given context if necessary
          let prf = table V.! line
              stp = flatProof V.! line
          -- On failure, run the proof writer to just emit a "?"
          base <- if succeeded prf then prf else pure $ fst $ runProofWriter prf
          proveThin ctx stp base
    lookupProof i _ cite@(Range _ to)
      | Just err <- checkAccessibility flatProof i cite = lift $ Left err
      | otherwise =
          let prf = table V.! to
           in if succeeded prf then prf else pure $ fst $ runProofWriter prf

    lookupFact ref = (axioms M.!? ref) <|> (lookupThm ref)

-- Apply disjoint variable conditions
applyDConds :: Substitution -> [DVR] -> PropWriter
applyDConds sub dConds = do
  disjointVars <- try (checkDisjoints sub dConds) Inapplicable
  mapM_ applyDVR disjointVars

-- Check if a line or subproof is accessible to (able to be legitimately cited by) a given line
checkAccessibility :: V.Vector FlatStep -> Int -> Citation -> Maybe Mistake
checkAccessibility steps i (Line line)
  | isNothing (steps V.!? line) = Just CitesNonexistent
  | line > i = Just CitesLater
  | i == line = Just CitesSelf
  | FlatStep _ _ _ _ (_ : fromPath) <- steps V.! line,
    FlatStep _ _ _ _ atPath <- steps V.! i,
    not $ fromPath `isSuffixOf` atPath =
      Just CitesDischarged
  | otherwise = Nothing
checkAccessibility table i (Range from to)
  | isNothing (table V.!? from) = Just CitesNonexistent
  | isNothing (table V.!? to) = Just CitesNonexistent
  | from > to = Just NotASubproof
  -- The start of the range should be the start of a subproof
  | FlatStep _ _ _ _ (x : _) <- table V.! from,
    x /= 0 =
      Just NotASubproof
  -- The start and end of the range should be on the same level
  | FlatStep _ _ _ _ (_ : fromPath) <- table V.! from,
    FlatStep _ _ _ _ (_ : toPath) <- table V.! to,
    fromPath /= toPath =
      Just NotASubproof
  -- The subproof should not end after the line citing it
  | to > i = Just CitesLater
  -- The subproof should not contain the line citing it
  | i >= from && i <= to = Just CitesSelf
  -- The line should be discharging one level of nesting
  | FlatStep _ _ _ _ (_ : _ : toPath) <- table V.! to,
    FlatStep _ _ _ _ (_ : atPath) <- table V.! i,
    toPath /= atPath =
      Just CitesDischarged
  | otherwise = Nothing

proveForallI :: AllowedSubs -> Substitution -> Maybe (Substitution, [ProofWriter])
proveForallI allowed sub = do
  -- We should already know the substitutions for φ,ψ,x
  phi <- lookupWff "phi" sub
  psi <- lookupWff "psi" sub
  x <- lookupVar "x" sub
  -- Solve for the substitution needed for 'a', or default to a dummy variable
  -- to try the trivial case where x does not occur in ψ
  let a = fromMaybe "_a" (solveForVar allowed psi phi x)
  fullSub <- merge sub $ singletonVar "a" a
  let replPrf = proveReplWff allowed psi a phi (TrmVar x)
  return (fullSub, [replPrf])

proveExistsI :: AllowedSubs -> Substitution -> Maybe (Substitution, [ProofWriter])
proveExistsI allowed sub = do
  -- We should already know the substitutions for φ,ψ,x
  phi <- lookupWff "phi" sub
  psi <- lookupWff "psi" sub
  x <- lookupVar "x" sub
  -- Solve for the substitution needed for trm_1
  let trm_1 = fromMaybe (TrmMetavar "_trm_1") (solveForTrm allowed phi psi x)
  fullSub <- merge sub $ singletonTrm "trm_1" trm_1
  let replPrf = proveReplWff allowed phi x psi trm_1
  return (fullSub, [replPrf])

proveForallE :: AllowedSubs -> Substitution -> Maybe (Substitution, [ProofWriter])
proveForallE allowed sub = do
  -- We should already know the substitutions for φ,ψ,x
  phi <- lookupWff "phi" sub
  psi <- lookupWff "psi" sub
  x <- lookupVar "x" sub
  -- Solve for the substitution needed for trm_1
  let trm_1 = fromMaybe (TrmMetavar "_trm_1") (solveForTrm allowed psi phi x)
  fullSub <- merge sub $ singletonTrm "trm_1" trm_1
  let replPrf = proveReplWff allowed psi x phi trm_1
  return (fullSub, [replPrf])

proveExistsE :: AllowedSubs -> Substitution -> Maybe (Substitution, [ProofWriter])
proveExistsE allowed sub = do
  -- We should already know the substitutions for φ,ψ,x
  phi <- lookupWff "phi" sub
  psi <- lookupWff "psi" sub
  x <- lookupVar "x" sub
  -- Solve for the substitution needed for a
  let aTrm = fromMaybe (TrmVar "_a") (solveForTrm allowed psi phi x)
  -- a must be a variable
  a <- case aTrm of (TrmVar name) -> Just name; _ -> Nothing
  fullSub <- merge sub $ singletonVar "a" a
  let replPrf = proveReplWff allowed psi x phi aTrm
  return (fullSub, [replPrf])

proveEqE :: AllowedSubs -> Substitution -> Maybe (Substitution, [ProofWriter])
proveEqE allowed sub = do
  -- We should already know the substitutions for φ,ψ,trm_1,trm_2
  phi <- lookupWff "phi" sub
  psi <- lookupWff "psi" sub
  trm_1 <- lookupTrm "trm_1" sub
  trm_2 <- lookupTrm "trm_2" sub
  -- Solve for the substitution needed for χ
  chi <- solveForWff allowed phi psi trm_1 trm_2 "_x"
  fullSub <- mergeFold [sub, singletonWff "chi" chi, singletonVar "x" "_x"]
  let replPrf1 = proveReplWff allowed phi "_x" chi trm_1
  let replPrf2 = proveReplWff allowed psi "_x" chi trm_2
  return (fullSub, [replPrf1, replPrf2])

proveFHyp :: Substitution -> FHyp -> ProofWriter
proveFHyp sub (WffHyp hyp) | Just wff <- lookupWff hyp sub = proveWff wff
proveFHyp sub (VarHyp hyp) | Just var <- lookupVar hyp sub = proveVar var
proveFHyp sub (TrmHyp hyp) | Just trm <- lookupTrm hyp sub = proveTrm trm
proveFHyp sub (CtxHyp hyp) | Just ctx <- lookupCtx hyp sub = proveCtx ctx
proveFHyp _ hyp = proveMetavar $ markInternal hyp

-- Tries to thin a step to match a given context
proveThin :: Context -> FlatStep -> RpnStack -> ProofWriter
proveThin toCtx (FlatStep fromCtx _ _ _ _) base
  | fromCtx == toCtx = pure base
proveThin (psi : ctx) stp@(FlatStep _ phi _ _ _) base = do
  ctxPrf <- proveCtx ctx
  phiPrf <- proveWff phi
  psiPrf <- proveWff psi
  prev <- proveThin ctx stp base
  thinPrf <- proveStep $ RpnStep 4 "axm.thin"
  return $ ctxPrf <> phiPrf <> psiPrf <> prev <> thinPrf
proveThin _ _ _ = lift $ Left Inapplicable

-- Check that a cited step matches an essential hypothesis, and if so return the substitution
verifyEHyp :: FlatStep -> Condition -> Maybe Substitution
verifyEHyp (FlatStep ctx wff _ _ _) (Condition Nothing hyp) = do
  let ctxSub = singletonCtx ctx
  hypSub <- wff `matchTo` hyp
  merge ctxSub hypSub
verifyEHyp (FlatStep (assump : ctx) wff _ _ _) (Condition (Just sup) hyp) = do
  let ctxSub = singletonCtx ctx
  supSub <- assump `matchTo` sup
  hypSub <- wff `matchTo` hyp
  mergeFold [ctxSub, supSub, hypSub]
verifyEHyp _ _ = Nothing

-- Add any disjoint variable restrictions implied by the omission of declared
-- allowed substitutions. A variable should be disjoint from any variables
-- bound within its scope unless explicitly allowed.
inferDVRs :: S.Set FHyp -> AllowedSubs -> Wff -> PropWriter
inferDVRs bound allowed (WffBinOp _ lhs rhs) = do
  inferDVRs bound allowed lhs
  inferDVRs bound allowed rhs
inferDVRs bound allowed (WffNot wff) = inferDVRs bound allowed wff
inferDVRs _ _ (WffFalse) = pure ()
inferDVRs _ _ (WffTrue) = pure ()
inferDVRs bound allowed (WffMetavar var) =
  let allowedSubs = S.fromList (VarHyp <$> allowed var)
      disjoint = S.difference bound allowedSubs
   in reqDisjointFor (WffHyp var) disjoint
inferDVRs bound allowed (WffQnt _ var wff) =
  inferDVRs (S.insert (VarHyp var) bound) allowed wff
inferDVRs bound allowed (WffAtom _ args) =
  mapM_ (inferDVRsTrm bound allowed) args
inferDVRs bound allowed (WffSub trm var wff) = do
  inferDVRsTrm bound allowed trm
  -- Also treat variables subject to substitution as "bound" for our our
  -- purposes here (within the scope of where the substitution occurs)
  inferDVRs (S.insert (VarHyp var) bound) allowed wff

inferDVRsTrm :: S.Set FHyp -> AllowedSubs -> Term -> PropWriter
inferDVRsTrm bound allowed (TrmMetavar var) =
  let allowedSubs = S.fromList (VarHyp <$> allowed var)
      disjoint = S.difference bound allowedSubs
   in reqDisjointFor (TrmHyp var) disjoint
inferDVRsTrm bound _ (TrmVar var) =
  reqDisjointFor (VarHyp var) (S.delete (VarHyp var) bound)
inferDVRsTrm bound allowed (TrmFunc _ args) =
  mapM_ (inferDVRsTrm bound allowed) args
inferDVRsTrm _ _ (TrmConst _) = pure ()

inferDVRsCond :: AllowedSubs -> Condition -> PropWriter
inferDVRsCond allowed (Condition (Just sup) hyp) = do
  inferDVRs S.empty allowed sup
  inferDVRs S.empty allowed hyp
inferDVRsCond allowed (Condition Nothing hyp) =
  inferDVRs S.empty allowed hyp

varsInCond :: Condition -> S.Set FHyp
varsInCond (Condition (Just sup) hyp) = varsInWff sup <> varsInWff hyp
varsInCond (Condition Nothing hyp) = varsInWff hyp

try :: (MonadTrans t) => Maybe a1 -> a2 -> t (Either a2) a1
try val err = lift $ maybe (Left err) Right val
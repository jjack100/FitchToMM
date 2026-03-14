{-# LANGUAGE OverloadedStrings #-}

module FitchToMM.MMProof (Fact (..), MMProof (..), fromFitchProof, fromEquivProof) where

import Control.Monad
import Data.Foldable (asum)
import Data.List
import Data.Maybe
import qualified Data.Set as S
import qualified Data.Text as T
import qualified Data.Vector as V
import FitchToMM.Declarations
import FitchToMM.Equivalence (proveEquiv)
import FitchToMM.FitchProof
import FitchToMM.Matcher
import FitchToMM.Nonfree
import FitchToMM.Parser
import FitchToMM.ProofWriter
import FitchToMM.Replacement
import FitchToMM.SyntaxProver
import FitchToMM.Variable
import FitchToMM.Context

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
    proofMistakes :: MistakesList
  }
  deriving (Show)

-- List of mistakes paired with the (0-based) line numbers at which they occur
type MistakesList = [(Int, Mistake)]

fromFitchProof :: DeclMap -> FitchProof -> Maybe MMProof
fromFitchProof decls prf@(FitchProof label allowed prems steps) = do
  guard $ not $ null steps
  (prfWriter, mistakes) <- proveFlatSteps decls allowed flat
  let (fact, fHyps, dvrs, rpnStack) = proofInfo prfWriter ctx prems conclusion mandFHyps
  return $ MMProof label fact fHyps dvrs rpnStack mistakes
  where
    ctx = RelContext []
    flat = flattenProof prf
    FlatStep _ conclusion _ _ _ = last flat
    mandFHyps = foldMap varsInCond prems <> varsInWff conclusion <> (S.singleton $ CtxHyp "...")

fromEquivProof :: DeclMap -> EquivProof -> Maybe MMProof
fromEquivProof decls prf@(EquivProof label allowed steps) = do
  guard $ not $ null steps
  (prfWriter, mistakes) <- proveFlatSteps decls allowed flat
  let (fact, fHyps, dvrs, rpnStack) = proofInfo prfWriter ctx [] conclusion mandFHyps
  return $ MMProof label fact fHyps dvrs rpnStack mistakes
  where
    ctx = AbsContext []
    flat = flattenEquivProof prf
    FlatStep _ conclusion _ _ _ = last flat
    mandFHyps = varsInWff conclusion

proofInfo :: ProofWriter -> Context -> [Condition] -> Wff -> S.Set FHyp -> (Fact, [FHyp], [DVR], RpnStack)
proofInfo prfWriter ctx conds conclusion mandFHyps =
  (Fact ctx conclusion conds (sortVars $ S.elems mandFHyps) mandDVRs, allFHyps, dvrList, rpnStack)
  where
    (rpnStack, ProofProps optFHyps dvrs) = runProofWriter prfWriter
    allFHyps = sortVars $ S.elems $ mandFHyps <> optFHyps
    mandDVRs = S.toList $ getMandDVRs mandFHyps dvrs
    dvrList = S.toList dvrs

proveFlatSteps :: DeclMap -> AllowedSubs -> [FlatStep] -> Maybe (ProofWriter, MistakesList)
proveFlatSteps decls allowed flatSteps = do
  -- Return nothing on empty proof
  guard $ not $ null flatSteps
  return (finalProof, mistakesList)
  where
    -- We will build a table containing the subproofs corresponding to each step
    flatProof = V.fromList flatSteps
    table = V.generate (V.length flatProof) (\i -> step i (flatProof V.! i))

    -- Get the proof from the last entry in the table
    finalProof = do
      -- Include those disjoint variable restrictions implied by the omission of
      -- any declared allowed substitutions (in addition to those incurred along
      -- the course of the proof)
      let getDvrs (FlatStep _ wff _ _ _) = inferDVRs allowed wff
          dvrs = concatMap getDvrs flatSteps
      mapM_ applyDVR dvrs
      V.last table

    -- Collect any mistakes present among the steps
    mistakes = V.indexed $ fmap getMistake table
    mistakesList = mapMaybe sequence (V.toList mistakes)

    -- Function for generating the proof at each step
    step :: Int -> FlatStep -> ProofWriter
    -- The proof should not end with any undischarged assumptions
    step i (FlatStep ctx _ _ _ _)
      | i + 1 == V.length flatProof,
        not $ nullCtx ctx =
          fromMistake LeftUndischarged
    -- Handle premises
    step _ (FlatStep _ _ (Premise num) _ _) =
      proveLocalStep $ RpnStep 0 (T.show $ num + 1)
    -- Handle assumptions
    step _ (FlatStep ctx wff Assumption _ _)
      | Just (assump, rest) <- unconsCtx ctx,
        assump == wff = do
          ctxPrf <- proveCtx rest
          wffPrf <- proveWff wff
          assumePrf <- proveStep $ RpnStep 2 "axm.assume"
          return $ ctxPrf <> wffPrf <> assumePrf
    step _ (FlatStep _ _ Assumption _ _) = fromMistake BadAssumption
    -- Handle reiteration
    step i (FlatStep ctx expr Reiteration [citation] _)
      | Line _ <- citation = do
          FlatStep _ cited _ _ _ <- lift $ lookupStep i ctx citation
          unless (expr == cited) (fromMistake Inapplicable)
          lookupProof i ctx citation
      | otherwise = fromMistake Inapplicable
    step _ (FlatStep _ _ Reiteration _ _) = fromMistake BadCiteCount
    -- For rules that have multiple versions, provide an alias that tries alternatives
    step i fs@(FlatStep _ _ (Reference "axm.or-intr") _ _) = choice i fs ["axm.or-intr-1", "axm.or-intr-2"]
    step i fs@(FlatStep _ _ (Reference "axm.and-elim") _ _) = choice i fs ["axm.and-elim-1", "axm.and-elim-2"]
    step i fs@(FlatStep _ _ (Reference "axm.iff-elim") _ _) = choice i fs ["axm.iff-elim-1", "axm.iff-elim-2"]
    step i fs@(FlatStep _ _ (Reference "axm.eq-elim") _ _) = choice i fs ["axm.eq-elim-1", "thm.eq-elim-2"]
    -- Handle references to the definition of substitution
    step i fs@(FlatStep _ _ (Reference "def.sub-wff") _ _) = proveDef (proveDefSubWff allowed) i fs
    step i fs@(FlatStep _ _ (Reference "def.sub-trm") _ _) = proveDef (proveDefSubTrm allowed) i fs
    -- Handle application of a referenced rule
    step i fs@(FlatStep ctx wff (Reference ref) citations _)
      | Just (Fact (RelContext []) claim eHyps fHyps dvr) <- lookupFact ref = do
          -- Verify we are citing the correct number of lines for the fact we are referencing
          unless (length citations == length eHyps) (fromMistake BadCiteCount)
          citedSteps <- lift $ mapM (lookupStep i ctx) citations
          -- See if a valid substitution exists
          let ctxSub = singletonCtx ctx
          stmtSub <- try (wff `matchTo` claim) Inapplicable
          hypSubs <- try (zipWithM verifyEHyp citedSteps eHyps) Inapplicable
          merged <- try (mergeFold $ ctxSub : stmtSub : hypSubs) Inapplicable
          -- Handle rules requiring replacement statements as special cases
          let result = case ref of
                "axm.forall-intr" -> proveForallI allowed merged
                "axm.exists-intr" -> proveExistsI allowed merged
                "axm.forall-elim" -> proveForallE allowed merged
                "axm.exists-elim" -> proveExistsE allowed merged
                "axm.eq-elim-1" -> proveEqE allowed merged
                "thm.eq-elim-2" -> proveEqE allowed merged
                _ -> Just (merged, [])
          (fullSub, extraHyps) <- try result Inapplicable
          applyDVRs fullSub dvr
          fHypPrfs <- mapM (proveFHyp fullSub) fHyps
          extraPrfs <- sequence extraHyps
          eHypPrfs <- mapM (lookupProof i ctx) citations
          proveMMStep ref (concat [fHypPrfs, extraPrfs, eHypPrfs])
      | Just (Definition definiendum definiens fHyps dvr) <- lookupDef ref =
          let proveDefStmt fromDefiniendum fromDefiniens = do
                sub1 <- try (fromDefiniendum `matchTo` definiendum) Inapplicable
                sub2 <- try (fromDefiniens `matchTo` definiens) Inapplicable
                fullSub <- try (merge sub1 sub2) Inapplicable
                applyDVRs fullSub dvr
                fHypPrfs <- mapM (proveFHyp fullSub) fHyps
                labelProof <- proveStep $ RpnStep (length fHypPrfs) ref
                return $ mconcat fHypPrfs <> labelProof
           in proveDef proveDefStmt i fs
      | Just eqv <- lookupEqv ref = proveEqv eqv ref i fs
      | otherwise = fromMistake UnrecognizedFact

    -- Prove the introduction or elimination of a definition
    proveDef :: (Definiendum -> Definiens -> ProofWriter) -> Int -> FlatStep -> ProofWriter
    proveDef proveDefStmt i (FlatStep ctx wff _ [citation] _) = do
      (FlatStep _ cited _ _ _) <- lift $ lookupStep i ctx citation
      let intrPrf = prove "axm.def-intr" wff cited
          elimPrf = prove "axm.def-elim" cited wff
      alts [intrPrf, elimPrf]
      where
        fHyps = [CtxHyp "...", WffHyp "phi", WffHyp "psi"]
        prove label ph ps = do
          sub <- try (mergeFold [singletonCtx ctx, singletonWff "phi" ph, singletonWff "psi" ps]) Inapplicable
          fHypPrfs <- mapM (proveFHyp sub) fHyps
          citedPrf <- lookupProof i ctx citation
          defSubPrf <- proveDefStmt ph ps
          proveMMStep label $ fHypPrfs ++ [defSubPrf, citedPrf]
    proveDef _ _ _ = fromMistake BadCiteCount

    proveEqv :: EquivFact -> Label -> Int -> FlatStep -> ProofWriter
    proveEqv eqv ref i (FlatStep ctx wff _ [citation] _) = do
      FlatStep _ citedWff _ _ _ <- lift $ lookupStep i ctx citation
      ctxPrf <- proveCtx ctx
      wffCitedPrf <- proveWff citedWff
      wffPrf <- proveWff wff
      citedPrf <- lookupProof i ctx citation
      let prf1 = do
            eqvPrf <- proveEquiv eqv ref ctx citedWff wff
            proveMMStep "axm.iff-elim-1" [ctxPrf, wffCitedPrf, wffPrf, eqvPrf, citedPrf]
          prf2 = do
            eqvPrf <- proveEquiv eqv ref ctx wff citedWff
            proveMMStep "axm.iff-elim-2" [ctxPrf, wffPrf, wffCitedPrf, eqvPrf, citedPrf]
      alts [prf1, prf2]
    proveEqv _ _ _ _ = fromMistake BadCiteCount

    -- Try several possible references, and take the first that succeeds
    choice :: Int -> FlatStep -> [T.Text] -> ProofWriter
    choice i (FlatStep ctx expr _ cites pos) choices =
      let apply jus = step i (FlatStep ctx expr jus cites pos)
          results = map (apply . Reference) choices
       in alts results

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
      | Just err <- checkAccessibility flatProof i cite = fromMistake err
      | otherwise = do
          -- Try to thin it into the given context if necessary
          let prf = table V.! line
              stp = flatProof V.! line
          -- On failure, run the proof writer to just emit a "?"
          basePrf <- alts [prf, pure $ fst $ runProofWriter prf]
          proveThin ctx stp basePrf
    lookupProof i _ cite@(Range _ to)
      | Just err <- checkAccessibility flatProof i cite = fromMistake err
      | otherwise =
          let prf = table V.! to
           in alts [prf, pure $ fst $ runProofWriter prf]

    lookupFact = findFact decls
    lookupDef = findDefinition decls
    lookupEqv = findEquiv decls

-- Apply disjoint variable conditions
applyDVRs :: Substitution -> [DVR] -> PropWriter
applyDVRs sub fromDVRs = do
  toDVRs <- try (checkDisjoints sub fromDVRs) Inapplicable
  mapM_ applyDVR toDVRs

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
  ctx <- lookupCtx "..." sub
  -- Solve for the substitution needed for 'a', also trying a dummy variable
  -- _a for the trivial case where x does not occur in ψ
  let nfPrf2 = proveNfWff allowed x phi
      candidates = varsInWff phi <> varsInWff psi <> (S.singleton $ VarHyp "_a")
      tryCandidate cand = do
        guard $ isSetvar cand
        let candName = fHypName cand
            nfPrf1 = proveNfCtx allowed candName ctx
            rPrf = proveReplWff allowed psi candName phi (TrmVar x)
        guard $ succeeded nfPrf1
        guard $ succeeded rPrf
        fullSub <- merge sub $ singletonVar "a" candName
        return $ (fullSub, [nfPrf1, nfPrf2, rPrf])
  asum $ map tryCandidate $ S.toList candidates

proveExistsI :: AllowedSubs -> Substitution -> Maybe (Substitution, [ProofWriter])
proveExistsI allowed sub = do
  -- We should already know the substitutions for φ,ψ,x
  phi <- lookupWff "phi" sub
  psi <- lookupWff "psi" sub
  x <- lookupVar "x" sub
  -- Solve for the substitution needed for trm_1
  let trm_1 = fromMaybe (TrmMetavar "_trm_1") (solveForTrm allowed phi psi x)
  fullSub <- merge sub $ singletonTrm "trm_1" trm_1
  let rPrf = proveReplWff allowed phi x psi trm_1
  return (fullSub, [rPrf])

proveForallE :: AllowedSubs -> Substitution -> Maybe (Substitution, [ProofWriter])
proveForallE allowed sub = do
  -- We should already know the substitutions for φ,ψ,x
  phi <- lookupWff "phi" sub
  psi <- lookupWff "psi" sub
  x <- lookupVar "x" sub
  -- Solve for the substitution needed for trm_1
  let trm_1 = fromMaybe (TrmMetavar "_trm_1") (solveForTrm allowed psi phi x)
  fullSub <- merge sub $ singletonTrm "trm_1" trm_1
  let rPrf = proveReplWff allowed psi x phi trm_1
  return (fullSub, [rPrf])

proveExistsE :: AllowedSubs -> Substitution -> Maybe (Substitution, [ProofWriter])
proveExistsE allowed sub = do
  -- We should already know the substitutions for φ,ψ,χ,x
  phi <- lookupWff "phi" sub
  psi <- lookupWff "psi" sub
  chi <- lookupWff "chi" sub
  x <- lookupVar "x" sub
  ctx <- lookupCtx "..." sub
  -- Solve for the substitution needed for a
  let aTrm = fromMaybe (TrmVar "_a") (solveForTrm allowed psi phi x)
  -- a must be a variable
  a <- case aTrm of (TrmVar name) -> Just name; _ -> Nothing
  fullSub <- merge sub $ singletonVar "a" a
  let nfPrf1 = proveNfCtx allowed a ctx
      nfPrf2 = proveNfWff allowed a phi
      nfPrf3 = proveNfWff allowed a chi
      rPrf = proveReplWff allowed psi x phi aTrm
  return (fullSub, [nfPrf1, nfPrf2, nfPrf3, rPrf])

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
  let rPrf1 = proveReplWff allowed phi "_x" chi trm_1
  let rPrf2 = proveReplWff allowed psi "_x" chi trm_2
  return (fullSub, [rPrf1, rPrf2])

proveDefSubWff :: AllowedSubs -> Wff -> Wff -> ProofWriter
proveDefSubWff allowedSubs definiendum definiens = do
  sub1 <- try (definiendum `matchTo` WffSub (TrmMetavar "trm_1") "x" (WffMetavar "phi")) Inapplicable
  sub2 <- try (merge sub1 (singletonWff "psi" definiens)) Inapplicable
  -- Get the proofs for the floating hypotheses
  let fHyps = [WffHyp "phi", WffHyp "psi", VarHyp "x", TrmHyp "trm_1"]
  fHypPrfs <- mapM (proveFHyp sub2) fHyps
  -- Get the proof for the replacement statement
  phi <- try (lookupWff "phi" sub2) Inapplicable
  psi <- try (lookupWff "psi" sub2) Inapplicable
  x <- try (lookupVar "x" sub2) Inapplicable
  trm_1 <- try (lookupTrm "trm_1" sub2) Inapplicable
  replPrf <- proveReplWff allowedSubs psi x phi trm_1
  -- Prove the definition statement
  proveMMStep "def.sub-wff" (fHypPrfs ++ [replPrf])

proveDefSubTrm :: AllowedSubs -> Wff -> Wff -> ProofWriter
proveDefSubTrm allowedSubs definiendum definiens = do
  sub1 <- try (definiendum `matchTo` (WffAtom "eq" [TrmMetavar "trm_1", TrmSub (TrmMetavar "trm_4") "x" (TrmMetavar "trm_3")])) Inapplicable
  sub2 <- try (definiens `matchTo` (WffAtom "eq" [TrmMetavar "trm_1", TrmMetavar "trm_2"])) Inapplicable
  subMerged <- try (merge sub1 sub2) Inapplicable
  -- Get the proofs for the floating hypotheses
  let fHyps = [VarHyp "x", TrmHyp "trm_1", TrmHyp "trm_2", TrmHyp "trm_3", TrmHyp "trm_4"]
  fHypPrfs <- mapM (proveFHyp subMerged) fHyps
  -- Get the proof for the replacement statement
  t2 <- try (lookupTrm "trm_2" subMerged) Inapplicable
  t3 <- try (lookupTrm "trm_3" subMerged) Inapplicable
  t4 <- try (lookupTrm "trm_4" subMerged) Inapplicable
  x <- try (lookupVar "x" subMerged) Inapplicable
  replPrf <- proveReplTrm allowedSubs t2 x t3 t4
  -- Prove the definition statement
  proveMMStep "def.sub-trm" (fHypPrfs ++ [replPrf])

-- Tries to thin a step to match a given context
proveThin :: Context -> FlatStep -> RpnStack -> ProofWriter
proveThin toCtx (FlatStep fromCtx ps _ _ _) basePrf = case extras fromCtx toCtx of
  Just [] -> pure basePrf
  Just extraAssumptions -> do
    ctx1Prf <- proveCtx fromCtx
    ctx2Prf <- proveCtx $ AbsContext extraAssumptions
    psPrf <- proveWff ps
    proveMMStep "axm.thin" [ctx1Prf, ctx2Prf, psPrf, basePrf]
  Nothing -> fromMistake Inapplicable
  where
    extras (RelContext from) (RelContext to) = stripSuffix from to
    extras (AbsContext from) (AbsContext to) = stripSuffix from to
    extras _ _ = Nothing
    stripSuffix x y = reverse <$> stripPrefix (reverse x) (reverse y)

-- Check that a cited step matches an essential hypothesis, and if so return the substitution
verifyEHyp :: FlatStep -> Condition -> Maybe Substitution
verifyEHyp (FlatStep ctx wff _ _ _) (Condition Nothing hyp) = do
  let ctxSub = singletonCtx ctx
  hypSub <- wff `matchTo` hyp
  merge ctxSub hypSub
verifyEHyp (FlatStep ctx wff _ _ _) (Condition (Just sup) hyp) =
  case unconsCtx ctx of
    Just (assump, rest) -> do
      let ctxSub = singletonCtx rest
      supSub <- assump `matchTo` sup
      hypSub <- wff `matchTo` hyp
      mergeFold [ctxSub, supSub, hypSub]
    Nothing -> Nothing

varsInCond :: Condition -> S.Set FHyp
varsInCond (Condition (Just sup) hyp) = varsInWff sup <> varsInWff hyp
varsInCond (Condition Nothing hyp) = varsInWff hyp

-- Identify the mandatory disjoint variable restrictions (those that apply to mandatory vars)
getMandDVRs :: S.Set FHyp -> S.Set DVR -> S.Set DVR
getMandDVRs mandFHyps allDVRs =
  S.filter
    (\(DVR v1 v2) -> (v1 `S.member` mandFHyps) && (v2 `S.member` mandFHyps))
    allDVRs

try :: Maybe a -> Mistake -> ProofWriterM a
try val err = maybe (fromMistake err) pure val
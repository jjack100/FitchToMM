{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : FitchToMM.ProofWriter
-- Description : Monad for constructing Metamath proofs with proof state tracking
--
-- This module provides a monadic interface for building Metamath proofs that
-- may fail with a 'Mistake' while tracking floating hypotheses and disjointness restrictions.
-- It uses a writer monad to accumulate proof properties (used floating hypotheses
-- and incurred disjoint variable restrictions) and maintains a reverse Polish notation (RPN)
-- stack of proof steps.
module FitchToMM.ProofWriter where

import Control.Applicative ((<|>))
import qualified Control.Monad.Writer.Strict as W
import qualified Data.DList as D
import Data.Either
import Data.List
import Data.Maybe
import Data.Semigroup.Generic
import qualified Data.Set as S
import qualified Data.Text as T
import GHC.Generics
import FitchToMM.Variable

-- | Monad for constructing proof steps.
--
-- This monad combines error handling ('Either Mistake') with state accumulation
-- ('WriterT ProofProps') to track:
--
-- - Floating hypotheses required for the proof
-- - Disjoint variable restrictions (DVRs) that must be satisfied
newtype ProofWriterM a = ProofWriterM (W.WriterT ProofProps (Either Mistake) a)
  deriving (Show)
  deriving
    (Functor, Applicative, Monad)
    via W.WriterT ProofProps (Either Mistake)

-- | A proof computation producing an RPN stack of proof steps.
--
-- This is the primary type for building complete proofs.
type ProofWriter = ProofWriterM RpnStack

-- | A proof computation producing only proof properties (no result value).
--
-- Used for accumulating properties/constraints without producing proof steps.
type PropWriter = ProofWriterM ()

-- | Proof properties accumulated during proof construction.
--
-- Tracks:
--
-- - Floating hypotheses that have been used by the proof
-- - Disjoint variable restrictions that have been incurred
data ProofProps = ProofProps (S.Set FHyp) (S.Set DVR)
  deriving (Show, Generic)
  deriving
    (Semigroup, Monoid)
    via (GenericSemigroupMonoid ProofProps)

-- | A stack of proof steps in reverse Polish notation (RPN).
--
-- Steps are stored in a difference list for efficient concatenation.
newtype RpnStack = RpnStack (D.DList StackEntry)
  deriving (Show)

-- | A single entry in the proof stack.
--
-- The boolean flag indicates whether the step is \"local\" (specific to the
-- scope of the theorem) and should be qualified with the theorem label.
-- The entry being unknown is meant to correspond to the usage of the question mark
-- (?) in Metamath in place of a step to indicate an incomplete proof.
data StackEntry = StackEntry Bool RpnStep | Unknown
  deriving (Show)

-- | A Metamath proof step.
--
-- Contains the arity (number of hypotheses required) and the label of the
-- theorem or axiom being applied.
data RpnStep = RpnStep Int Label
  deriving (Show)

-- | The label of a Metamath theorem or axiom.
type Label = T.Text

instance Semigroup RpnStack where
  (<>) :: RpnStack -> RpnStack -> RpnStack
  (RpnStack a) <> (RpnStack b) = RpnStack $ a <> b

instance Monoid RpnStack where
  mempty = RpnStack mempty

-- | Errors that can occur during proof construction.
data Mistake
  = -- | Malformed assumption
    BadAssumption
  | -- | Cites the wrong number of lines
    BadCiteCount
  | -- | Cites a line that depends on a discharged assumption
    CitesDischarged
  | -- | Cites a line that does not come until later
    CitesLater
  | -- | Cites a line that does not exist
    CitesNonexistent
  | -- | Proof step cites itself
    CitesSelf
  | -- | Empty list where non-empty expected
    EmptyList
  | -- | Justification is not applicable
    Inapplicable
  | -- | Proof ends with 1 or more undischarged assumptions
    LeftUndischarged
  | -- | Cites a range of lines that is not a subproof
    NotASubproof
  | -- | References an unrecognized fact
    UnrecognizedFact
  deriving (Eq, Show)

-- | Lift an 'Either' computation into the 'ProofWriterM' monad.
lift :: Either Mistake a -> ProofWriterM a
lift = ProofWriterM . W.lift

-- | Convert a 'Mistake' into a failed proof writer computation.
fromMistake :: Mistake -> ProofWriterM a
fromMistake = lift . Left

-- | Try a list of alternative proof strategies.
--
-- Returns the first successful computation, or the last one if all fail.
-- If given an empty list, produces an 'Inapplicable' error.
alts :: [ProofWriterM a] -> ProofWriterM a
alts choices =
  fromMaybe
    (fromMistake Inapplicable)
    (find succeeded choices <|> listToMaybe choices)

-- | Produce the syntax proof for a metavariable.
-- Records the used floating hypothesis and generates a proof step.
-- Symbols not in 'preDeclaredVars' are marked as local.
proveMetavar :: FHyp -> ProofWriter
proveMetavar fhyp = do
  ProofWriterM $ W.tell $ ProofProps (S.singleton fhyp) S.empty
  let prove = if fhyp `elem` preDeclaredVars then proveStep else proveLocalStep
  prove $ RpnStep 0 $ fHypLabel fhyp

proveVar :: Var -> ProofWriter
proveVar = proveMetavar . VarHyp

proveWffMetavar :: Var -> ProofWriter
proveWffMetavar = proveMetavar . WffHyp

proveTrmMetavar :: Var -> ProofWriter
proveTrmMetavar = proveMetavar . TrmHyp

proveEllipsis :: ProofWriter
proveEllipsis = proveMetavar $ CtxHyp "..."

-- | Get the Metamath label for a Fitch hypothesis.
--
-- Examples:
--
-- > fHypLabel (VarHyp "x") @"var.x"
-- > fHypLabel (WffHyp "p") @"wff.p"
-- > fHypLabel (CtxHyp "...") @"ctx.ellipsis"
fHypLabel :: FHyp -> Label
fHypLabel (VarHyp l) = "var." <> l
fHypLabel (TrmHyp l) = "trm." <> l
fHypLabel (WffHyp l) = "wff." <> l
fHypLabel (CtxHyp "...") = "ctx.ellipsis"
fHypLabel (CtxHyp l) = "ctx." <> l

-- | Mark a floating hypothesis as internally generated.
--
-- Internal hypotheses (used in generated proof but not in original Fitch proof)
-- are prefixed with an underscore to distinguish them.
markInternal :: FHyp -> FHyp
markInternal (VarHyp l) = VarHyp $ T.cons '_' l
markInternal (TrmHyp l) = TrmHyp $ T.cons '_' l
markInternal (WffHyp l) = WffHyp $ T.cons '_' l
markInternal (CtxHyp l) = CtxHyp $ T.cons '_' l

-- | Generate a Metamath proof step with given label and hypotheses.
--
-- Combines the given hypotheses (RPN stacks) with a new step.
-- The arity is inferred from the number of provided hypotheses.
proveMMStep :: Label -> [RpnStack] -> ProofWriter
proveMMStep label hyps = do
  step <- proveStep $ RpnStep (length hyps) label
  return $ mconcat hyps <> step

-- | Generate a proof with a single step.
--
-- The step has no hypotheses and produces a single stack entry.
proveStep :: RpnStep -> ProofWriter
proveStep = pure . RpnStack . D.singleton . (StackEntry False)

-- | Generate a proof with a single step whose label is local to the theorem.
--
-- Local steps are qualified with their theorem label when printed.
proveLocalStep :: RpnStep -> ProofWriter
proveLocalStep = pure . RpnStack . D.singleton . (StackEntry True)

-- | Apply a disjoint variable restriction (DVR) to the proof.
--
-- Has no effect if the variables are identical.
applyDVR :: DVR -> PropWriter
applyDVR dvr@(DVR v1 v2)
  | v1 /= v2 = ProofWriterM $ W.tell $ ProofProps S.empty (S.singleton dvr)
  | otherwise = pure ()

-- | Require that two variables are disjoint.
reqDisjoint :: FHyp -> FHyp -> PropWriter
reqDisjoint v1 v2
  | v1 /= v2 = ProofWriterM $ W.tell $ ProofProps S.empty (S.singleton $ mkDVR v1 v2)
  | otherwise = pure ()

-- | Require that a hypothesis is disjoint from all in a collection.
reqDisjointFor :: (Foldable t) => FHyp -> t FHyp -> PropWriter
reqDisjointFor v = mapM_ (reqDisjoint v)

-- | Run a proof writer computation and extract the result and accumulated properties.
--
-- Returns @(RpnStack, ProofProps)@. If the computation fails, returns
-- an unknown stack and empty properties.
runProofWriter :: ProofWriter -> (RpnStack, ProofProps)
runProofWriter (ProofWriterM writer) = case W.runWriterT writer of
  Left _ -> (RpnStack (D.singleton Unknown), ProofProps S.empty S.empty)
  Right res -> res

-- | Run a proof writer computation and extract only the accumulated properties.
--
-- Discards any stack result.
execProofWriter :: ProofWriter -> ProofProps
execProofWriter = snd . runProofWriter

-- | Get the first 'Mistake' encountered, if any.
--
-- Returns @Just mistake@ if the computation failed, or @Nothing@ if successful.
getMistake :: ProofWriter -> Maybe Mistake
getMistake (ProofWriterM writer) = case W.runWriterT writer of
  Left err -> Just err
  Right _ -> Nothing

-- | Check if a proof writer computation failed.
failed :: ProofWriterM a -> Bool
failed (ProofWriterM writer) = isLeft $ W.runWriterT writer

-- | Check if a proof writer computation succeeded.
succeeded :: ProofWriterM a -> Bool
succeeded (ProofWriterM writer) = isRight $ W.runWriterT writer

-- | Extract the proof steps from an RPN stack as labels.
--
-- Local steps are qualified with the given theorem label.
listStack :: Label -> RpnStack -> [T.Text]
listStack thmLabel stack =
  map
    (maybe "?" $ \(RpnStep _ label) -> label)
    $ getSteps thmLabel stack

-- | Extract proof steps from an RPN stack.
--
-- Returns a list of @Maybe RpnStep@ where @Nothing@ indicates an unknown entry.
-- Local steps are qualified with the theorem label.
getSteps :: Label -> RpnStack -> [Maybe RpnStep]
getSteps thmLabel (RpnStack dlist) =
  let getStep (StackEntry True (RpnStep arity label)) =
        Just $ RpnStep arity (thmLabel <> "." <> label)
      getStep (StackEntry False step) = Just step
      getStep (Unknown) = Nothing
   in map getStep (D.toList dlist)
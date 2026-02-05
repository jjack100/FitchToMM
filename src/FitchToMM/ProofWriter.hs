{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE OverloadedStrings #-}

module FitchToMM.ProofWriter
  ( ProofWriter,
    Mistake (..),
    RpnStack,
    RpnStep (..),
    ProofProps (..),
    FHyp (..),
    Label,
    DVR(..),
    PropWriter,
    proveMetavar,
    proveVar,
    proveStep,
    runProofWriter,
    reqDisjoint,
    execProofWriter,
    getMistake,
    failed,
    succeeded,
    proveEllipsis,
    proveTrmMetavar,
    proveWffMetavar,
    fHypLabel,
    markInternal,
    listStack,
    reqDisjointFor,
    getSteps,
    mkDVR,
    applyDVR,
  )
where

import qualified Control.Monad.Writer.Strict as W
import qualified Data.DList as D
import Data.Either
import Data.Semigroup.Generic
import qualified Data.Set as S
import qualified Data.Text as T
import GHC.Generics

-- Helper Monad to build the RPN stack while tracking properties about the proof
type ProofWriter = W.WriterT ProofProps (Either Mistake) RpnStack

type PropWriter = W.WriterT ProofProps (Either Mistake) ()

data ProofProps = ProofProps (S.Set FHyp) (S.Set DVR)
  deriving (Show, Generic)
  deriving
    (Semigroup, Monoid)
    via (GenericSemigroupMonoid ProofProps)

newtype RpnStack = RpnStack (D.DList (Maybe RpnStep))
  deriving (Show)

data RpnStep = RpnStep Int Label
  deriving (Show)

type Label = T.Text

instance Semigroup RpnStack where
  (RpnStack a) <> (RpnStack b) = RpnStack $ a <> b

instance Monoid RpnStack where
  mempty = RpnStack mempty

-- Floating hypothesis
data FHyp
  = VarHyp {fHypName :: T.Text}
  | TrmHyp {fHypName :: T.Text}
  | WffHyp {fHypName :: T.Text}
  | CtxHyp {fHypName :: T.Text}
  deriving (Ord, Eq, Show)

-- Disjoint variable restriction
data DVR = DVR FHyp FHyp
  deriving (Show, Eq, Ord)

data Mistake
  = BadAssumption
  | BadCiteCount
  | CitesDischarged
  | CitesLater
  | CitesNonexistent
  | CitesSelf
  | EmptyList
  | Inapplicable
  | LeftUndischarged
  | NotASubproof
  | UnrecognizedFact
  deriving (Eq, Show)

proveMetavar :: FHyp -> ProofWriter
proveMetavar fhyp = do
  W.tell $ ProofProps (S.singleton fhyp) S.empty
  proveStep $ RpnStep 0 $ fHypLabel fhyp

fHypLabel :: FHyp -> Label
fHypLabel (VarHyp l) = "var." <> l
fHypLabel (TrmHyp l) = "trm." <> l
fHypLabel (WffHyp l) = "wff." <> l
fHypLabel (CtxHyp "...") = "ctx.ellipsis"
fHypLabel (CtxHyp l) = "ctx." <> l

{- Prefix a variable with an underscore to indicate it is used internally
   (i.e., used in the generated proof but not present in the Fitch proof) -}
markInternal :: FHyp -> FHyp
markInternal (VarHyp l) = VarHyp $ T.cons '_' l
markInternal (TrmHyp l) = TrmHyp $ T.cons '_' l
markInternal (WffHyp l) = WffHyp $ T.cons '_' l
markInternal (CtxHyp l) = CtxHyp $ T.cons '_' l

proveVar :: T.Text -> ProofWriter
proveVar = proveMetavar . VarHyp

proveWffMetavar :: T.Text -> ProofWriter
proveWffMetavar = proveMetavar . WffHyp

proveTrmMetavar :: T.Text -> ProofWriter
proveTrmMetavar = proveMetavar . TrmHyp

proveEllipsis :: ProofWriter
proveEllipsis = proveMetavar $ CtxHyp "..."

proveStep :: RpnStep -> ProofWriter
proveStep = pure . RpnStack . D.singleton . Just

mkDVR :: FHyp -> FHyp -> DVR
mkDVR v1 v2 = if v1 <= v2 then DVR v1 v2 else DVR v2 v1

applyDVR :: DVR -> W.WriterT ProofProps (Either Mistake) ()
applyDVR dvr = W.tell $ ProofProps S.empty (S.singleton dvr)

reqDisjoint :: FHyp -> FHyp -> W.WriterT ProofProps (Either Mistake) ()
reqDisjoint v1 v2 = W.tell $ ProofProps S.empty (S.singleton $ mkDVR v1 v2)

reqDisjointFor :: (Foldable t) => FHyp -> t FHyp -> PropWriter
reqDisjointFor v = mapM_ (reqDisjoint v)

runProofWriter :: ProofWriter -> (RpnStack, ProofProps)
runProofWriter writer = case W.runWriterT writer of
  Left _ -> (RpnStack (D.singleton Nothing), ProofProps S.empty S.empty)
  Right res -> res

execProofWriter :: ProofWriter -> ProofProps
execProofWriter = snd . runProofWriter

getMistake :: ProofWriter -> Maybe Mistake
getMistake writer = case W.runWriterT writer of
  Left err -> Just err
  Right _ -> Nothing

failed :: ProofWriter -> Bool
failed = isLeft . W.runWriterT

succeeded :: ProofWriter -> Bool
succeeded = isRight . W.runWriterT

listStack :: RpnStack -> [T.Text]
listStack (RpnStack stack) =
  let getLabel (RpnStep _ label) = label
   in map (maybe "?" getLabel) $ D.toList stack

getSteps :: RpnStack -> [Maybe RpnStep]
getSteps (RpnStack dlist) = D.toList dlist
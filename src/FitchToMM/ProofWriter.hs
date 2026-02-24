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
    DVR (..),
    PropWriter,
    proveMetavar,
    proveVar,
    proveStep,
    proveLocalStep,
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
    preDeclaredVars,
    sortVars,
    proveMMStep,
    isSetvar,
    isMetavar,
    isCtx,
  )
where

import qualified Control.Monad.Writer.Strict as W
import qualified Data.DList as D
import Data.Either
import Data.List
import Data.Maybe
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

newtype RpnStack = RpnStack (D.DList StackEntry)
  deriving (Show)

-- Store a boolean flag indicating if the step is "local" and should be prefixed
-- with the label of the theorem
data StackEntry = StackEntry Bool RpnStep | Unknown
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
  let prove = if fhyp `elem` preDeclaredVars then proveStep else proveLocalStep
  prove $ RpnStep 0 $ fHypLabel fhyp

fHypLabel :: FHyp -> Label
fHypLabel (VarHyp l) = "var." <> l
fHypLabel (TrmHyp l) = "trm." <> l
fHypLabel (WffHyp l) = "wff." <> l
fHypLabel (CtxHyp "...") = "ctx.ellipsis"
fHypLabel (CtxHyp l) = "ctx." <> l

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
proveStep = pure . RpnStack . D.singleton . (StackEntry False)

proveMMStep :: Label -> [RpnStack] -> ProofWriter
proveMMStep label hyps = do
  step <- proveStep $ RpnStep (length hyps) label
  return $ mconcat hyps <> step

proveLocalStep :: RpnStep -> ProofWriter
proveLocalStep = pure . RpnStack . D.singleton . (StackEntry True)

mkDVR :: FHyp -> FHyp -> DVR
mkDVR v1 v2 = if v1 <= v2 then DVR v1 v2 else DVR v2 v1

applyDVR :: DVR -> W.WriterT ProofProps (Either Mistake) ()
applyDVR dvr@(DVR v1 v2)
  | v1 /= v2 = W.tell $ ProofProps S.empty (S.singleton dvr)
  | otherwise = pure ()

reqDisjoint :: FHyp -> FHyp -> PropWriter
reqDisjoint v1 v2
  | v1 /= v2 = W.tell $ ProofProps S.empty (S.singleton $ mkDVR v1 v2)
  | otherwise = pure ()

reqDisjointFor :: (Foldable t) => FHyp -> t FHyp -> PropWriter
reqDisjointFor v = mapM_ (reqDisjoint v)

runProofWriter :: ProofWriter -> (RpnStack, ProofProps)
runProofWriter writer = case W.runWriterT writer of
  Left _ -> (RpnStack (D.singleton Unknown), ProofProps S.empty S.empty)
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

listStack :: T.Text -> RpnStack -> [T.Text]
listStack thmLabel stack =
  map
    (maybe "?" $ \(RpnStep _ label) -> label)
    $ getSteps thmLabel stack

getSteps :: T.Text -> RpnStack -> [Maybe RpnStep]
getSteps thmLabel (RpnStack dlist) =
  let getStep (StackEntry True (RpnStep arity label)) =
        Just $ RpnStep arity (thmLabel <> "." <> label)
      getStep (StackEntry False step) = Just step
      getStep (Unknown) = Nothing
   in map getStep (D.toList dlist)

preDeclaredVars :: [FHyp]
preDeclaredVars =
  [CtxHyp "..."]
    ++ map WffHyp ["phi", "psi", "chi", "phi_1", "psi_1", "chi_1", "phi_2", "psi_2", "chi_2"]
    ++ map (VarHyp . T.singleton) ['a' .. 'z']
    ++ map TrmHyp ["trm_1", "trm_2", "trm_3", "trm_4", "trm_5"]
    ++ [VarHyp "_a", VarHyp "_x", VarHyp "_trm_1"]

sortVars :: [FHyp] -> [FHyp]
sortVars = sortOn $ \x -> (pos x, x)
  where
    pos x = fromMaybe end (elemIndex x preDeclaredVars)
    end = length preDeclaredVars
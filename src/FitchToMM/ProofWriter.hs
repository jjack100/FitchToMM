{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE OverloadedStrings #-}

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

-- Helper Monad to build the RPN stack while tracking properties about the proof
newtype ProofWriterM a = ProofWriterM (W.WriterT ProofProps (Either Mistake) a)
  deriving (Show)
  deriving
    (Functor, Applicative, Monad)
    via W.WriterT ProofProps (Either Mistake)

type ProofWriter = ProofWriterM RpnStack

type PropWriter = ProofWriterM ()

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
  (<>) :: RpnStack -> RpnStack -> RpnStack
  (RpnStack a) <> (RpnStack b) = RpnStack $ a <> b

instance Monoid RpnStack where
  mempty = RpnStack mempty

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

lift :: Either Mistake a -> ProofWriterM a
lift = ProofWriterM . W.lift

fromMistake :: Mistake -> ProofWriterM a
fromMistake = lift . Left

alts :: [ProofWriterM a] -> ProofWriterM a
alts choices =
  fromMaybe
    (fromMistake Inapplicable)
    (find succeeded choices <|> listToMaybe choices)

proveMetavar :: FHyp -> ProofWriter
proveMetavar fhyp = do
  ProofWriterM $ W.tell $ ProofProps (S.singleton fhyp) S.empty
  let prove = if fhyp `elem` preDeclaredVars then proveStep else proveLocalStep
  prove $ RpnStep 0 $ fHypLabel fhyp

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

proveVar :: Var -> ProofWriter
proveVar = proveMetavar . VarHyp

proveWffMetavar :: Var -> ProofWriter
proveWffMetavar = proveMetavar . WffHyp

proveTrmMetavar :: Var -> ProofWriter
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

applyDVR :: DVR -> PropWriter
applyDVR dvr@(DVR v1 v2)
  | v1 /= v2 = ProofWriterM $ W.tell $ ProofProps S.empty (S.singleton dvr)
  | otherwise = pure ()

reqDisjoint :: FHyp -> FHyp -> PropWriter
reqDisjoint v1 v2
  | v1 /= v2 = ProofWriterM $ W.tell $ ProofProps S.empty (S.singleton $ mkDVR v1 v2)
  | otherwise = pure ()

reqDisjointFor :: (Foldable t) => FHyp -> t FHyp -> PropWriter
reqDisjointFor v = mapM_ (reqDisjoint v)

runProofWriter :: ProofWriter -> (RpnStack, ProofProps)
runProofWriter (ProofWriterM writer) = case W.runWriterT writer of
  Left _ -> (RpnStack (D.singleton Unknown), ProofProps S.empty S.empty)
  Right res -> res

execProofWriter :: ProofWriter -> ProofProps
execProofWriter = snd . runProofWriter

getMistake :: ProofWriter -> Maybe Mistake
getMistake (ProofWriterM writer) = case W.runWriterT writer of
  Left err -> Just err
  Right _ -> Nothing

failed :: ProofWriterM a -> Bool
failed (ProofWriterM writer) = isLeft $ W.runWriterT writer

succeeded :: ProofWriterM a -> Bool
succeeded (ProofWriterM writer) = isRight $ W.runWriterT writer

listStack :: Label -> RpnStack -> [T.Text]
listStack thmLabel stack =
  map
    (maybe "?" $ \(RpnStep _ label) -> label)
    $ getSteps thmLabel stack

getSteps :: Label -> RpnStack -> [Maybe RpnStep]
getSteps thmLabel (RpnStack dlist) =
  let getStep (StackEntry True (RpnStep arity label)) =
        Just $ RpnStep arity (thmLabel <> "." <> label)
      getStep (StackEntry False step) = Just step
      getStep (Unknown) = Nothing
   in map getStep (D.toList dlist)
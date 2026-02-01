{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}

module FitchToMM.Schema
  ( Theorem,
    Fact,
    parseTheorem,
    parseFact,
  )
where

import Control.Monad
import Data.Aeson
import Data.Char (isAlphaNum, isAscii)
import qualified Data.Map.Strict as M
import Data.OpenApi
import qualified Data.Text as T
import qualified FitchToMM.Fact as MMFact
import qualified FitchToMM.FitchProof as F
import FitchToMM.Parser
import qualified FitchToMM.ProofWriter as PW
import GHC.Generics

data Theorem = Theorem
  { name :: MMLabel,
    allowedSubs :: AllowedSubs,
    premises :: [EHyp],
    steps :: [ProofStep]
  }
  deriving stock (Generic)
  deriving anyclass (ToSchema, FromJSON)

newtype MMLabel = MMLabel T.Text
  deriving stock (Generic)
  deriving anyclass (ToSchema)

instance FromJSON MMLabel where
  parseJSON = withText "MMLabel" $ \txt -> do
    let valid c = isAscii c && (isAlphaNum c || elem c ("-._" :: String))
    unless (T.all valid txt) $ fail $ "Invalid characters in label: " <> T.unpack txt
    return $ MMLabel txt

data Fact = Fact
  { factName :: T.Text,
    claim :: T.Text,
    fHyps :: [FHyp],
    eHyps :: [EHyp],
    dvrs :: [(FHyp, FHyp)]
  }
  deriving stock (Generic)
  deriving anyclass (ToSchema, FromJSON)

data FHyp
  = VarHyp T.Text
  | TrmHyp T.Text
  | WffHyp T.Text
  | CtxHyp T.Text
  deriving stock (Generic)
  deriving anyclass (ToSchema, FromJSON)

newtype AllowedSubs = AllowedSubs (M.Map T.Text [T.Text])
  deriving stock (Generic)
  deriving anyclass (ToSchema, FromJSON)

data ProofStep
  = ProofStep
      { expression :: T.Text,
        rule :: T.Text,
        cites :: [Citation]
      }
  | Subproof
      { assumption :: T.Text,
        substeps :: [ProofStep]
      }
  deriving stock (Generic)
  deriving anyclass (ToSchema, FromJSON)

data Citation = Line Int | Range Int Int
  deriving stock (Generic)
  deriving anyclass (ToSchema, FromJSON)

data EHyp = EHyp
  { supposition :: Maybe T.Text,
    condition :: T.Text
  }
  deriving stock (Generic)
  deriving anyclass (ToSchema, FromJSON)

parseTheorem :: Language -> Theorem -> Either T.Text F.FitchProof
parseTheorem l (Theorem (MMLabel thmName) thmAllowedSubs thmPrems thmSteps) = do
  parsedPrems <- mapM (parseEHyp l) thmPrems
  parsedSteps <- mapM (parseProofStep l) thmSteps
  let AllowedSubs subs = thmAllowedSubs
  let subsFunc = \x -> M.findWithDefault [] x subs
  return $ F.FitchProof thmName subsFunc parsedPrems parsedSteps

parseProofStep :: Language -> ProofStep -> Either T.Text F.FitchStep
parseProofStep l (ProofStep prfExpr prfRule prfCites) = do
  parsedExpr <- parseExpr l prfExpr
  let parsedCites = map parseCitation prfCites
  return $ F.FitchStep parsedExpr prfRule parsedCites
parseProofStep l (Subproof assump stps) = do
  parsedAssump <- parseExpr l assump
  parsedSteps <- mapM (parseProofStep l) stps
  return $ F.FitchSubproof parsedAssump parsedSteps

parseFact :: Language -> Fact -> Either T.Text (T.Text, MMFact.Fact)
parseFact l fact = do
  parsedEHyps <- mapM (parseEHyp l) (eHyps fact)
  parsedClaim <- parseExpr l (claim fact)
  return
    ( factName fact,
      MMFact.Fact
        parsedClaim
        (map parseFHyp $ fHyps fact)
        parsedEHyps
        (map parseDVR $ dvrs fact)
    )

parseDVR :: (FHyp, FHyp) -> PW.DVR
parseDVR (x, y) = PW.DVR (parseFHyp x) (parseFHyp y)

parseFHyp :: FHyp -> PW.FHyp
parseFHyp (VarHyp txt) = PW.VarHyp txt
parseFHyp (TrmHyp txt) = PW.TrmHyp txt
parseFHyp (WffHyp txt) = PW.WffHyp txt
parseFHyp (CtxHyp txt) = PW.CtxHyp txt

parseEHyp :: Language -> EHyp -> Either T.Text F.Condition
parseEHyp l (EHyp (Just sup) cond) = do
  parsedSup <- parseExpr l sup
  parsedCond <- parseExpr l cond
  return $ F.Condition (Just parsedSup) parsedCond
parseEHyp l (EHyp Nothing cond) = do
  parsedCond <- parseExpr l cond
  return $ F.Condition Nothing parsedCond

parseExpr :: Language -> T.Text -> Either T.Text Wff
parseExpr l expr = case parseFormula (primitives <> l) expr of
  Left err -> Left $ T.pack $ show err
  Right res -> Right res

parseCitation :: Citation -> F.Citation
parseCitation (Line i) = F.Line i
parseCitation (Range i j) = F.Range i j
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}

module FitchToMM.Schema where

import Control.Monad
import Data.Aeson
import Data.Bifunctor (first)
import Data.Char (isAlphaNum, isAscii)
import qualified Data.Map.Strict as M
import Data.OpenApi
import qualified Data.Text as T
import FitchToMM.Collection (fromListE)
import qualified FitchToMM.Collection as C
import FitchToMM.Declarations (toLanguage)
import qualified FitchToMM.Declarations as D
import qualified FitchToMM.FitchProof as F
import qualified FitchToMM.MMProof as MM
import qualified FitchToMM.Parser as P
import qualified FitchToMM.ProofWriter as PW
import GHC.Generics

data Collection = Collection
  { title :: T.Text,
    items :: [Item]
  }
  deriving stock (Generic)
  deriving anyclass (ToSchema, FromJSON)

data Item
  = Theorem
      { label :: MMLabel,
        allowedSubs :: AllowedSubs,
        premises :: [EHyp],
        steps :: [ProofStep]
      }
  | Definition
      { label :: MMLabel,
        allowedSubs :: AllowedSubs,
        symbolType :: SymbolType,
        definedTerm :: T.Text,
        definiendum :: T.Text,
        definiens :: T.Text
      }
  deriving stock (Generic)
  deriving anyclass (ToSchema, FromJSON)

data SymbolType = Predicate Int | Function Int | Constant
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

parseCollection :: D.DeclMap -> Collection -> Either T.Text C.Collection
parseCollection declMap (Collection cTitle cItems) =
  fromListE cTitle declMap (map parseItem cItems)

parseItem :: Item -> D.DeclMap -> Either T.Text C.Item
parseItem (Theorem (MMLabel itmName) itmAllowedSubs itmPrems itmSteps) declMap = do
  let l = toLanguage declMap
  parsedPrems <- mapM (parseEHyp l) itmPrems
  parsedSteps <- mapM (parseProofStep l) itmSteps
  let AllowedSubs subs = itmAllowedSubs
      subsFunc x = M.findWithDefault [] x subs
      fitchProof = F.FitchProof itmName subsFunc parsedPrems parsedSteps
      maybeMMProof = MM.fromFitchProof declMap fitchProof
  mmProof <- maybe (Left "Empty theorem") Right maybeMMProof
  return $ C.TheoremItem fitchProof mmProof
parseItem (Definition (MMLabel itmName) itmAllowedSubs itmSymType itmDefinedTerm itmDefiniendum itmDefiniens) declMap = do
  let symTyp = parseSymbolType itmSymType
      symSig x = if x == itmDefinedTerm then Just symTyp else Nothing
      l = P.union (toLanguage declMap) (P.Language symSig)
      AllowedSubs subs = itmAllowedSubs
      subsFunc x = M.findWithDefault [] x subs
  def <- first T.show $ D.mkDef itmDefiniendum itmDefiniens subsFunc l
  return $ C.DefinitionItem itmName subsFunc symTyp itmDefinedTerm def

parseSymbolType :: SymbolType -> P.SymbolType
parseSymbolType (Predicate arity) = P.SymPredicate arity
parseSymbolType (Function arity) = P.SymFunction arity
parseSymbolType Constant = P.SymConstant

parseProofStep :: P.Language -> ProofStep -> Either T.Text F.FitchStep
parseProofStep l (ProofStep prfExpr prfRule prfCites) = do
  parsedExpr <- parseExpr l prfExpr
  let parsedCites = map parseCitation prfCites
  return $ F.FitchStep parsedExpr prfRule parsedCites
parseProofStep l (Subproof assump stps) = do
  parsedAssump <- parseExpr l assump
  parsedSteps <- mapM (parseProofStep l) stps
  return $ F.FitchSubproof parsedAssump parsedSteps

parseDVR :: (FHyp, FHyp) -> PW.DVR
parseDVR (x, y) = PW.mkDVR (parseFHyp x) (parseFHyp y)

parseFHyp :: FHyp -> PW.FHyp
parseFHyp (VarHyp txt) = PW.VarHyp txt
parseFHyp (TrmHyp txt) = PW.TrmHyp txt
parseFHyp (WffHyp txt) = PW.WffHyp txt
parseFHyp (CtxHyp txt) = PW.CtxHyp txt

parseEHyp :: P.Language -> EHyp -> Either T.Text D.Condition
parseEHyp l (EHyp (Just sup) cond) = do
  parsedSup <- parseExpr l sup
  parsedCond <- parseExpr l cond
  return $ D.Condition (Just parsedSup) parsedCond
parseEHyp l (EHyp Nothing cond) = do
  parsedCond <- parseExpr l cond
  return $ D.Condition Nothing parsedCond

parseExpr :: P.Language -> T.Text -> Either T.Text P.Wff
parseExpr l expr = case P.parseFormula l expr of
  Left err -> Left $ T.pack $ show err
  Right res -> Right res

parseCitation :: Citation -> F.Citation
parseCitation (Line i) = F.Line i
parseCitation (Range i j) = F.Range i j
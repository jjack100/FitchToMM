{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module FitchToMM.Serialize where

import Autodocodec
import Autodocodec.Schema
import Control.Monad
import Data.Aeson (FromJSON, ToJSON, withText)
import qualified Data.Aeson as JSON
import Data.Aeson.Encode.Pretty (encodePretty)
import qualified Data.Aeson.KeyMap as KM
import Data.Bifunctor (first)
import qualified Data.ByteString.Lazy as BL
import Data.Char (isAlphaNum, isAscii)
import qualified Data.HashMap.Strict as HashMap
import qualified Data.Map.Strict as M
import qualified Data.Text as T
import FitchToMM.Collection (fromList)
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
  deriving
    (FromJSON, ToJSON)
    via (Autodocodec Collection)

instance HasCodec Collection where
  codec :: JSONCodec Collection
  codec =
    object "Collection" $
      Collection
        <$> requiredField "title" "The title of the collection" .= title
        <*> requiredField "items" "Items the collection contains" .= items

data Item
  = Theorem
      { label :: MMLabel,
        allowedSubs :: AllowedSubs,
        premises :: [Premise],
        steps :: [ProofStep]
      }
  | Definition
      { label :: MMLabel,
        allowedSubs :: AllowedSubs,
        symbol :: Symbol,
        definiendum :: T.Text,
        definiens :: T.Text
      }
  | Equivalence
      { label :: MMLabel,
        allowedSubs :: AllowedSubs,
        steps :: [ProofStep]
      }

instance HasCodec Item where
  codec = object "Item" $ discriminatedUnionCodec "type" enc dec
    where
      theoremCodec =
        Theorem
          <$> requiredField' "label" .= label
          <*> requiredField' "allowedSubs" .= allowedSubs
          <*> requiredField' "premises" .= premises
          <*> requiredField' "steps" .= steps
      definitionCodec =
        Definition
          <$> requiredField' "label" .= label
          <*> requiredField' "allowedSubs" .= allowedSubs
          <*> requiredField "symbol" "The symbol to be defined" .= symbol
          <*> requiredField "definiendum" "The formula containing the defined symbol, to be equated with the definiens" .= definiendum
          <*> requiredField "definiens" "The formula on the right-hand side of ':=', used to define the symbol" .= definiens
      equivCodec =
        Equivalence
          <$> requiredField' "label" .= label
          <*> requiredField' "allowedSubs" .= allowedSubs
          <*> requiredField "steps" "Fitch-style steps (that for an equivalence proof should end in a biconditional statement)" .= steps
      enc itm@(Theorem _ _ _ _) = ("Theorem", mapToEncoder itm theoremCodec)
      enc itm@(Definition _ _ _ _ _) = ("Definition", mapToEncoder itm definitionCodec)
      enc itm@(Equivalence _ _ _) = ("Equivalence", mapToEncoder itm equivCodec)
      dec =
        HashMap.fromList
          [ ("theorem", ("Theorem", mapToDecoder id theoremCodec)),
            ("definition", ("Definition", mapToDecoder id definitionCodec)),
            ("equivalence", ("Equivalence", mapToDecoder id equivCodec))
          ]

data Symbol = Predicate T.Text Int | Function T.Text Int | Constant T.Text

instance HasCodec Symbol where
  codec :: JSONCodec Symbol
  codec = object "Symbol" $ discriminatedUnionCodec "type" enc dec
    where
      argsCodec =
        (,)
          <$> requiredField' "name" .= fst
          <*> requiredField "arity" "Number of arguments the predicate or function accepts" .= snd
      constCodec = requiredField' "name"
      enc (Predicate name arity) = ("Predicate", mapToEncoder (name, arity) argsCodec)
      enc (Function name arity) = ("Function", mapToEncoder (name, arity) argsCodec)
      enc (Constant name) = ("Constant", mapToEncoder name constCodec)
      dec =
        HashMap.fromList
          [ ("predicate", ("Theorem", mapToDecoder (uncurry Predicate) argsCodec)),
            ("function", ("Function", mapToDecoder (uncurry Function) argsCodec)),
            ("constant", ("Constant", mapToDecoder Constant constCodec))
          ]

newtype MMLabel = MMLabel T.Text
  deriving stock (Generic)
  deriving anyclass (ToJSON)

instance FromJSON MMLabel where
  parseJSON = withText "MMLabel" $ \txt -> do
    let valid c = isAscii c && (isAlphaNum c || elem c ("-._" :: String))
    unless (T.all valid txt) $ fail $ "Invalid characters in label: " <> T.unpack txt
    return $ MMLabel txt

instance HasCodec MMLabel where
  codec :: JSONCodec MMLabel
  codec = codecViaAeson "MMLabel"

data Fact = Fact
  { factName :: T.Text,
    claim :: T.Text,
    fHyps :: [FHyp],
    eHyps :: [Premise],
    dvrs :: [(FHyp, FHyp)]
  }

data FHyp
  = VarHyp T.Text
  | TrmHyp T.Text
  | WffHyp T.Text
  | CtxHyp T.Text

newtype AllowedSubs = AllowedSubs (M.Map T.Text [T.Text])
  deriving stock (Generic)
  deriving anyclass (FromJSON, ToJSON)

instance HasCodec AllowedSubs where
  codec :: JSONCodec AllowedSubs
  codec = codecViaAeson "AllowedSubs" <?> "Map from metavariables to a list of variables that may occur in the substituted formula or term"

data ProofStep
  = ProofStep
      { expression :: T.Text,
        rule :: MMLabel,
        cites :: [Citation]
      }
  | Subproof
      { assumption :: T.Text,
        substeps :: [ProofStep]
      }
  deriving stock (Generic)
  deriving anyclass (FromJSON, ToJSON)

instance HasCodec ProofStep where
  codec :: JSONCodec ProofStep
  codec = named "ProofStep" $ object "ProofStep" $ discriminatedUnionCodec "type" enc dec
    where
      stepCodec =
        ProofStep
          <$> requiredField "expression" "S-expression representation of the formula proven at this step" .= expression
          <*> requiredField "rule" "The rule being referenced as a justification (either a Metamath label or a built-in rule)" .= rule
          <*> requiredField "cites" "List of previous lines or subproofs that satisfy the premises of the rule" .= cites
      subproofCodec =
        Subproof
          <$> requiredField "assumption" "An assumption to be made for the sake of argument" .= assumption
          <*> requiredField' "substeps" .= substeps
      enc itm@(ProofStep _ _ _) = ("ProofStep", mapToEncoder itm stepCodec)
      enc itm@(Subproof _ _) = ("Subproof", mapToEncoder itm subproofCodec)
      dec =
        HashMap.fromList
          [ ("step", ("Step", mapToDecoder id stepCodec)),
            ("subproof", ("Subproof", mapToDecoder id subproofCodec))
          ]

data Citation = Line Int | Range Int Int
  deriving stock (Generic)
  deriving anyclass (FromJSON, ToJSON)

instance HasCodec Citation where
  codec =
    bimapCodec f g $ disjointEitherCodec codec codec
    where
      f (Left line) = Right $ Line line
      f (Right [start, end]) = Right $ Range start end
      f (Right _) = Left "A range should have exactly two elements (the start and end)"

      g (Line line) = Left line
      g (Range start end) = Right [start, end]

data Premise = Premise
  { supposition :: Maybe T.Text,
    condition :: T.Text
  }
  deriving stock (Generic)
  deriving anyclass (FromJSON, ToJSON)

instance HasCodec Premise where
  codec =
    object "Premise" $
      Premise
        <$> optionalField "supposition" "A supposition from which the condition should follow, to be discharged in an application of the theorem" .= supposition
        <*> requiredField "condition" "The condition that should be satisfied as a premise to the theorem" .= condition

writeSchema :: FilePath -> IO ()
writeSchema path = BL.writeFile path $ encodePretty revisedSchema
  where
    collectionSchema = jsonSchemaViaCodec @Collection
    (json, defs) = moveDefs $ describe $ JSON.toJSON collectionSchema
    revisedSchema = case json of
      JSON.Object o -> JSON.Object $ KM.insert "$defs" (JSON.Object defs) o
      v -> v
    -- Use generated comments as the description field
    describe (JSON.Object o) =
      let renamed = case KM.lookup "$comment" o of
            Just v -> KM.insert "description" v (KM.delete "$comment" o)
            Nothing -> o
       in JSON.Object $ KM.map describe renamed
    describe (JSON.Array a) = JSON.Array $ fmap describe a
    describe v = v
    -- Remove and collect $defs to move them to the root level
    moveDefs (JSON.Object o) =
      let withoutDefs = KM.delete "$defs" o
          res = KM.map (fst . moveDefs) withoutDefs
       in (JSON.Object res, getDefs o <> foldMap (snd . moveDefs) withoutDefs)
    moveDefs (JSON.Array a) =
      let res = JSON.Array $ fmap (fst . moveDefs) a
       in (res, foldMap (snd . moveDefs) a)
    moveDefs v = (v, mempty)
    getDefs o = case KM.lookup "$defs" o of
      Just (JSON.Object d) -> d
      _ -> KM.empty

parseCollection :: D.DeclMap -> Collection -> Either T.Text C.Collection
parseCollection declMap (Collection cTitle cItems) =
  fromList cTitle declMap (map parseItem cItems)

parseItem :: Item -> D.DeclMap -> Either T.Text C.Item
parseItem (Theorem (MMLabel itmName) itmAllowedSubs itmPrems itmSteps) declMap = do
  let l = toLanguage declMap
  parsedPrems <- mapM (parsePremise l) itmPrems
  parsedSteps <- mapM (parseProofStep l) itmSteps
  let AllowedSubs subs = itmAllowedSubs
      subsFunc x = M.findWithDefault [] x subs
      fitchProof = F.FitchProof itmName subsFunc parsedPrems parsedSteps
      maybeMMProof = MM.fromFitchProof declMap fitchProof
  mmProof <- maybe (Left "Empty theorem") Right maybeMMProof
  return $ C.TheoremItem fitchProof mmProof
parseItem (Definition (MMLabel itmName) itmAllowedSubs itmSymb itmDefiniendum itmDefiniens) declMap = do
  let symTyp = getSymbolType itmSymb
      symName = getSymbolName itmSymb
      symSig x = if x == symName then Just symTyp else Nothing
      l = P.union (toLanguage declMap) (P.Language symSig)
      AllowedSubs subs = itmAllowedSubs
      subsFunc x = M.findWithDefault [] x subs
  def <- first T.show $ D.mkDef itmDefiniendum itmDefiniens subsFunc l
  return $ C.DefinitionItem itmName subsFunc symTyp symName def
parseItem (Equivalence (MMLabel itmName) itmAllowedSubs itmSteps) declMap = do
  let l = toLanguage declMap
  parsedSteps <- mapM (parseProofStep l) itmSteps
  let AllowedSubs subs = itmAllowedSubs
      subsFunc x = M.findWithDefault [] x subs
      equivProof = F.EquivProof itmName subsFunc parsedSteps
      maybeMMProof = MM.fromEquivProof declMap equivProof
  mmProof <- maybe (Left "Empty theorem") Right maybeMMProof
  return $ C.EquivItem equivProof mmProof

getSymbolType :: Symbol -> P.SymbolType
getSymbolType (Predicate _ arity) = P.SymPredicate arity
getSymbolType (Function _ arity) = P.SymFunction arity
getSymbolType (Constant _) = P.SymConstant

getSymbolName :: Symbol -> T.Text
getSymbolName (Predicate name _) = name
getSymbolName (Function name _) = name
getSymbolName (Constant name) = name

parseProofStep :: P.Language -> ProofStep -> Either T.Text F.FitchStep
parseProofStep l (ProofStep prfExpr (MMLabel prfRule) prfCites) = do
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

parsePremise :: P.Language -> Premise -> Either T.Text D.Condition
parsePremise l (Premise (Just sup) cond) = do
  parsedSup <- parseExpr l sup
  parsedCond <- parseExpr l cond
  return $ D.Condition (Just parsedSup) parsedCond
parsePremise l (Premise Nothing cond) = do
  parsedCond <- parseExpr l cond
  return $ D.Condition Nothing parsedCond

parseExpr :: P.Language -> T.Text -> Either T.Text P.Wff
parseExpr l expr = case P.parseFormula l expr of
  Left err -> Left $ T.pack $ show err
  Right res -> Right res

parseCitation :: Citation -> F.Citation
parseCitation (Line i) = F.Line i
parseCitation (Range i j) = F.Range i j
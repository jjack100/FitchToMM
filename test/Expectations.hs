{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Expectations
  ( shouldBeRight,
    expr,
    shouldVerifyProof,
    shouldReportMistakes,
    shouldFail,
    verifyStmt,
    sampleSyntax,
    shouldVerifyCollection,
  )
where

import Data.Bifunctor (first)
import Data.Foldable (traverse_)
import Data.Maybe
import qualified Data.Set as S
import qualified Data.Text as T
import FitchToMM.Collection
import FitchToMM.Compressed (compressProof, packProof)
import FitchToMM.Declarations
import FitchToMM.FitchProof
import FitchToMM.MMProof
import FitchToMM.Parser
import FitchToMM.Pretty
import FitchToMM.ProofWriter
import qualified FitchToMM.Serialize as SE
import Hmm
import Prettyprinter
import Prettyprinter.Render.String
import Test.Hspec
import Test.QuickCheck
import Control.Monad (unless)

shouldVerifyProof :: T.Text -> FitchProof -> Expectation
shouldVerifyProof baseTxt theorem = shouldBeRight $ verifyProof baseTxt theorem

shouldVerifyCollection :: T.Text -> SE.Collection -> Expectation
shouldVerifyCollection baseTxt collection = shouldBeRight $ verifyCollection baseTxt collection

shouldReportMistakes :: FitchProof -> [(Int, Mistake)] -> Expectation
shouldReportMistakes theorem =
  let MMProof _ _ _ _ _ mistakes = fromJust $ fromFitchProof base theorem
   in shouldMatchList mistakes

shouldFail :: FitchProof -> Expectation
shouldFail theorem = shouldSatisfy (fromFitchProof base theorem) isNothing

shouldBeRight :: (Show a) => Either a b -> Expectation
shouldBeRight (Left err) = expectationFailure $ show err
shouldBeRight (Right _) = pure ()

verifyCollection :: T.Text -> SE.Collection -> Either String ()
verifyCollection baseTxt collection = do
  (Collection _ _ items) <- first T.unpack $ SE.parseCollection base collection
  prettied <- traverse prettyItem items
  (_, db) <- mmParseFromString $ T.unpack baseTxt ++ ' ' : (renderString $ layoutCompact $ vsep prettied)
  traverse_ snd (mmVerifiesAll db)
  return ()
  where
    prettyItem :: Item -> Either String (Doc a)
    prettyItem (TheoremItem _ prf) = do
      let mistakes = proofMistakes prf
      unless (null mistakes) (Left $ show mistakes)
      return $ prettyCompressed $ compressProof $ packProof prf
    prettyItem (DefinitionItem l _ symType symbol def) = pure $ prettyDefinition l symType symbol def
    prettyItem (EquivItem _ prf) = do
      let mistakes = proofMistakes prf
      unless (null mistakes) (Left $ show mistakes)
      return $ prettyCompressed $ compressProof $ packProof prf

verifyProof :: T.Text -> FitchProof -> Either String ()
verifyProof baseTxt theorem@(FitchProof name _ _ _) = do
  let l = T.unpack name
  -- Verify it in normal format
  let mmProof = fromJust $ fromFitchProof base theorem
  let metamath = pretty $ baseTxt <> sampleSyntaxMM
  let full = renderString $ layoutCompact $ vsep [metamath, prettyNormal mmProof]
  (_, db) <- mmParseFromString full
  mmVerifiesLabel db l
  -- Verify it in compressed format
  let mmCompressed = compressProof $ packProof $ mmProof
  let fullC = renderString $ layoutCompact $ vsep [metamath, prettyCompressed mmCompressed]
  (_, dbC) <- mmParseFromString fullC
  mmVerifiesLabel dbC l

verifyStmt :: T.Text -> T.Text -> ProofWriter -> Either String ()
verifyStmt baseTxt stmt pw = do
  let l = "proof"
      (proof, ProofProps _ dvrs) = runProofWriter pw
      prettyPrf =
        "${"
          <+> (sep $ map prettyDVR $ S.toList dvrs)
          <+> pretty l
          <+> "$p"
          <+> pretty stmt
          <+> "$="
          <+> (pretty $ T.unwords $ listStack l proof)
          <+> "$."
          <+> "$}"
      database = T.unpack $ baseTxt <> sampleSyntaxMM
  (_, db) <- mmParseFromString $ database ++ (renderString $ layoutCompact prettyPrf)
  mmVerifiesLabel db (T.unpack l)

sampleSyntax :: Language
sampleSyntax = Language $ \case
  "P" -> Just $ SymPredicate 1
  "Q" -> Just $ SymPredicate 2
  "R" -> Just $ SymPredicate 3
  "F" -> Just $ SymFunction 1
  "G" -> Just $ SymFunction 2
  "H" -> Just $ SymFunction 3
  "C" -> Just $ SymConstant
  "D" -> Just $ SymConstant
  "E" -> Just $ SymConstant
  _ -> Nothing

sampleSyntaxMM :: T.Text
sampleSyntaxMM =
  " $c P Q R F G H C D E $. \
  \ prd.P $a prd P $. \
  \ prd.Q $a prd Q $. \
  \ prd.R $a prd R $. \
  \ func.F $a func F $. \
  \ func.G $a func G $. \
  \ func.H $a func H $. \
  \ trm.C $a trm C $. \
  \ trm.D $a trm D $. \
  \ trm.E $a trm E $. "

expr :: T.Text -> Wff
expr = unsafeParseFormula $ sampleSyntax

instance Arbitrary Wff where
  arbitrary :: Gen Wff
  arbitrary = sized genWff

instance Arbitrary BinOp where
  arbitrary :: Gen BinOp
  arbitrary = elements [OpAnd, OpOr, OpImplies, OpIff]

instance Arbitrary Quantifier where
  arbitrary :: Gen Quantifier
  arbitrary = elements [QntForall, QntExists, QntUnique]

instance Arbitrary Term where
  arbitrary :: Gen Term
  arbitrary = sized genTrm

genWff :: Int -> Gen Wff
genWff 0 =
  oneof
    [ pure WffTrue,
      pure WffFalse,
      genWffMetavar
    ]
genWff n =
  frequency
    [ (2, pure WffTrue),
      (2, pure WffFalse),
      (2, genWffMetavar),
      (4, WffNot <$> sub),
      (4, WffBinOp <$> arbitrary <*> sub <*> sub),
      (3, WffQnt <$> arbitrary <*> genVar <*> sub),
      (3, genAtom),
      (2, WffSub <$> arbitrary <*> genVar <*> sub)
    ]
  where
    sub = genWff (n `div` 2)

genTrm :: Int -> Gen Term
genTrm 0 =
  oneof
    [ TrmVar <$> genVar,
      genConst,
      genTrmMetavar
    ]
genTrm n =
  frequency
    [ (1, TrmVar <$> genVar),
      (1, genConst),
      (1, genTrmMetavar),
      (2, genFunc n),
      (2, TrmSub <$> sub <*> genVar <*> sub)
    ]
  where
    sub = genTrm (n `div` 2)

genVar :: Gen T.Text
genVar = T.singleton <$> elements ['w' .. 'z']

genWffMetavar :: Gen Wff
genWffMetavar = WffMetavar <$> elements ["phi", "psi", "chi", "phi_1", "psi_1", "chi_1"]

genTrmMetavar :: Gen Term
genTrmMetavar = TrmMetavar <$> elements ["trm_1", "trm_2", "trm_3", "trm_4", "trm_5"]

genAtom :: Gen Wff
genAtom = do
  (name, ar) <- elements [("eq", 2), ("P", 1), ("Q", 2), ("R", 3)]
  terms <- vectorOf ar arbitrary
  pure $ WffAtom name terms

genFunc :: Int -> Gen Term
genFunc n = do
  (name, ar) <- elements [("F", 1), ("G", 2), ("H", 3)]
  terms <- vectorOf ar (genTrm (n `div` 2))
  pure $ TrmFunc name terms

genConst :: Gen Term
genConst = TrmConst <$> elements ["C", "D", "E"]
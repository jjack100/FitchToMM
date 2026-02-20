{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Expectations
  ( shouldBeRight,
    shouldVerifyWff,
    expr,
    shouldVerifyProof,
    shouldReportMistakes,
    shouldFail,
  )
where

import Data.Maybe
import qualified Data.Text as T
import FitchToMM.Compressed (compressProof, packProof)
import FitchToMM.Declarations
import FitchToMM.FitchProof
import FitchToMM.MMProof
import FitchToMM.Parser
import FitchToMM.Pretty
import FitchToMM.ProofWriter
import FitchToMM.SyntaxProver
import Hmm
import Prettyprinter
import Prettyprinter.Render.String
import Prettyprinter.Render.Text
import Test.Hspec

shouldVerifyWff :: T.Text -> Wff -> Expectation
shouldVerifyWff baseTxt = shouldBeRight . verifyWff baseTxt

shouldVerifyProof :: T.Text -> FitchProof -> Expectation
shouldVerifyProof baseTxt theorem = shouldBeRight $ verifyProof baseTxt theorem

shouldReportMistakes :: FitchProof -> [(Int, Mistake)] -> Expectation
shouldReportMistakes theorem =
  let MMProof _ _ _ _ _ mistakes = fromJust $ fromFitchProof base theorem
   in shouldMatchList mistakes

shouldFail :: FitchProof -> Expectation
shouldFail theorem = shouldSatisfy (fromFitchProof base theorem) isNothing

shouldBeRight :: (Show a) => Either a b -> Expectation
shouldBeRight (Left err) = expectationFailure $ show err
shouldBeRight (Right _) = pure ()

verifyProof :: T.Text -> FitchProof -> Either String ()
verifyProof baseTxt theorem@(FitchProof name _ _ _) = do
  let label = T.unpack name
  -- Verify it in normal format
  let mmProof = fromJust $ fromFitchProof base theorem
  let metamath = pretty $ baseTxt <> sampleSyntaxMM
  let full = renderString $ layoutCompact $ vsep [metamath, prettyNormal mmProof]
  (_, db) <- mmParseFromString full
  mmVerifiesLabel db label
  -- Verify it in compressed format
  let mmCompressed = compressProof $ packProof $ mmProof
  let fullC = renderString $ layoutCompact $ vsep [metamath, prettyCompressed mmCompressed]
  (_, dbC) <- mmParseFromString fullC
  mmVerifiesLabel dbC label

verifyWff :: T.Text -> Wff -> Either String ()
verifyWff baseTxt wff = do
  let label = "wff-proof"
  let sexpr = renderStrict $ layoutCompact $ prettyWff $ wff
  let (proof, _) = runProofWriter $ proveWff wff
  let metamath =
        baseTxt
          <> sampleSyntaxMM
          <> " ${ "
          <> label
          <> " $p wff "
          <> sexpr
          <> " $= "
          <> (T.unwords $ listStack label proof)
          <> " $. $} "
  (_, db) <- mmParseFromString $ T.unpack $ metamath
  mmVerifiesLabel db (T.unpack label)

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

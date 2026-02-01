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

import qualified Data.Map.Strict as M
import Data.Maybe
import qualified Data.Set as S
import qualified Data.Text as T
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
shouldVerifyWff base = shouldBeRight . verifyWff base

shouldVerifyProof :: T.Text -> FitchProof -> Expectation
shouldVerifyProof base theorem = shouldBeRight $ verifyProof base theorem

shouldReportMistakes :: FitchProof -> [(Int, Mistake)] -> Expectation
shouldReportMistakes theorem =
  let MMProof _ _ _ _ _ mistakes = fromJust $ fromFitchProof (const Nothing) theorem
   in shouldMatchList mistakes

shouldFail :: FitchProof -> Expectation
shouldFail theorem = shouldSatisfy (fromFitchProof (const Nothing) theorem) isNothing

shouldBeRight :: (Show a) => Either a b -> Expectation
shouldBeRight (Left err) = expectationFailure $ show err
shouldBeRight (Right _) = pure ()

verifyProof :: T.Text -> FitchProof -> Either String ()
verifyProof base theorem@(FitchProof name _ _ _) = do
  let mmProof = fromFitchProof (const Nothing) theorem
  let metamath = pretty $ base <> sampleSyntaxMM
  let full = renderString $ layoutCompact $ vsep [metamath, prettyNormal (fromJust mmProof)]
  let label = T.unpack $ "thm." <> name
  (_, db) <- mmParseFromString full
  mmVerifiesLabel db label

verifyWff :: T.Text -> Wff -> Either String ()
verifyWff base wff = do
  let label = "wff-proof"
  let sexpr = renderStrict $ layoutCompact $ prettyWff $ wff
  let (proof, _) = runProofWriter $ proveWff wff
  let metamath =
        base
          <> sampleSyntaxMM
          <> " ${ "
          <> label
          <> " $p wff "
          <> sexpr
          <> " $= "
          <> (T.unwords $ listStack proof)
          <> " $. $} "
  (_, db) <- mmParseFromString $ T.unpack $ metamath
  mmVerifiesLabel db (T.unpack label)

sampleSyntax :: Language
sampleSyntax =
  primitives
    <> Language
      -- Predicate Symbols
      (M.fromList [("P", 1), ("Q", 2), ("R", 3)])
      -- Function Symbols
      (M.fromList [("F", 1), ("G", 2), ("H", 3)])
      -- Constant Symbols
      (S.fromList ["C", "D", "E"])

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

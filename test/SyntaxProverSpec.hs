{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module SyntaxProverSpec (spec) where

import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Expectations
import FitchToMM.Parser
import FitchToMM.Pretty
import FitchToMM.SyntaxProver
import Paths_fitch_to_mm
import Prettyprinter (layoutCompact)
import Prettyprinter.Render.Text (renderStrict)
import Test.Hspec
import Test.Hspec.QuickCheck
import Data.Either (isRight)

spec :: Spec
spec = describe "SyntaxProver" $ do
  folPath <- runIO $ getDataFileName "fol.mm"
  folMM <- runIO $ TIO.readFile folPath
  it "correctly handles logical connectives" $ do
    shouldVerifyWff folMM (expr "( and true false )")
    shouldVerifyWff folMM (expr "( or false ( not true ) )")
    shouldVerifyWff folMM (expr "( not ( implies true ( not false ) ) )")
    shouldVerifyWff folMM (expr "( iff ( and true false) ( or false true ) )")
  it "whitespace around parens is optional" $ do
    shouldVerifyWff folMM (expr "(and true false)")
    shouldVerifyWff folMM (expr "(or false (not true))")
    shouldVerifyWff folMM (expr "(not (implies true (not false)))")
    shouldVerifyWff folMM (expr "(iff (and true false) (or false true))")
    shouldVerifyWff folMM (expr "(forall x phi)")
  it "correctly handles atomic formulae" $ do
    shouldVerifyWff folMM (expr "( P x )")
    shouldVerifyWff folMM (expr "( Q x y )")
    shouldVerifyWff folMM (expr "( R x y z )")
  prop "WFFs remain unchanged after printing and reparsing" $ reparse
  prop "Syntax proofs of WFFs should be correct" $ verifiesWff folMM

reparse :: Wff -> Bool
reparse wff =
  let txt = renderStrict $ layoutCompact $ prettyWff wff
   in case parseFormula sampleSyntax txt of
        Left _ -> False
        Right reparsed -> reparsed == wff

shouldVerifyWff :: T.Text -> Wff -> Expectation
shouldVerifyWff baseTxt wff =
  let wffPrf = proveWff wff
      stmt = "wff " <> (renderStrict $ layoutCompact $ prettyWff wff)
   in shouldBeRight $ verifyStmt baseTxt stmt wffPrf

verifiesWff :: T.Text -> Wff -> Bool
verifiesWff baseTxt wff =
  let wffPrf = proveWff wff
      stmt = "wff " <> (renderStrict $ layoutCompact $ prettyWff wff)
   in isRight $ verifyStmt baseTxt stmt wffPrf


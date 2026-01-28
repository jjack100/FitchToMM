{-# LANGUAGE OverloadedStrings #-}

module SyntaxProverSpec (spec) where

import qualified Data.Text.IO as TIO
import Expectations
import Paths_fitch_to_mm
import Test.Hspec

spec :: Spec
spec = describe "SyntaxProver" $ do
  folPath <- runIO $ getDataFileName "fol.mm"
  folMM <- runIO $ TIO.readFile folPath
  it "correctly handles logical connectives" $ do
    shouldVerifyWff folMM (expr "(and true false)")
    shouldVerifyWff folMM (expr "(or false (not true))")
    shouldVerifyWff folMM (expr "(not (implies true (not false)))")
    shouldVerifyWff folMM (expr "(iff (and true false) (or false true))")
  it "correctly handles atomic formulae" $ do
    shouldVerifyWff folMM (expr "(P x)")
    shouldVerifyWff folMM (expr "(Q x y)")
    shouldVerifyWff folMM (expr "(R x y z)")
    shouldVerifyWff folMM (expr "(R C y D)")
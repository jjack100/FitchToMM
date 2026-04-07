{-# LANGUAGE OverloadedStrings #-}

module DvrSpec (spec) where

import Expectations
import FitchToMM.Variable
import Test.Hspec

spec :: Spec
spec = describe "Disjoint variable restrictions" $ do
  it "introduces DVRs between wffs and bound variables" $ do
    shouldMatchList
      (inferDVRs (const []) (expr "( forall x phi )"))
      [mkDVR (VarHyp "x") (WffHyp "phi")]
    shouldMatchList
      (inferDVRs (const []) (expr "( exists y ( forall x phi ) )"))
      [ mkDVR (VarHyp "x") (WffHyp "phi"),
        mkDVR (VarHyp "y") (WffHyp "phi"),
        mkDVR (VarHyp "x") (VarHyp "y")
      ]

  it "introduces DVRs between terms and bound variables" $ do
    shouldMatchList
      (inferDVRs (const []) (expr "( exists x ( eq trm_1 trm_2 ) )"))
      [ mkDVR (VarHyp "x") (TrmHyp "trm_1"),
        mkDVR (VarHyp "x") (TrmHyp "trm_2")
      ]

  it "does not introduce DVRs for a wff in a different scope" $ do
    shouldMatchList
      (inferDVRs (const []) (expr "( and ( exists x phi ) psi )"))
      [ mkDVR (VarHyp "x") (WffHyp "phi")
      ]

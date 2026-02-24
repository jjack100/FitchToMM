{-# LANGUAGE OverloadedStrings #-}

module ReplacementSpec (spec) where

import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Expectations
import FitchToMM.Declarations
import FitchToMM.Parser
import FitchToMM.Pretty
import FitchToMM.ProofWriter
import FitchToMM.Replacement
import Paths_fitch_to_mm
import Prettyprinter
import Prettyprinter.Render.Text
import Test.Hspec

spec :: Spec
spec = describe "Replacement" $ do
  folPath <- runIO $ getDataFileName "fol.mm"
  folMM <- runIO $ TIO.readFile folPath
  it "is correct for simple cases" $ do
    shouldReplace folMM (const []) "( P C )" "x" "( P x )" (TrmConst "C")
    shouldReplace folMM (const []) "( P ( F C ) )" "x" "( P x )" (TrmFunc "F" [TrmConst "C"])
    shouldReplace folMM (const []) "( Q C C )" "x" "( Q x x )" (TrmConst "C")
    shouldReplace folMM (const []) "( Q y D )" "x" "( Q y x )" (TrmConst "D")
    shouldReplace folMM (const []) "( P ( G C C ) )" "x" "( P ( G x C ) )" (TrmConst "C")
    shouldReplace folMM (const []) "( iff ( P y ) ( P y ) )" "x" "( iff ( P x ) ( P x ) )" (TrmVar "y")
  it "is correct for the identity substitution" $ do
    shouldReplace folMM xInPhi "phi" "x" "phi" (TrmVar "x")
  it "replaces nothing when there are no free occurrences" $ do
    shouldReplace folMM (const []) "true" "x" "true" (TrmConst "C")
    shouldReplace folMM (const []) "false" "x" "false" (TrmConst "D")
    shouldReplace folMM (const []) "( and phi psi )" "x" "( and phi psi )" (TrmConst "E")
    shouldReplace folMM (const []) "( forall x ( P x ) )" "x" "( forall x ( P x ) ) " (TrmMetavar "trm_1")
  it "fails when trying to replace bound occurrences" $ do
    shouldNotReplace (const []) "( forall x ( P C ) )" "x" "( forall x ( P x ) ) " (TrmConst "C")
    shouldNotReplace (const []) "( forall y ( P y ) )" "x" "( forall x ( P x ) ) " (TrmVar "y")
  it "is correct when mixing free and nonfree occurrences in the same formula" $ do
    shouldReplace folMM (const []) "( and ( P C ) ( forall x ( P x ) ) )" "x" "( and ( P x ) ( forall x ( P x ) ) )" (TrmConst "C")
  it "is correct with the substitution operator for WFFs" $ do
    shouldReplace folMM (const []) "( sub a y ( Q C y ) )" "x" "( sub a y ( Q x y ) )" (TrmConst "C")
    shouldNotReplace (const []) "( sub a y ( Q x C ) )" "y" "( sub a y ( Q x y ) )" (TrmConst "C")
    shouldReplace folMM (const []) "( sub a y ( Q x y ) )" "y" "( sub a y ( Q x y ) )" (TrmConst "C")
    shouldNotReplace (const []) "( sub ( F y ) y ( Q x y ) )" "y" "( sub ( F y ) y ( Q x y ) )" (TrmConst "C")
    shouldReplace folMM (const []) "( sub ( F C ) y ( Q x y ) )" "y" "( sub ( F y ) y ( Q x y ) )" (TrmConst "C")
    shouldReplace folMM (const []) "( sub C y ( Q x y ) )" "a" "( sub a y ( Q x y ) )" (TrmConst "C")
  it "is correct with the substitution operator for terms" $ do
    shouldReplace folMM (const []) "( P ( sub a y ( G C y ) ) )" "x" "( P ( sub a y ( G x y ) ) )" (TrmConst "C")
    shouldNotReplace (const []) "( P ( sub a y ( G x C ) ) )" "y" "( P ( sub a y ( G x y ) ) )" (TrmConst "C")
    shouldReplace folMM (const []) "( P ( sub a y ( G x y ) ) )" "y" "( P ( sub a y ( G x y ) ) )" (TrmConst "C")
    shouldNotReplace (const []) "( P ( sub ( F y ) y ( G x y ) ) )" "y" "( P ( sub ( F y ) y ( G x y ) ) )" (TrmConst "C")
    shouldReplace folMM (const []) "( P ( sub ( F C ) y ( G x y ) ) )" "y" "( P ( sub ( F y ) y ( G x y ) ) )" (TrmConst "C")
    shouldReplace folMM (const []) "( P ( sub C y ( G x y ) ) )" "a" "( P ( sub a y ( G x y ) ) )" (TrmConst "C")
  it "works with WFF metavariables" $ do
    shouldReplace folMM (const []) "phi" "x" "phi" (TrmConst "C")
    shouldNotReplace xInPhi "phi" "x" "phi" (TrmConst "C")
    shouldReplace folMM xInPhi "( sub C x phi )" "x" "phi" (TrmConst "C")
    shouldReplace folMM xInPhi "phi" "y" "( sub y x phi )" (TrmVar "x")
    shouldNotReplace xyInPhi "phi" "y" "( sub y x phi )" (TrmVar "x")
    shouldReplace folMM (const []) "( sub x a false )" "a" "false" (TrmVar "x")
  it "works with term metavariables" $ do
    shouldReplace folMM (const []) "( P trm_1 )" "x" "( P trm_1 )" (TrmConst "C")
    shouldNotReplace xInTrm1 "( P trm_1 )" "x" "( P trm_1 )" (TrmConst "C")
    shouldReplace folMM xInTrm1 "( P ( sub C x trm_1 ) )" "x" "( P trm_1 )" (TrmConst "C")
    shouldReplace folMM xInTrm1 "( P trm_1 )" "y" "( P ( sub y x trm_1 ) )" (TrmVar "x")
    shouldNotReplace xyInTrm1 "( P trm_1 )" "y" "( P ( sub y x trm_1 ) )" (TrmVar "x")

xInPhi :: T.Text -> [T.Text]
xInPhi "phi" = ["x"]
xInPhi _ = []

xyInPhi :: T.Text -> [T.Text]
xyInPhi "phi" = ["x", "y"]
xyInPhi _ = []

xInTrm1 :: T.Text -> [T.Text]
xInTrm1 "trm_1" = ["x"]
xInTrm1 _ = []

xyInTrm1 :: T.Text -> [T.Text]
xyInTrm1 "trm_1" = ["x", "y"]
xyInTrm1 _ = []

shouldReplace :: T.Text -> AllowedSubs -> T.Text -> T.Text -> T.Text -> Term -> Expectation
shouldReplace baseTxt allowed wff1 var wff2 trm =
  let result = proveReplWff allowed (expr wff1) var (expr wff2) trm
      trmTxt = renderStrict $ layoutCompact $ prettyTrm trm
      stmt = "; " <> wff1 <> " REPLACES " <> var <> " IN " <> wff2 <> " WITH " <> trmTxt
   in if (failed result)
        then expectationFailure "Failed to prove replacement"
        else shouldBeRight $ verifyStmt baseTxt stmt result

shouldNotReplace :: AllowedSubs -> T.Text -> T.Text -> T.Text -> Term -> Expectation
shouldNotReplace allowed wff1 var wff2 trm =
  let result = proveReplWff allowed (expr wff1) var (expr wff2) trm
   in shouldSatisfy result failed
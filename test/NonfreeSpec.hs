{-# LANGUAGE OverloadedStrings #-}

module NonfreeSpec (spec) where

import Data.Either
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Expectations
import FitchToMM.Declarations
import FitchToMM.Matcher
import FitchToMM.Nonfree
import FitchToMM.Parser
import FitchToMM.Pretty
import FitchToMM.ProofWriter
import Paths_fitch_to_mm
import Prettyprinter
import Prettyprinter.Render.String
import Prettyprinter.Render.Text
import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck

spec :: Spec
spec = describe "Nonfreeness Prover" $ do
  folPath <- runIO $ getDataFileName "fol.mm"
  folMM <- runIO $ TIO.readFile folPath
  it "proves variables that do not occur in a WFF are nonfree" $ do
    shouldBeNonfree folMM (const []) "x" "false"
    shouldBeNonfree folMM (const []) "x" "phi"
    shouldBeNonfree folMM (const []) "y" "( and true false )"
    shouldBeNonfree folMM (const []) "z" "( or true false )"
    shouldBeNonfree folMM (const []) "x" "( implies true false )"
    shouldBeNonfree folMM (const []) "x" "( iff true false )"
    shouldBeNonfree folMM (const []) "x" "( not phi )"
    shouldBeNonfree folMM (const []) "x" "( not ( not phi ) )"
    shouldBeNonfree folMM (const []) "x" "( not ( not ( and phi true ) ) )"
    shouldBeNonfree folMM (const []) "x" "( eq y z )"
    shouldBeNonfree folMM (const []) "x" "( eq C D )"
    shouldBeNonfree folMM (const []) "x" "( eq y ( G z w ) )"
    shouldBeNonfree folMM xInPhi "y" "phi"
    shouldBeNonfree folMM xInPhi "x" "psi"
  it "proves variables bound by a quantifier are nonfree" $ do
    shouldBeNonfree folMM (const []) "x" "( forall x ( P x ) )"
    shouldBeNonfree folMM (const []) "x" "( exists x ( P x ) )"
    shouldBeNonfree folMM (const []) "x" "( unique x ( P x ) )"
    shouldBeNonfree folMM (const []) "y" "( or ( not true ) ( unique y chi ) )"
    shouldBeNonfree folMM (const []) "w" "( unique z ( forall w ( not ( not phi ) ) ) )"
    shouldBeNonfree folMM (const []) "w" "( sub E y ( forall z ( unique w ( sub z w ( P trm_3 ) ) ) ) )"
  it "proves variables removed by substitution in a WFF are nonfree" $ do
    shouldBeNonfree folMM (const []) "x" "( sub y x ( P x ) )"
    shouldBeNonfree folMM (const []) "x" "( sub trm_1 x ( P x ) )"
    shouldBeNonfree folMM (const []) "x" "( sub y x ( eq x x ) )"
    shouldBeNonfree folMM (const []) "x" "( sub y x ( eq y ( F x ) ) )"
  it "proves variables removed by substitution in a term are nonfree" $ do
    shouldBeNonfree folMM (const []) "x" "( P ( sub y x x ) )"
    shouldBeNonfree folMM (const []) "z" "( R trm_2 ( sub ( F trm_2 ) w ( sub D z E ) ) E )"
  it "cannot prove nonfreeness for free variables in a WFF" $ do
    shouldBeFree (const []) "x" "( P x )"
    shouldBeFree (const []) "x" "( eq x x )"
    shouldBeFree (const []) "x" "( not ( eq x y ) )"
    shouldBeFree xInPhi "x" "phi"
    shouldBeFree xInPhi "x" "( and phi psi )"
    shouldBeFree (const []) "x" "( and ( P x ) ( forall x ( P x ) ) )"
  it "treats variables in the scope of a quantifier that binds to a different variable as still free" $ do
    shouldBeFree (const []) "x" "( forall y ( P x ) )"
    shouldBeFree (const []) "x" "( exists y ( Q x y ) )"
    shouldBeFree (const []) "x" "( unique y ( R x y z ) )"
  it "treats variables in the scope of a substitution that replaces a different variable as still free" $ do
    shouldBeFree (const []) "x" "( sub trm_1 y ( Q x y ) )"
    shouldBeFree (const []) "x" "( sub z y ( R x y z ) )"
  it "treats variables free in a term inserted by substitution as free" $ do
    shouldBeFree (const []) "x" "( sub x y ( eq y y ) )"
    shouldBeFree (const []) "x" "( sub ( G x y ) y ( eq y y ) )"
    shouldBeFree xInTrm1 "x" "( sub trm_1 y ( eq y y ) )"
  it "can prove nonfreeness for contexts" $ do
    shouldBeNonfreeCtx folMM (const []) "x" []
    shouldBeNonfreeCtx folMM (const []) "y" ["( and true false )"]
    shouldBeNonfreeCtx folMM (const []) "x" ["( forall x ( P x ) )"]
    shouldBeNonfreeCtx folMM (const []) "x" ["( and true false )", "( forall x ( P x ) )"]
    shouldBeNonfreeCtx folMM (const []) "x" ["( forall x ( P x ) )", "( exists x ( P x ) )", "( unique x ( P x ) )"]
  prop "Nonfreeness proofs should be correct for WFFs" $ verifiesNonfreeWff folMM
  prop "Nonfreeness proofs should be correct for lists" $ verifiesNonfreeLst folMM

xInPhi :: T.Text -> [T.Text]
xInPhi "phi" = ["x"]
xInPhi _ = []

xInTrm1 :: T.Text -> [T.Text]
xInTrm1 "trm_1" = ["x"]
xInTrm1 _ = []

shouldBeNonfree :: T.Text -> AllowedSubs -> T.Text -> T.Text -> Expectation
shouldBeNonfree baseTxt allowed var wff =
  let result = proveNfWff allowed var (expr wff)
      stmt = "; NONFREE " <> var <> " " <> wff
   in if (failed result)
        then expectationFailure "Failed to prove nonfreeness"
        else shouldBeRight $ verifyStmt baseTxt stmt result

shouldBeNonfreeCtx :: T.Text -> AllowedSubs -> T.Text -> [T.Text] -> Expectation
shouldBeNonfreeCtx baseTxt allowed var wffs =
  let ctx = RelContext $ reverse $ map expr wffs
      result = proveNfCtx allowed var ctx
      ctxTxt = "... " <> T.unwords wffs
      stmt = "; NONFREE " <> var <> " " <> ctxTxt
   in if (failed result)
        then expectationFailure "Failed to prove nonfreeness"
        else shouldBeRight $ verifyStmt baseTxt stmt result

shouldBeFree :: AllowedSubs -> T.Text -> T.Text -> Expectation
shouldBeFree allowed var wff =
  let result = proveNfWff allowed var (expr wff)
   in shouldSatisfy result failed

-- If a nonfreeness proof for a WFF reports success, it should be verifiable
verifiesNonfreeWff :: T.Text -> NonfreeWff -> Bool
verifiesNonfreeWff baseTxt (NonfreeWff allowed var wff) =
  let proof = proveNfWff allowed var wff
      wffTxt = renderStrict $ layoutCompact $ prettyWff wff
      stmt = "; NONFREE " <> var <> " " <> wffTxt
   in if succeeded proof
        then isRight $ verifyStmt baseTxt stmt proof
        else True

-- If a nonfreeness proof for a list reports success, it should be verifiable
verifiesNonfreeLst :: T.Text -> NonfreeLst -> Bool
verifiesNonfreeLst baseTxt (NonfreeLst allowed var lst) =
  let proof = proveNfLst allowed var lst
      render = renderStrict . layoutCompact . prettyTrm
      lstStr = T.unwords $ map render lst
      stmt = "; NONFREE " <> var <> " " <> lstStr
   in if succeeded proof
        then isRight $ verifyStmt baseTxt stmt proof
        else True

data NonfreeWff = NonfreeWff AllowedSubs T.Text Wff

instance Show NonfreeWff where
  show (NonfreeWff _ var wff) =
    let wffStr = renderString $ layoutPretty defaultLayoutOptions $ prettyWff wff
     in "; NONFREE " <> T.unpack var <> " " <> wffStr

instance Arbitrary NonfreeWff where
  arbitrary = do
    wff <- arbitrary
    let allVars = S.toList $ varsInWff wff
        setvars = map fHypName $ filter isSetvar allVars
        metavars = map fHypName $ filter isMetavar allVars
    subs <- infiniteListOf $ sublistOf setvars
    let subMap = M.fromList $ zip metavars subs
        allowedSubs = \k -> M.findWithDefault [] k subMap
    var <- if null setvars then pure "x" else elements setvars
    return $ NonfreeWff allowedSubs var wff

data NonfreeLst = NonfreeLst AllowedSubs T.Text [Term]

instance Show NonfreeLst where
  show (NonfreeLst _ var lst) =
    let render = renderString . layoutPretty defaultLayoutOptions . prettyTrm
        lstStr = unwords $ map render lst
     in "; NONFREE " <> T.unpack var <> " " <> lstStr

instance Arbitrary NonfreeLst where
  arbitrary = do
    lst <- listOf1 arbitrary
    let allVars = S.toList $ varsInLst lst
        setvars = map fHypName $ filter isSetvar allVars
        metavars = map fHypName $ filter isMetavar allVars
    subs <- infiniteListOf $ sublistOf setvars
    let subMap = M.fromList $ zip metavars subs
        allowedSubs = \k -> M.findWithDefault [] k subMap
    var <- if null setvars then pure "x" else elements setvars
    return $ NonfreeLst allowedSubs var lst
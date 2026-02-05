{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module MMProofSpec (spec) where

import qualified Data.Text.IO as TIO
import Expectations
import FitchToMM.FitchProof
import FitchToMM.ProofWriter
import Paths_fitch_to_mm
import Test.Hspec

spec :: Spec
spec = describe "FitchProver" $ do
  folPath <- runIO $ getDataFileName "fol.mm"
  folMM <- runIO $ TIO.readFile folPath

  let noneFree = const []

  describe "Propositional Logic" $ do
    it "correctly handles a simple subproof" $ do
      let theorem =
            FitchProof
              "simple"
              noneFree
              []
              [ FitchSubproof (expr "phi") [],
                FitchStep (expr "( implies phi phi )") "axm.implies-intr" [Range 1 1]
              ]
      shouldVerifyProof folMM theorem

    it "correctly handles thinning on reiteration" $ do
      let theorem =
            FitchProof
              "reiteration-example"
              noneFree
              [Condition Nothing (expr "phi")]
              [ FitchSubproof
                  (expr "true")
                  [ FitchStep (expr "phi") "reiteration" [Line 1]
                  ],
                FitchStep (expr "( implies true phi )") "axm.implies-intr" [Range 2 3]
              ]
      shouldVerifyProof folMM theorem

    it "correctly handles a nested subproof" $ do
      let theorem =
            FitchProof
              "nested"
              noneFree
              []
              [ FitchSubproof
                  (expr "(not phi)")
                  [ FitchSubproof
                      (expr "phi")
                      [FitchStep (expr "false") "axm.not-elim" [Line 2, Line 1]],
                    FitchStep (expr "(not phi)") "axm.not-intr" [Range 2 3]
                  ],
                FitchStep (expr "(implies (not phi) (not phi))") "axm.implies-intr" [Range 1 4]
              ]
      shouldVerifyProof folMM theorem

    it "can use suppositional premise" $ do
      let theorem =
            FitchProof
              "supposition-example"
              noneFree
              [Condition (Just $ expr "phi") (expr "psi")]
              [FitchStep (expr "( implies phi psi )") "axm.implies-intr" [Range 1 2]]
      shouldVerifyProof folMM theorem

    it "can use conjunction introduction" $ do
      let theorem =
            FitchProof
              "and-intr-example"
              noneFree
              [ Condition Nothing (expr "phi"),
                Condition Nothing (expr "psi"),
                Condition Nothing (expr "chi")
              ]
              [ FitchStep (expr "( and phi psi )") "axm.and-intr" [Line 1, Line 2],
                FitchStep (expr "( and chi ( and phi psi ) )") "axm.and-intr" [Line 3, Line 4]
              ]
      shouldVerifyProof folMM theorem

    it "can use disjunction introduction" $ do
      let theorem =
            FitchProof
              "or-intr-example"
              noneFree
              [Condition Nothing (expr "phi")]
              [ FitchStep (expr "( or phi psi )") "axm.or-intr" [Line 1],
                FitchStep (expr "( or chi ( or phi psi ) )") "axm.or-intr" [Line 2]
              ]
      shouldVerifyProof folMM theorem

    it "can use implication introduction" $ do
      let theorem =
            FitchProof
              "impl-intr-example"
              noneFree
              [Condition Nothing (expr "phi")]
              [ FitchSubproof
                  (expr "psi")
                  [FitchStep (expr "phi") "reiteration" [Line 1]],
                FitchStep (expr "( implies psi phi )") "axm.implies-intr" [Range 2 3]
              ]
      shouldVerifyProof folMM theorem

    it "can use biconditional introduction" $ do
      let theorem =
            FitchProof
              "iff-intr-example"
              noneFree
              [ Condition Nothing (expr "( implies phi psi )"),
                Condition Nothing (expr "( implies psi phi )")
              ]
              [ FitchSubproof
                  (expr "phi")
                  [FitchStep (expr "psi") "axm.implies-elim" [Line 1, Line 3]],
                FitchSubproof
                  (expr "psi")
                  [FitchStep (expr "phi") "axm.implies-elim" [Line 2, Line 5]],
                FitchStep (expr "( iff phi psi )") "axm.iff-intr" [Range 3 4, Range 5 6]
              ]
      shouldVerifyProof folMM theorem

    it "can use negation introduction" $ do
      let theorem =
            FitchProof
              "not-intr-example"
              noneFree
              [Condition Nothing (expr "phi")]
              [ FitchSubproof
                  (expr "( not phi )")
                  [FitchStep (expr "false") "axm.not-elim" [Line 1, Line 2]],
                FitchStep (expr "( not ( not phi ) )") "axm.not-intr" [Range 2 3]
              ]
      shouldVerifyProof folMM theorem

    it "can use verum introduction" $ do
      let theorem =
            FitchProof
              "true-intr-example"
              noneFree
              []
              [FitchStep (expr "true") "axm.true-intr" []]
      shouldVerifyProof folMM theorem

    it "can use conjunction elimination" $ do
      let theorem =
            FitchProof
              "and-elim-example"
              noneFree
              [Condition Nothing (expr "( and ( implies phi psi ) phi )")]
              [ FitchStep (expr "( implies phi psi )") "axm.and-elim" [Line 1],
                FitchStep (expr "phi") "axm.and-elim" [Line 1],
                FitchStep (expr "psi") "axm.implies-elim" [Line 2, Line 3]
              ]
      shouldVerifyProof folMM theorem

    it "can use disjunction elimination" $ do
      let theorem =
            FitchProof
              "or-elim-example"
              noneFree
              [ Condition Nothing (expr "( or phi psi )"),
                Condition Nothing (expr "( implies phi chi )"),
                Condition Nothing (expr "( implies psi chi )")
              ]
              [ FitchSubproof
                  (expr "phi")
                  [FitchStep (expr "chi") "axm.implies-elim" [Line 2, Line 4]],
                FitchSubproof
                  (expr "psi")
                  [FitchStep (expr "chi") "axm.implies-elim" [Line 3, Line 6]],
                FitchStep (expr "chi") "axm.or-elim" [Line 1, Range 4 5, Range 6 7]
              ]
      shouldReportMistakes theorem []
      shouldVerifyProof folMM theorem

    it "can use implication elimination" $ do
      let theorem =
            FitchProof
              "implies-elim-example"
              noneFree
              [ Condition Nothing (expr "( implies phi psi )"),
                Condition Nothing (expr "phi")
              ]
              [FitchStep (expr "psi") "axm.implies-elim" [Line 1, Line 2]]
      shouldVerifyProof folMM theorem

    it "can use biconditional elimination" $ do
      let theorem1 =
            FitchProof
              "iff-elim-example-1"
              noneFree
              [ Condition Nothing (expr "( iff phi psi )"),
                Condition Nothing (expr "phi")
              ]
              [FitchStep (expr "psi") "axm.iff-elim" [Line 1, Line 2]]
      let theorem2 =
            FitchProof
              "iff-elim-example-2"
              noneFree
              [ Condition Nothing (expr "( iff phi psi )"),
                Condition Nothing (expr "psi")
              ]
              [FitchStep (expr "phi") "axm.iff-elim" [Line 1, Line 2]]
      shouldVerifyProof folMM theorem1
      shouldVerifyProof folMM theorem2

    it "can use negation elimination" $ do
      let theorem =
            FitchProof
              "neg-elim-example"
              noneFree
              [Condition Nothing (expr "phi"), Condition Nothing (expr "(not phi)")]
              [FitchStep (expr "false") "axm.not-elim" [Line 1, Line 2]]
      shouldVerifyProof folMM theorem

    it "can prove the law of excluded middle" $ do
      let theorem =
            FitchProof
              "lem"
              noneFree
              []
              [ FitchSubproof
                  (expr "( not ( or phi ( not phi ) ) )")
                  [ FitchSubproof
                      (expr "phi")
                      [ FitchStep (expr "( or phi ( not phi ) )") "axm.or-intr" [Line 2],
                        FitchStep (expr "false") "axm.not-elim" [Line 3, Line 1]
                      ],
                    FitchStep (expr "( not phi )") "axm.not-intr" [Range 2 4],
                    FitchStep (expr "( or phi ( not phi ) )") "axm.or-intr" [Line 5],
                    FitchStep (expr "false") "axm.not-elim" [Line 6, Line 1]
                  ],
                FitchStep (expr "( or phi ( not phi ) )") "axm.ip" [Range 1 7]
              ]
      shouldVerifyProof folMM theorem

  describe "Predicate Logic" $ do
    it "can use universal introduction" $ do
      let theorem =
            FitchProof
              "forall-intr-example"
              noneFree
              []
              [ FitchStep (expr "( eq a a )") "axm.eq-intr" [],
                FitchStep (expr "( forall x ( eq x x ) )") "axm.forall-intr" [Line 1]
              ]
      shouldVerifyProof folMM theorem

    it "can use universal introduction when the variable does not occur" $ do
      let theorem =
            FitchProof
              "forall-intr-example-2"
              noneFree
              [Condition Nothing (expr "phi")]
              [FitchStep (expr "( forall z phi )") "axm.forall-intr" [Line 1]]
      shouldVerifyProof folMM theorem

    it "can use existential introduction" $ do
      let theorem =
            FitchProof
              "exists-intr-example"
              noneFree
              []
              [ FitchStep (expr "( eq a a )") "axm.eq-intr" [],
                FitchStep (expr "( exists x ( eq x a ) )") "axm.exists-intr" [Line 1],
                FitchStep (expr "( exists y ( exists x ( eq x y ) ) )") "axm.exists-intr" [Line 2]
              ]
      shouldVerifyProof folMM theorem

    it "can use existential introduction when the variable does not occur" $ do
      let theorem1 =
            FitchProof
              "exists-intr-example-2"
              noneFree
              [Condition Nothing (expr "phi")]
              [FitchStep (expr "( exists x phi )") "axm.exists-intr" [Line 1]]
      shouldVerifyProof folMM theorem1

    it "can use equality introduction" $ do
      let theorem =
            FitchProof
              "eq-intr-example"
              noneFree
              []
              [FitchStep (expr "( eq (F C) (F C) )") "axm.eq-intr" []]
      shouldVerifyProof folMM theorem

    it "can use universal elimination" $ do
      let theorem =
            FitchProof
              "universal-elim-example"
              noneFree
              [Condition Nothing (expr "( forall x ( Q x x ) )")]
              [FitchStep (expr "( Q C C )") "axm.forall-elim" [Line 1]]
      shouldVerifyProof folMM theorem

    it "can use existential elimination" $ do
      let theorem =
            FitchProof
              "exists-elim-example"
              noneFree
              [ Condition Nothing (expr "(forall x (implies (P x) (P(F x))))"),
                Condition Nothing (expr "(exists x (P x))")
              ]
              [ FitchSubproof
                  (expr "(P a)")
                  [ FitchStep (expr "( implies (P a) (P(F a)) )") "axm.forall-elim" [Line 1],
                    FitchStep (expr "(P(F a))") "axm.implies-elim" [Line 4, Line 3],
                    FitchStep (expr "( exists x (P(F x)) )") "axm.exists-intr" [Line 5]
                  ],
                FitchStep (expr "( exists x (P(F x)) )") "axm.exists-elim" [Line 2, Range 3 6]
              ]
      shouldVerifyProof folMM theorem

    it "can use equality elimination" $ do
      let theorem1 =
            FitchProof
              "eq-elim-example"
              noneFree
              [ Condition Nothing (expr "( eq C D )"),
                Condition Nothing (expr "( R C C E )")
              ]
              [FitchStep (expr "( R C D E )") "axm.eq-elim" [Line 1, Line 2]]
      shouldVerifyProof folMM theorem1
      let theorem2 =
            FitchProof
              "eq-example-2"
              noneFree
              [ Condition Nothing (expr "( eq C D )"),
                Condition Nothing (expr "( R D D E )")
              ]
              [FitchStep (expr "( R C D E )") "axm.eq-elim" [Line 1, Line 2]]
      shouldVerifyProof folMM theorem2

    it "can use universal quantification with implication" $ do
      let theorem =
            FitchProof
              "forall-implies-example"
              ( \case
                  "chi" -> ["x"]
                  _ -> []
              )
              [ Condition Nothing (expr "(forall x ( implies phi psi ))"),
                Condition Nothing (expr "(implies psi chi)")
              ]
              [ FitchStep (expr "(implies phi psi)") "axm.forall-elim" [Line 1],
                FitchSubproof
                  (expr "phi")
                  [ FitchStep (expr "psi") "axm.implies-elim" [Line 3, Line 4],
                    FitchStep (expr "chi") "axm.implies-elim" [Line 2, Line 5]
                  ],
                FitchStep (expr "(implies phi chi)") "axm.implies-intr" [Range 4 6],
                FitchStep (expr "(forall x (implies phi chi))") "axm.forall-intr" [Line 7]
              ]
      shouldVerifyProof folMM theorem

  describe "Validation of citations" $ do
    it "rejects citations of nonexistent lines" $ do
      let theorem =
            FitchProof
              "cite-nonexistent"
              noneFree
              []
              [ FitchStep (expr "phi") "axm.false-elim" [Line 0],
                FitchStep (expr "psi") "axm.false-elim" [Line 3]
              ]
      shouldReportMistakes theorem [(0, CitesNonexistent), (1, CitesNonexistent)]

    it "rejects a line that cites itself" $ do
      let theorem =
            FitchProof
              "self-cite"
              noneFree
              []
              [FitchStep (expr "phi") "reiteration" [Line 1]]
      shouldReportMistakes theorem [(0, CitesSelf)]

    it "rejects a line that cites a later line" $ do
      let theorem =
            FitchProof
              "cites-later"
              noneFree
              []
              [ FitchStep (expr "phi") "axm.false-elim" [Line 3],
                FitchStep (expr "( not phi )") "axm.false-elim" [Line 3],
                FitchStep (expr "false") "axm.not-elim" [Line 1, Line 2]
              ]
      shouldReportMistakes theorem [(0, CitesLater), (1, CitesLater)]

    it "rejects a citation of a discharged assumption" $ do
      let theorem =
            FitchProof
              "cites-undischarged"
              noneFree
              []
              [ FitchSubproof (expr "phi") [],
                FitchStep (expr "( or phi psi )") "axm.or-intr" [Line 1]
              ]
      shouldReportMistakes theorem [(1, CitesDischarged)]

    it "rejects bad use of false-elim" $ do
      let theorem =
            FitchProof
              "bad-thm"
              noneFree
              []
              [ FitchSubproof
                  (expr "(not phi)")
                  [ FitchSubproof
                      (expr "phi")
                      [FitchStep (expr "false") "axm.not-elim" [Line 2, Line 1]],
                    FitchStep (expr "false") "axm.false-elim" [Range 2 3]
                  ],
                FitchStep (expr "false") "axm.false-elim" [Range 1 4]
              ]
      shouldReportMistakes theorem [(3, Inapplicable), (4, Inapplicable)]

  it "rejects a proof missing a conclusion" $ do
    let theorem =
          FitchProof
            "missing-conclusion"
            noneFree
            [Condition Nothing (expr "phi"), Condition Nothing (expr "psi")]
            []
    shouldFail theorem

  it "rejects an empty proof" $ do
    let theorem =
          FitchProof
            "empty"
            noneFree
            []
            []
    shouldFail theorem
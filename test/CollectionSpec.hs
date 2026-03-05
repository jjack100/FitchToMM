{-# LANGUAGE OverloadedStrings #-}

module CollectionSpec (spec) where

import qualified Data.Map.Strict as M
import qualified Data.Text.IO as TIO
import Expectations (shouldVerifyCollection)
import FitchToMM.Serialize
import Paths_fitch_to_mm
import Test.Hspec

spec :: Spec
spec = describe "Collections" $ do
  folPath <- runIO $ getDataFileName "fol.mm"
  folMM <- runIO $ TIO.readFile folPath

  describe "Reference" $ do
    it "can reference a previous theorem" $ do
      let itms =
            [ Theorem
                (MMLabel "thm.example-1")
                (AllowedSubs M.empty)
                []
                [ Subproof "phi" [],
                  ProofStep
                    "( implies phi phi )"
                    (MMLabel "axm.implies-intr")
                    [Range 1 1]
                ],
              Theorem
                (MMLabel "thm.example-2")
                (AllowedSubs M.empty)
                []
                [ ProofStep
                    "( implies ( not phi ) ( not phi ) )"
                    (MMLabel "thm.example-1")
                    []
                ]
            ]
      shouldVerifyCollection folMM (Collection "" itms)

    it "can reference a previous theorem with a premise" $ do
      let itms =
            [ Theorem
                (MMLabel "thm.example-1")
                (AllowedSubs M.empty)
                [Premise Nothing "phi"]
                [ Subproof
                    "psi"
                    [ ProofStep
                        "phi"
                        (MMLabel "reiteration")
                        [Line 1]
                    ],
                  ProofStep
                    "( implies psi phi )"
                    (MMLabel "axm.implies-intr")
                    [Range 2 3]
                ],
              Theorem
                (MMLabel "thm.example-2")
                (AllowedSubs M.empty)
                [Premise Nothing "( not phi )"]
                [ ProofStep
                    "( implies phi ( not phi ) )"
                    (MMLabel "thm.example-1")
                    [Line 1]
                ]
            ]
      shouldVerifyCollection folMM (Collection "" itms)

    it "can reference a previous theorem with a suppositional premise" $ do
      let itms =
            [ Theorem
                (MMLabel "thm.example-1")
                (AllowedSubs M.empty)
                [Premise (Just "( not phi )") "phi"]
                [ ProofStep
                    "( implies ( not phi ) phi )"
                    (MMLabel "axm.implies-intr")
                    [Range 1 2],
                  Subproof
                    "( not phi )"
                    [ ProofStep
                        "phi"
                        (MMLabel "axm.implies-elim")
                        [Line 3, Line 4],
                      ProofStep
                        "false"
                        (MMLabel "axm.not-elim")
                        [Line 5, Line 4]
                    ],
                  ProofStep
                    "phi"
                    (MMLabel "axm.ip")
                    [Range 4 6]
                ],
              Theorem
                (MMLabel "thm.example-2")
                (AllowedSubs M.empty)
                [Premise Nothing "( implies ( not psi ) psi )"]
                [ Subproof
                    "( not psi )"
                    [ ProofStep
                        "psi"
                        (MMLabel "axm.implies-elim")
                        [Line 1, Line 2]
                    ],
                  ProofStep
                    "psi"
                    (MMLabel "thm.example-1")
                    [Range 2 3]
                ]
            ]
      shouldVerifyCollection folMM (Collection "" itms)

  describe "Definition" $ do
    it "can use definiendum introduction" $ do
      let itms =
            exampleDef
              ++ [ Theorem
                     (MMLabel "thm.example")
                     (AllowedSubs M.empty)
                     [Premise Nothing "( not ( eq trm_1 trm_2 ) )"]
                     [ ProofStep
                         "( neq trm_1 trm_2 )"
                         (MMLabel "def.neq")
                         [Line 1]
                     ]
                 ]
      shouldVerifyCollection folMM (Collection "" itms)
    it "can use definiendum elimination" $ do
      let itms =
            exampleDef
              ++ [ Theorem
                     (MMLabel "thm.example")
                     (AllowedSubs M.empty)
                     [Premise Nothing "( neq trm_1 trm_2 )"]
                     [ ProofStep
                         "( not ( eq trm_1 trm_2 ) )"
                         (MMLabel "def.neq")
                         [Line 1]
                     ]
                 ]
      shouldVerifyCollection folMM (Collection "" itms)

  describe "Equivalence" $ do
    it "correctly uses an equivalence" $ do
      let itms =
            exampleDeMorgan
              ++ [ Theorem
                     (MMLabel "thm.example-1")
                     (AllowedSubs M.empty)
                     [Premise Nothing "( not ( or phi psi ) )"]
                     [ ProofStep
                         "( and ( not phi ) ( not psi ) )"
                         (MMLabel "eqv.dem")
                         [Line 1]
                     ],
                   Theorem
                     (MMLabel "thm.example-2")
                     (AllowedSubs M.empty)
                     [Premise Nothing "( and ( not phi ) ( not psi ) )"]
                     [ ProofStep
                         "( not ( or phi psi ) )"
                         (MMLabel "eqv.dem")
                         [Line 1]
                     ]
                 ]
      shouldVerifyCollection folMM (Collection "" itms)

    it "correctly uses an equivalence on a subexpression inside a quantifier" $ do
      let itms =
            exampleDeMorgan
              ++ [ Theorem
                     (MMLabel "thm.example-1")
                     (AllowedSubs $ M.fromList [("phi", ["x"]), ("psi", ["x"])])
                     [Premise Nothing "( forall x ( not ( or phi psi ) ) )"]
                     [ ProofStep
                         "( forall x ( and ( not phi ) ( not psi ) ) )"
                         (MMLabel "eqv.dem")
                         [Line 1]
                     ],
                   Theorem
                     (MMLabel "thm.example-2")
                     (AllowedSubs $ M.fromList [("phi", ["x"]), ("psi", ["x"])])
                     [Premise Nothing "( forall x ( and ( not phi ) ( not psi ) ) )"]
                     [ ProofStep
                         "( forall x ( not ( or phi psi ) ) )"
                         (MMLabel "eqv.dem")
                         [Line 1]
                     ]
                 ]
      shouldVerifyCollection folMM (Collection "" itms)

    it "correctly uses an equivalence on a subexpression inside negation" $ do
      let itms =
            exampleDeMorgan
              ++ [ Theorem
                     (MMLabel "thm.example")
                     (AllowedSubs M.empty)
                     [Premise Nothing "( not ( not ( or phi psi ) ) )"]
                     [ ProofStep
                         "( not ( and ( not phi ) ( not psi ) ) )"
                         (MMLabel "eqv.dem")
                         [Line 1]
                     ]
                 ]
      shouldVerifyCollection folMM (Collection "" itms)

    it "correctly uses an equivalence on a subexpression inside a substitution" $ do
      let itms =
            exampleDeMorgan
              ++ [ Theorem
                     (MMLabel "thm.example")
                     (AllowedSubs $ M.fromList [("phi", ["x"]), ("psi", ["x"])])
                     [Premise Nothing "( sub trm_1 x ( not ( or phi psi ) ) )"]
                     [ ProofStep
                         "( sub trm_1 x ( and ( not phi ) ( not psi ) ) )"
                         (MMLabel "eqv.dem")
                         [Line 1]
                     ]
                 ]
      shouldVerifyCollection folMM (Collection "" itms)

    it "correctly uses an equivalence on a subexpression inside a binary connective" $ do
      let itms =
            exampleDeMorgan
              ++ [ Theorem
                     (MMLabel "thm.example")
                     (AllowedSubs M.empty)
                     [Premise Nothing "( implies ( not ( or phi psi ) ) ( not ( or phi psi ) ) )"]
                     [ ProofStep
                         "( implies ( and ( not phi ) ( not psi ) ) ( and ( not phi ) ( not psi ) ) )"
                         (MMLabel "eqv.dem")
                         [Line 1]
                     ]
                 ]
      shouldVerifyCollection folMM (Collection "" itms)

    it "correctly uses an equivalence on only some occurrences" $ do
      let itms =
            exampleDeMorgan
              ++ [ Theorem
                     (MMLabel "thm.example")
                     (AllowedSubs M.empty)
                     [Premise Nothing "( implies ( not ( or phi psi ) ) ( not ( or phi psi ) ) )"]
                     [ ProofStep
                         "( implies ( and ( not phi ) ( not psi ) ) ( not ( or phi psi ) ) )"
                         (MMLabel "eqv.dem")
                         [Line 1]
                     ]
                 ]
      shouldVerifyCollection folMM (Collection "" itms)

-- Example definition for "not equal to"
exampleDef :: [Item]
exampleDef =
  [ Definition
      (MMLabel "def.neq")
      (AllowedSubs M.empty)
      (Predicate "neq" 2)
      "( neq trm_1 trm_2 )"
      "( not ( eq trm_1 trm_2 ) )"
  ]

-- Example theorems/equivalence demonstrating some of De Morgan's laws
exampleDeMorgan :: [Item]
exampleDeMorgan =
  [ Theorem
      (MMLabel "thm.dem-1")
      (AllowedSubs M.empty)
      [Premise Nothing "( not ( or phi psi ) )"]
      [ Subproof
          "phi"
          [ ProofStep
              "( or phi psi )"
              (MMLabel "axm.or-intr")
              [Line 2],
            ProofStep
              "false"
              (MMLabel "axm.not-elim")
              [Line 3, Line 1]
          ],
        Subproof
          "psi"
          [ ProofStep
              "( or phi psi )"
              (MMLabel "axm.or-intr")
              [Line 5],
            ProofStep
              "false"
              (MMLabel "axm.not-elim")
              [Line 6, Line 1]
          ],
        ProofStep
          "( not phi )"
          (MMLabel "axm.not-intr")
          [Range 2 4],
        ProofStep
          "( not psi )"
          (MMLabel "axm.not-intr")
          [Range 5 7],
        ProofStep
          "( and ( not phi ) ( not psi ) )"
          (MMLabel "axm.and-intr")
          [Line 8, Line 9]
      ],
    Theorem
      (MMLabel "thm.dem-2")
      (AllowedSubs M.empty)
      [Premise Nothing "( and ( not phi ) ( not psi ) )"]
      [ Subproof
          "( or phi psi )"
          [ Subproof
              "phi"
              [ ProofStep
                  "( not phi )"
                  (MMLabel "axm.and-elim")
                  [Line 1],
                ProofStep
                  "false"
                  (MMLabel "axm.not-elim")
                  [Line 3, Line 4]
              ],
            Subproof
              "psi"
              [ ProofStep
                  "( not psi )"
                  (MMLabel "axm.and-elim")
                  [Line 1],
                ProofStep
                  "false"
                  (MMLabel "axm.not-elim")
                  [Line 6, Line 7]
              ],
            ProofStep
              "false"
              (MMLabel "axm.or-elim")
              [Line 2, Range 3 5, Range 6 8]
          ],
        ProofStep
          "( not ( or phi psi ) )"
          (MMLabel "axm.not-intr")
          [Range 2 9]
      ],
    Equivalence
      (MMLabel "eqv.dem")
      (AllowedSubs M.empty)
      [ Subproof
          "( not ( or phi psi ) )"
          [ ProofStep
              "( and ( not phi ) ( not psi ) )"
              (MMLabel "thm.dem-1")
              [Line 1]
          ],
        Subproof
          "( and ( not phi ) ( not psi ) )"
          [ ProofStep
              "( not ( or phi psi ) )"
              (MMLabel "thm.dem-2")
              [Line 3]
          ],
        ProofStep
          "( iff ( not ( or phi psi ) ) ( and ( not phi ) ( not psi )) )"
          (MMLabel "axm.iff-intr")
          [Range 1 2, Range 3 4]
      ]
  ]

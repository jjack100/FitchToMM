{-# LANGUAGE OverloadedStrings #-}

module FitchToMM.Axioms (axioms, preDeclaredVars, sortVars) where

import Data.List
import qualified Data.Map.Strict as M
import Data.Maybe
import qualified Data.Text as T
import FitchToMM.Fact
import FitchToMM.FitchProof (Condition (..))
import FitchToMM.Parser (Wff, primitives, unsafeParseFormula)
import FitchToMM.ProofWriter

axioms :: M.Map T.Text Fact
axioms =
  M.fromList
    [ -- Axioms of propositional logic
      ( "axm.and-intr",
        Fact
          (expr "( and phi psi )")
          [CtxHyp "...", WffHyp "phi", WffHyp "psi"]
          [ Condition Nothing (expr "phi"),
            Condition Nothing (expr "psi")
          ]
          []
      ),
      ( "axm.or-intr-1",
        Fact
          (expr "( or phi psi )")
          [CtxHyp "...", WffHyp "phi", WffHyp "psi"]
          [Condition Nothing (expr "phi")]
          []
      ),
      ( "axm.or-intr-2",
        Fact
          (expr "( or psi phi )")
          [CtxHyp "...", WffHyp "phi", WffHyp "psi"]
          [Condition Nothing (expr "phi")]
          []
      ),
      ( "axm.implies-intr",
        Fact
          (expr "( implies phi psi )")
          [CtxHyp "...", WffHyp "phi", WffHyp "psi"]
          [Condition (Just $ expr "phi") (expr "psi")]
          []
      ),
      ( "axm.iff-intr",
        Fact
          (expr "( iff phi psi )")
          [CtxHyp "...", WffHyp "phi", WffHyp "psi"]
          [ Condition (Just $ expr "phi") (expr "psi"),
            Condition (Just $ expr "psi") (expr "phi")
          ]
          []
      ),
      ( "axm.not-intr",
        Fact
          (expr "( not phi )")
          [CtxHyp "...", WffHyp "phi"]
          [Condition (Just $ expr "phi") (expr "false")]
          []
      ),
      ( "axm.true-intr",
        Fact
          (expr "true")
          [CtxHyp "..."]
          []
          []
      ),
      ( "axm.and-elim-1",
        Fact
          (expr "phi")
          [CtxHyp "...", WffHyp "phi", WffHyp "psi"]
          [Condition Nothing (expr "( and phi psi )")]
          []
      ),
      ( "axm.and-elim-2",
        Fact
          (expr "psi")
          [CtxHyp "...", WffHyp "phi", WffHyp "psi"]
          [Condition Nothing (expr "( and phi psi )")]
          []
      ),
      ( "axm.or-elim",
        Fact
          (expr "chi")
          [CtxHyp "...", WffHyp "phi", WffHyp "psi", WffHyp "chi"]
          [ Condition Nothing (expr "( or phi psi )"),
            Condition (Just $ expr "phi") (expr "chi"),
            Condition (Just $ expr "psi") (expr "chi")
          ]
          []
      ),
      ( "axm.implies-elim",
        Fact
          (expr "psi")
          [CtxHyp "...", WffHyp "phi", WffHyp "psi"]
          [ Condition Nothing (expr "( implies phi psi )"),
            Condition Nothing (expr "phi")
          ]
          []
      ),
      ( "axm.iff-elim-1",
        Fact
          (expr "psi")
          [CtxHyp "...", WffHyp "phi", WffHyp "psi"]
          [ Condition Nothing (expr "( iff phi psi )"),
            Condition Nothing (expr "phi")
          ]
          []
      ),
      ( "axm.iff-elim-2",
        Fact
          (expr "phi")
          [CtxHyp "...", WffHyp "phi", WffHyp "psi"]
          [ Condition Nothing (expr "( iff phi psi )"),
            Condition Nothing (expr "psi")
          ]
          []
      ),
      ( "axm.not-elim",
        Fact
          (expr "false")
          [CtxHyp "...", WffHyp "phi"]
          [ Condition Nothing (expr "phi"),
            Condition Nothing (expr "( not phi )")
          ]
          []
      ),
      ( "axm.false-elim",
        Fact
          (expr "phi")
          [CtxHyp "...", WffHyp "phi"]
          [Condition Nothing (expr "false")]
          []
      ),
      ( "axm.ip",
        Fact
          (expr "phi")
          [CtxHyp "...", WffHyp "phi"]
          [Condition (Just $ expr "( not phi )") (expr "false")]
          []
      ),
      -- Axioms of predicate logic
      ( "axm.forall-intr",
        Fact
          (expr "( forall x psi )")
          [CtxHyp "...", WffHyp "phi", WffHyp "psi", VarHyp "a", VarHyp "x"]
          [Condition Nothing (expr "phi")]
          [mkDVR (CtxHyp "...") (VarHyp "a")]
      ),
      ( "axm.exists-intr",
        Fact
          (expr "( exists x psi )")
          [CtxHyp "...", WffHyp "phi", WffHyp "psi", VarHyp "x", TrmHyp "trm_1"]
          [Condition Nothing (expr "phi")]
          []
      ),
      ( "axm.eq-intr",
        Fact
          (expr "( eq trm_1 trm_1 )")
          [CtxHyp "...", TrmHyp "trm_1"]
          []
          []
      ),
      ( "axm.forall-elim",
        Fact
          (expr "psi")
          [CtxHyp "...", WffHyp "phi", WffHyp "psi", VarHyp "x", TrmHyp "trm_1"]
          [Condition Nothing (expr "( forall x phi )")]
          []
      ),
      ( "axm.exists-elim",
        Fact
          (expr "chi")
          [CtxHyp "...", WffHyp "phi", WffHyp "psi", WffHyp "chi", VarHyp "a", VarHyp "x"]
          [ Condition Nothing (expr "( exists x phi )"),
            Condition (Just $ expr "psi") (expr "chi")
          ]
          [mkDVR (CtxHyp "...") (VarHyp "a"), mkDVR (WffHyp "phi") (VarHyp "a"), mkDVR (WffHyp "chi") (VarHyp "a")]
      ),
      ( "axm.eq-elim-1",
        Fact
          (expr "psi")
          [CtxHyp "...", WffHyp "phi", WffHyp "psi", WffHyp "chi", VarHyp "x", TrmHyp "trm_1", TrmHyp "trm_2"]
          [ Condition Nothing (expr "( eq trm_1 trm_2 )"),
            Condition Nothing (expr "phi")
          ]
          [mkDVR (CtxHyp "x") (VarHyp "trm_1"), mkDVR (CtxHyp "x") (VarHyp "trm_2")]
      ),
      ( "thm.eq-elim-2",
        Fact
          (expr "phi")
          [CtxHyp "...", WffHyp "phi", WffHyp "psi", WffHyp "chi", VarHyp "x", TrmHyp "trm_1", TrmHyp "trm_2"]
          [ Condition Nothing (expr "( eq trm_1 trm_2 )"),
            Condition Nothing (expr "psi")
          ]
          [mkDVR (CtxHyp "x") (VarHyp "trm_1"), mkDVR (CtxHyp "x") (VarHyp "trm_2")]
      )
    ]

expr :: T.Text -> Wff
expr = unsafeParseFormula $ primitives

preDeclaredVars :: [FHyp]
preDeclaredVars =
  [CtxHyp "..."]
    ++ map WffHyp ["phi", "psi", "chi", "phi_1", "psi_1", "chi_1", "phi_2", "psi_2", "chi_2"]
    ++ map (VarHyp . T.singleton) ['a' .. 'z']
    ++ map TrmHyp ["trm_1", "trm_2", "trm_3"]

sortVars :: [FHyp] -> [FHyp]
sortVars = sortOn $ \x -> (pos x, x)
  where
    pos x = fromMaybe end (elemIndex x preDeclaredVars)
    end = length preDeclaredVars
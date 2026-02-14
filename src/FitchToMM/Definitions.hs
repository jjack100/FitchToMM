{-# LANGUAGE OverloadedStrings #-}

module FitchToMM.Definitions
  ( Definition (..),
    Definiendum,
    Definiens,
    baseDefinitions,
  )
where

import qualified Data.Map.Strict as M
import qualified Data.Text as T
import FitchToMM.Parser
import FitchToMM.ProofWriter

data Definition = Definition Definiendum Definiens [FHyp] [DVR]

type Definiendum = Wff

type Definiens = Wff

baseDefinitions :: M.Map T.Text Definition
baseDefinitions =
  M.fromList
    [ ( "def.unique",
        Definition
          (expr "( unique x phi )")
          (expr "( exists x ( and phi ( forall y ( implies ( sub y x phi ) ( eq y x ) ) ) ) )")
          [WffHyp "phi", VarHyp "x", VarHyp "y"]
          [mkDVR (VarHyp "y") (WffHyp "phi")]
      )
    ]

expr :: T.Text -> Wff
expr = unsafeParseFormula $ primitives
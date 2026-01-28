module FitchToMM.Fact (Fact (..)) where

import FitchToMM.FitchProof
import FitchToMM.Parser
import FitchToMM.ProofWriter

data Fact = Fact Wff [FHyp] [Condition] [DVR]
  deriving (Show)
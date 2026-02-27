{-# LANGUAGE OverloadedStrings #-}

module FitchToMM.FitchProof where

import qualified Data.Text as T
import FitchToMM.Declarations (AllowedSubs, Condition (..))
import FitchToMM.Parser
import FitchToMM.ProofWriter 

data Citation = Line Int | Range Int Int
  deriving (Show)

data FitchStep
  = FitchStep Wff T.Text [Citation]
  | FitchSubproof Wff [FitchStep]
  deriving (Show)

data FitchProof = FitchProof T.Text AllowedSubs [Condition] [FitchStep]

data Justification
  = Reference T.Text
  | Premise Int
  | Assumption
  | Reiteration
  deriving (Show)

data FlatStep = FlatStep Context Wff Justification [Citation] [Int]
  deriving (Show)

flattenProof :: FitchProof -> [FlatStep]
flattenProof (FitchProof _ _ prems steps) = hyps ++ body
  where
    hyps = concat $ zipWith hypStep [0 ..] prems
    body = flattenSteps (RelContext []) [] (length prems) steps
    hypStep i (Condition Nothing hyp) =
      [FlatStep (RelContext []) hyp (Premise i) [] [i]]
    hypStep i (Condition (Just sup) hyp) =
      [ FlatStep (RelContext [sup]) sup Assumption [] [0, i],
        FlatStep (RelContext [sup]) hyp (Premise i) [] [1, i]
      ]

flattenSteps :: Context -> [Int] -> Int -> [FitchStep] -> [FlatStep]
flattenSteps context position start fitch =
  let f ctx pos i (FitchStep expr "reiteration" c) =
        [FlatStep ctx expr Reiteration (map toZeroBased c) (i : pos)]
      f ctx pos i (FitchStep expr r c) =
        [FlatStep ctx expr (Reference r) (map toZeroBased c) (i : pos)]
      f ctx pos i (FitchSubproof assump steps) =
        FlatStep (assume ctx assump) assump Assumption [] (0 : i : pos)
          : flattenSteps (assume ctx assump) (i : pos) 1 steps
   in concat $ zipWith (f context position) [start ..] fitch

toZeroBased :: Citation -> Citation
toZeroBased (Line i) = Line (i - 1)
toZeroBased (Range i j) = Range (i - 1) (j - 1)

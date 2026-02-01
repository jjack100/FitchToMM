{-# LANGUAGE OverloadedStrings #-}

module FitchToMM.Compressed
  ( PackedProof (..),
    PackedStep (..),
    packProof,
  )
where

import Data.List (mapAccumR)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.Text as T
--import qualified Data.Vector.Unboxed as V
import FitchToMM.Fact (Fact)
import FitchToMM.MMProof (MMProof (..))
import FitchToMM.ProofWriter

data PackedStep = PackedStep (Maybe Int) T.Text | Backreference Int | UnknownStep
  deriving (Show)

data PackedProof
  = PackedProof
  { packedLabel :: T.Text,
    packedFact :: Fact,
    packedFHyps :: [FHyp],
    packedDvrs :: [DVR],
    packedStack :: [PackedStep],
    packedMistakes :: [(Int, Mistake)]
  }
  deriving (Show)

data ProofTree = ProofTreeSubproof Label [ProofTree] | ProofTreeUnknown
  deriving (Eq, Ord)

packProof :: MMProof -> PackedProof
packProof (MMProof label fact fhyps dvrs stack mistakes) =
  PackedProof label fact fhyps dvrs packedSteps mistakes
  where
    packedSteps = packTree (`S.member` toPack) tree
    tree = parseRPN $ getSteps stack
    toPack = findPackable tree

packTree :: (ProofTree -> Bool) -> ProofTree -> [PackedStep]
packTree packable tree = reverse steps
  where
    packSubproof :: TagMap -> ProofTree -> (TagMap, [PackedStep])
    packSubproof prevMap subprf@(ProofTreeSubproof label substeps)
      | packable subprf = case lookupTag subprf tagMap of
          Just tag -> (tagMap, [Backreference tag])
          Nothing ->
            let (n, newMap) = insertLabel subprf tagMap
             in (newMap, PackedStep (Just n) label : concat newSteps)
      | otherwise = (tagMap, PackedStep Nothing label : concat newSteps)
      where
        (tagMap, newSteps) = mapAccumR packSubproof prevMap substeps
    packSubproof prevMap ProofTreeUnknown = (prevMap, [UnknownStep])
    (_, steps) = packSubproof emptyTagMap tree

-- Find subproofs that are candidates for packing
findPackable :: ProofTree -> S.Set ProofTree
findPackable = M.keysSet . M.filterWithKey packable . findSubproofs
  where
    packable tree count = complete tree && nontrivial tree && count > 1
    complete (ProofTreeUnknown) = False
    complete (ProofTreeSubproof _ subproof) = all complete subproof
    nontrivial (ProofTreeSubproof _ substeps) = not $ null substeps
    nontrivial ProofTreeUnknown = False

-- Find and count the occurrences of subproofs
findSubproofs :: ProofTree -> M.Map ProofTree Int
findSubproofs proof@(ProofTreeSubproof _ steps) =
  let subproofs = M.unionsWith (+) (findSubproofs <$> steps)
   in M.insertWith (+) proof 1 subproofs
findSubproofs _ = M.empty

-- Reconstruct the tree-structure of the proof from the RPN stack
parseRPN :: [Maybe RpnStep] -> ProofTree
parseRPN steps = case foldl' pushStep [] steps of
  -- Only one entry should be left on the stack if the proof was valid
  [tree] -> tree
  _ -> ProofTreeUnknown
  where
    pushStep :: [ProofTree] -> Maybe RpnStep -> [ProofTree]
    pushStep prev (Just (RpnStep arity label)) =
      let (consumed, rest) = splitAt arity prev
          subproof = ProofTreeSubproof label consumed
       in subproof : rest
    pushStep prev Nothing = ProofTreeUnknown : prev

{-
encodeInt :: Int -> T.Text
encodeInt n
  | n <= 0 = T.empty
  | otherwise = T.reverse $ T.pack encoding
  where
    (q, r) = quotRem (n - 1) 20
    encoding = digits20 V.! r : map ((digits5 V.!) . pred) (q `toBijectiveBase` 5)
    digits20 = V.fromListN 20 ['A' .. 'T']
    digits5 = V.fromListN 5 ['U' .. 'Y']

toBijectiveBase :: Int -> Int -> [Int]
toBijectiveBase 0 _ = []
toBijectiveBase n k =
  let q = (n - 1) `div` k
   in n - (q * k) : toBijectiveBase q k
-}

-- A map to keep track of which subproofs have been tagged for backreferencing
data TagMap = TagMap Int (M.Map ProofTree Int)

lookupTag :: ProofTree -> TagMap -> Maybe Int
lookupTag label (TagMap _ tagMap) = M.lookup label tagMap

emptyTagMap :: TagMap
emptyTagMap = TagMap 1 M.empty

insertLabel :: ProofTree -> TagMap -> (Int, TagMap)
insertLabel label (TagMap n tagMap) =
  (n, TagMap (n + 1) (M.insert label n tagMap))
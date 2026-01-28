{-# LANGUAGE OverloadedStrings #-}

module FitchToMM.Compressed where

import qualified Data.Text as T
import qualified Data.Vector.Unboxed as V

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
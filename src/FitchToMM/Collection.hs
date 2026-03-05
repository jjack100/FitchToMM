{-# LANGUAGE OverloadedStrings #-}

module FitchToMM.Collection (Collection (..), Item (..), fromList, findItem) where

import Data.Either (fromRight)
import Data.List (find, mapAccumL)
import qualified Data.Text as T
import FitchToMM.Declarations
import FitchToMM.FitchProof (EquivProof, FitchProof)
import FitchToMM.MMProof (MMProof (proofFact, proofLabel))
import FitchToMM.Parser (SymbolType)
import FitchToMM.ProofWriter (Label)

data Collection = Collection T.Text DeclMap [Item]

data Item
  = TheoremItem FitchProof MMProof
  | DefinitionItem Label AllowedSubs SymbolType T.Text Definition
  | EquivItem EquivProof MMProof

fromList :: T.Text -> DeclMap -> [DeclMap -> Either T.Text Item] -> Either T.Text Collection
fromList title prevMap getItems = do
  let (declMap, itemsE) = mapAccumL processItem prevMap getItems
  items <- sequence itemsE
  return $ Collection title declMap items

processItem :: DeclMap -> (DeclMap -> Either T.Text Item) -> (DeclMap, Either T.Text Item)
processItem prevMap getItem =
  let result = do
        item <- getItem prevMap
        newDecls <- insertItem prevMap item
        return (newDecls, item)
   in (fromRight prevMap $ fst <$> result, snd <$> result)

insertItem :: DeclMap -> Item -> Either T.Text DeclMap
insertItem prevMap (TheoremItem _ proof) =
  let decl = FactDeclaration $ proofFact proof
   in Right $ insertDecl prevMap (proofLabel proof) decl
insertItem prevMap (DefinitionItem label _ symbolTyp symbol def) =
  let withDecl = insertDecl prevMap label (DefDeclaration def)
      withSymb = insertSymbol withDecl symbol symbolTyp
   in Right withSymb
insertItem prevMap (EquivItem _ proof) = do
  let fact = proofFact proof
  eqvFact <-
    maybe
      (Left $ proofLabel proof <> " not in the form of an equivalence")
      Right
      (factAsEquiv fact)
  let decl = EquivDeclaration eqvFact
  return $ insertDecl prevMap (proofLabel proof) decl

findItem :: Collection -> Label -> Maybe Item
findItem (Collection _ _ items) label = find (\x -> itemLabel x == label) items

itemLabel :: Item -> Label
itemLabel (TheoremItem _ proof) = proofLabel proof
itemLabel (DefinitionItem label _ _ _ _) = label
itemLabel (EquivItem _ proof) = proofLabel proof
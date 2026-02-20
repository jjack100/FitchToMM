{-# LANGUAGE OverloadedStrings #-}

module FitchToMM.Collection (Collection (..), Item (..), fromList, fromListE, findItem) where

import Data.List (find, mapAccumL)
import qualified Data.Text as T
import Data.Void (absurd)
import FitchToMM.Declarations
import FitchToMM.FitchProof (FitchProof)
import FitchToMM.MMProof (MMProof (proofFact, proofLabel))
import FitchToMM.Parser (SymbolType)
import FitchToMM.ProofWriter (Label)
import GHC.Base (Void)

data Collection = Collection T.Text DeclMap [Item]

data Item
  = TheoremItem FitchProof MMProof
  | DefinitionItem Label AllowedSubs SymbolType T.Text Definition

fromList :: T.Text -> DeclMap -> [DeclMap -> Item] -> Collection
fromList title prevMap getItems =
  let itemsE :: [DeclMap -> Either Void Item]
      itemsE = map (Right .) getItems
      collectionE = fromListE title prevMap itemsE
   in either absurd id collectionE

fromListE :: T.Text -> DeclMap -> [DeclMap -> Either a Item] -> Either a Collection
fromListE title prevMap getItems = do
  let (declMap, itemsE) = mapAccumL processItem prevMap getItems
  items <- sequence itemsE
  return $ Collection title declMap items

processItem :: DeclMap -> (DeclMap -> Either a Item) -> (DeclMap, Either a Item)
processItem prevMap getItem =
  let itemE = getItem prevMap
      newDecls = case itemE of
        Left _ -> prevMap
        Right item -> insertItem prevMap item
   in (newDecls, itemE)

insertItem :: DeclMap -> Item -> DeclMap
insertItem prevMap (TheoremItem _ proof) =
  let decl = FactDeclaration $ proofFact proof
   in insertDecl prevMap (proofLabel proof) decl
insertItem prevMap (DefinitionItem label _ symbolTyp definedTerm def) =
  let withDecl = insertDecl prevMap label (DefDeclaration def)
      withSymb = insertSymbol withDecl definedTerm symbolTyp
   in withSymb

findItem :: Collection -> Label -> Maybe Item
findItem (Collection _ _ items) label = find (\x -> itemLabel x == label) items

itemLabel :: Item -> Label
itemLabel (TheoremItem _ proof) = proofLabel proof
itemLabel (DefinitionItem label _ _ _ _) = label
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module FitchToMM.Declarations
  ( DeclMap,
    Fact (..),
    Definition (..),
    Definiendum,
    Definiens,
    Declaration (..),
    Condition (..),
    AllowedSubs,
    findFact,
    insertDecl,
    findDefinition,
    toLanguage,
    mkDef,
    mkFact,
    inferDVRs,
    base,
    fromListM,
    emptyDeclMap,
    insertSymbol,
  )
where

import Control.Monad (foldM, guard)
import Data.Containers.ListUtils (nubOrd)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.Text as T
import FitchToMM.Matcher (varsInWff)
import FitchToMM.Parser
import FitchToMM.ProofWriter
import Text.Parsec (ParseError)

data DeclMap = DeclMap (M.Map Label Declaration) (M.Map T.Text SymbolType)

data Declaration
  = FactDeclaration Fact
  | DefDeclaration Definition

data Fact = Fact Wff [Condition] [FHyp] [DVR]
  deriving (Show)

-- A condition can optionally be making a supposition, i.e., an assumption to be
-- discharged in the application of the fact it is conditioning
data Condition = Condition (Maybe Wff) Wff
  deriving (Show)

type AllowedSubs = T.Text -> [T.Text]

data Definition = Definition Definiendum Definiens [FHyp] [DVR]

type Definiendum = Wff

type Definiens = Wff

type Sexpr = T.Text

findFact :: DeclMap -> Label -> Maybe Fact
findFact (DeclMap declMap _) label = case declMap M.!? label of
  (Just (FactDeclaration fact)) -> Just fact
  _ -> Nothing

findDefinition :: DeclMap -> Label -> Maybe Definition
findDefinition (DeclMap declMap _) label = case declMap M.!? label of
  (Just (DefDeclaration def)) -> Just def
  _ -> Nothing

toLanguage :: DeclMap -> Language
toLanguage (DeclMap _ symbolMap) = Language $ \symbol -> symbolMap M.!? symbol

fromList :: [(Label, Language -> Declaration)] -> DeclMap
fromList = foldl' append emptyDeclMap
  where
    append prev (label, toDecl) =
      let lang = toLanguage prev
       in insertDecl prev label (toDecl lang)

fromListM :: (Monad m) => [(Label, Language -> m Declaration)] -> m DeclMap
fromListM = foldM append emptyDeclMap
  where
    append prev (label, toDecl) = do
      decl <- toDecl $ toLanguage prev
      return $ insertDecl prev label decl

mkFact :: Sexpr -> [(Maybe Sexpr, Sexpr)] -> [FHyp] -> [DVR] -> Language -> Either ParseError Fact
mkFact claim conds fhyps dvrs lang = do
  let parse = parseFormula lang
  claimWff <- parse claim
  let parseCond (supp, cond) = do
        suppWff <- traverse parse supp
        condWff <- parse cond
        return $ Condition suppWff condWff
  parsedConds <- traverse parseCond conds
  return $ Fact claimWff parsedConds fhyps dvrs

mkDef :: Sexpr -> Sexpr -> AllowedSubs -> Language -> Either ParseError Definition
mkDef definiendum definiens allowedSubs lang = do
  let parse = parseFormula lang
  definiendumWff <- parse definiendum
  definiensWff <- parse definiens
  let fHyps = sortVars $ S.elems $ varsInWff definiendumWff <> varsInWff definiensWff
      dvrs = inferDVRs allowedSubs fHyps
  return $ Definition definiendumWff definiensWff fHyps dvrs

inferDVRs :: AllowedSubs -> [FHyp] -> [DVR]
inferDVRs allowed fhyps = nubOrd $ do
  -- Consider all possible pairings between two different variables
  var1 <- fhyps
  var2 <- fhyps
  guard $ var1 /= var2
  -- Only consider DVRs where at least one (the first) is a setvar
  let isSetvar (VarHyp _) = True
      isSetvar _ = False
  guard $ isSetvar var1
  -- Don't automatically include DVRs with the assumption context
  -- That is only necessary in special cases to express side-conditions
  let isCtx (CtxHyp _) = True
      isCtx _ = False
  guard $ not $ isCtx var2
  -- Don't include DVRs when the substitution is explicitly allowed
  guard $ not $ (fHypName var1) `elem` allowed (fHypName var2)
  return $ mkDVR var1 var2

insertDecl :: DeclMap -> Label -> Declaration -> DeclMap
insertDecl (DeclMap declMap lang) label decl = DeclMap (M.insert label decl declMap) lang

insertSymbol :: DeclMap -> T.Text -> SymbolType -> DeclMap
insertSymbol (DeclMap declMap lang) symbol symbolType = DeclMap declMap (M.insert symbol symbolType lang)

emptyDeclMap :: DeclMap
emptyDeclMap = DeclMap M.empty M.empty

base :: DeclMap
base =
  fromList
    [ -- Axioms of propositional logic
      ( "axm.and-intr",
        declareFact
          "( and phi psi )"
          [ (Nothing, "phi"),
            (Nothing, "psi")
          ]
          [CtxHyp "...", WffHyp "phi", WffHyp "psi"]
          []
      ),
      ( "axm.or-intr-1",
        declareFact
          "( or phi psi )"
          [(Nothing, "phi")]
          [CtxHyp "...", WffHyp "phi", WffHyp "psi"]
          []
      ),
      ( "axm.or-intr-2",
        declareFact
          "( or psi phi )"
          [(Nothing, "phi")]
          [CtxHyp "...", WffHyp "phi", WffHyp "psi"]
          []
      ),
      ( "axm.implies-intr",
        declareFact
          "( implies phi psi )"
          [(Just "phi", "psi")]
          [CtxHyp "...", WffHyp "phi", WffHyp "psi"]
          []
      ),
      ( "axm.iff-intr",
        declareFact
          "( iff phi psi )"
          [ (Just "phi", "psi"),
            (Just "psi", "phi")
          ]
          [CtxHyp "...", WffHyp "phi", WffHyp "psi"]
          []
      ),
      ( "axm.not-intr",
        declareFact
          "( not phi )"
          [(Just "phi", "false")]
          [CtxHyp "...", WffHyp "phi"]
          []
      ),
      ( "axm.true-intr",
        declareFact
          "true"
          []
          [CtxHyp "..."]
          []
      ),
      ( "axm.and-elim-1",
        declareFact
          "phi"
          [(Nothing, "( and phi psi )")]
          [CtxHyp "...", WffHyp "phi", WffHyp "psi"]
          []
      ),
      ( "axm.and-elim-2",
        declareFact
          "psi"
          [(Nothing, "( and phi psi )")]
          [CtxHyp "...", WffHyp "phi", WffHyp "psi"]
          []
      ),
      ( "axm.or-elim",
        declareFact
          "chi"
          [ (Nothing, "( or phi psi )"),
            (Just "phi", "chi"),
            (Just "psi", "chi")
          ]
          [CtxHyp "...", WffHyp "phi", WffHyp "psi", WffHyp "chi"]
          []
      ),
      ( "axm.implies-elim",
        declareFact
          "psi"
          [ (Nothing, "( implies phi psi )"),
            (Nothing, "phi")
          ]
          [CtxHyp "...", WffHyp "phi", WffHyp "psi"]
          []
      ),
      ( "axm.iff-elim-1",
        declareFact
          "psi"
          [ (Nothing, "( iff phi psi )"),
            (Nothing, "phi")
          ]
          [CtxHyp "...", WffHyp "phi", WffHyp "psi"]
          []
      ),
      ( "axm.iff-elim-2",
        declareFact
          "phi"
          [ (Nothing, "( iff phi psi )"),
            (Nothing, "psi")
          ]
          [CtxHyp "...", WffHyp "phi", WffHyp "psi"]
          []
      ),
      ( "axm.not-elim",
        declareFact
          "false"
          [ (Nothing, "phi"),
            (Nothing, "( not phi )")
          ]
          [CtxHyp "...", WffHyp "phi"]
          []
      ),
      ( "axm.false-elim",
        declareFact
          "phi"
          [(Nothing, "false")]
          [CtxHyp "...", WffHyp "phi"]
          []
      ),
      ( "axm.ip",
        declareFact
          "phi"
          [(Just "( not phi )", "false")]
          [CtxHyp "...", WffHyp "phi"]
          []
      ),
      -- Axioms of predicate logic
      ( "axm.forall-intr",
        declareFact
          "( forall x psi )"
          [(Nothing, "phi")]
          [CtxHyp "...", WffHyp "phi", WffHyp "psi", VarHyp "a", VarHyp "x"]
          [mkDVR (CtxHyp "...") (VarHyp "a")]
      ),
      ( "axm.exists-intr",
        declareFact
          "( exists x psi )"
          [(Nothing, "phi")]
          [CtxHyp "...", WffHyp "phi", WffHyp "psi", VarHyp "x", TrmHyp "trm_1"]
          []
      ),
      ( "axm.eq-intr",
        declareFact
          "( eq trm_1 trm_1 )"
          []
          [CtxHyp "...", TrmHyp "trm_1"]
          []
      ),
      ( "axm.forall-elim",
        declareFact
          "psi"
          [(Nothing, "( forall x phi )")]
          [CtxHyp "...", WffHyp "phi", WffHyp "psi", VarHyp "x", TrmHyp "trm_1"]
          []
      ),
      ( "axm.exists-elim",
        declareFact
          "chi"
          [ (Nothing, "( exists x phi )"),
            (Just "psi", "chi")
          ]
          [CtxHyp "...", WffHyp "phi", WffHyp "psi", WffHyp "chi", VarHyp "a", VarHyp "x"]
          [mkDVR (CtxHyp "...") (VarHyp "a"), mkDVR (WffHyp "phi") (VarHyp "a"), mkDVR (WffHyp "chi") (VarHyp "a")]
      ),
      ( "axm.eq-elim-1",
        declareFact
          "psi"
          [ (Nothing, "( eq trm_1 trm_2 )"),
            (Nothing, "phi")
          ]
          [CtxHyp "...", WffHyp "phi", WffHyp "psi", WffHyp "chi", VarHyp "x", TrmHyp "trm_1", TrmHyp "trm_2"]
          [mkDVR (VarHyp "x") (TrmHyp "trm_1"), mkDVR (VarHyp "x") (TrmHyp "trm_2")]
      ),
      ( "thm.eq-elim-2",
        declareFact
          "phi"
          [ (Nothing, "( eq trm_1 trm_2 )"),
            (Nothing, "psi")
          ]
          [CtxHyp "...", WffHyp "phi", WffHyp "psi", WffHyp "chi", VarHyp "x", TrmHyp "trm_1", TrmHyp "trm_2"]
          [mkDVR (VarHyp "x") (TrmHyp "trm_1"), mkDVR (VarHyp "x") (TrmHyp "trm_2")]
      ),
      -- Definition of uniqueness quantification
      ( "def.unique",
        declareDef
          "( unique x phi )"
          "( exists x ( and phi ( forall y ( implies ( sub y x phi ) ( eq y x ) ) ) ) )"
          (\case "phi" -> ["x"]; _ -> [])
      )
    ]
  where
    declareFact claim conds fhyps dvrs =
      FactDeclaration
        . (either (error . show) id)
        . mkFact claim conds fhyps dvrs

    declareDef definiendum definiens allowedSubs =
      DefDeclaration
        . (either (error . show) id)
        . mkDef definiendum definiens allowedSubs
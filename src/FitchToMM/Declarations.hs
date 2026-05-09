{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : FitchToMM.Declarations
-- Description : Declaration map
--
-- This module manages the collection of declarations (facts, definitions, equivalences).
-- The idea is that a declaration provides the information needed for an item to be referenced
-- by another.
module FitchToMM.Declarations
  ( DeclMap,
    Fact (..),
    Definition (..),
    Definiendum,
    Definiens,
    Declaration (..),
    Condition (..),
    EquivFact (..),
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
    findEquiv,
    factAsEquiv,
  )
where

import Control.Monad (foldM, guard)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.Text as T
import FitchToMM.Parser
import FitchToMM.ProofWriter
import Text.Parsec (ParseError)
import FitchToMM.Context
import FitchToMM.Variable

-- | A declaration map consists of a map of Metamath labels to declarations
-- such as facts and definitions, as well as a map from defined symbols to their
-- respective grammatical types.
data DeclMap = DeclMap (M.Map Label Declaration) (M.Map T.Text SymbolType)

-- | A declaration for an item (fact, definition, or equivalence).
data Declaration
  = -- | A fact: a statement with its requirements for application
    FactDeclaration Fact
  | -- | A definition: a biconditional between definiendum and definiens
    DefDeclaration Definition
  | -- | An equivalence: a proven biconditional between two formulas
    EquivDeclaration EquivFact

-- | A logical fact with its statement and conditions.
data Fact = Fact Context Wff [Condition] [FHyp] [DVR]
  deriving (Show)

-- | A condition (essential hypothesis) in a rule application.
--
-- A condition can optionally be making a supposition, i.e., an assumption to be
-- discharged in the application of the fact it is conditioning.
data Condition = Condition (Maybe Wff) Wff
  deriving (Show)

-- | A definition of a new logical construct.
data Definition = Definition Definiendum Definiens [FHyp] [DVR]

-- | A fact stating a logical equivalence between two WFFs.
--
-- This is distinguished from regular facts, because it indicates the
-- special case where the substitutability of equivalents can be used as a rule
-- (that is, subexpressions can be replaced with equivalent ones)
data EquivFact = EquivFact Wff Wff [FHyp] [DVR]
  deriving (Show)

-- | The definiendum - the WFF containing the symbol being defined.
type Definiendum = Wff

-- | The definiens - the WFF defining the symbol, to be equated to the definiendum.
type Definiens = Wff

-- | An S-expression string representation of a formula.
type Sexpr = T.Text

-- | Find a fact by its label.
--
-- Returns @Just fact@ if the label names a fact declaration,
-- or @Nothing@ if the label is unrecognized or names a definition/equivalence.
findFact :: DeclMap -> Label -> Maybe Fact
findFact (DeclMap declMap _) label = case declMap M.!? label of
  (Just (FactDeclaration fact)) -> Just fact
  _ -> Nothing

-- | Find a definition by its label.
--
-- Returns @Just def@ if the label names a definition declaration,
-- or @Nothing@ if unrecognized or names a fact/equivalence.
findDefinition :: DeclMap -> Label -> Maybe Definition
findDefinition (DeclMap declMap _) label = case declMap M.!? label of
  (Just (DefDeclaration def)) -> Just def
  _ -> Nothing

-- | Find an equivalence by its label.
--
-- Returns @Just eqv@ if the label names an equivalence declaration,
-- or @Nothing@ if unrecognized or names a fact/definition.
findEquiv :: DeclMap -> Label -> Maybe EquivFact
findEquiv (DeclMap declMap _) label = case declMap M.!? label of
  (Just (EquivDeclaration def)) -> Just def
  _ -> Nothing

-- | Extract the language signature from the declaration map.
--
-- Returns a 'Language' mapping symbols to their types (predicates,
-- functions, constants) as declared in the map.
toLanguage :: DeclMap -> Language
toLanguage (DeclMap _ symbolMap) = Language $ \symbol -> symbolMap M.!? symbol

-- | Convert a fact to an equivalence, if the fact has biconditional form.
--
-- Succeeds only if:
--
-- - The fact has no conditions (i.e., represents a tautology)
-- - The conclusion is a biconditional (@iff@) statement
--
-- Returns @Just eqv@ with the two sides of the biconditional as an equivalence,
-- or @Nothing@ if the fact doesn't match this form.
factAsEquiv :: Fact -> Maybe EquivFact
factAsEquiv (Fact _ claim conds fHyps dvrs) = do
  guard $ null conds
  (lhs, rhs) <- case claim of
    WffBinOp OpIff x y -> Just (x, y)
    _ -> Nothing
  return $ EquivFact lhs rhs fHyps dvrs

-- Build a declaration map from a list of label-declaration pairs.
-- Each declaration is processed sequentially, allowing later declarations
-- to reference the language built by earlier ones.
fromList :: [(Label, Language -> Declaration)] -> DeclMap
fromList = foldl' append emptyDeclMap
  where
    append prev (label, toDecl) =
      let lang = toLanguage prev
       in insertDecl prev label (toDecl lang)

-- | Monadic version of declaration map building.
-- Each declaration is processed sequentially, allowing later declarations
-- to reference the language built by earlier ones.
fromListM :: (Monad m) => [(Label, Language -> m Declaration)] -> m DeclMap
fromListM = foldM append emptyDeclMap
  where
    append prev (label, toDecl) = do
      decl <- toDecl $ toLanguage prev
      return $ insertDecl prev label decl

-- | Create a fact from S-expression strings and metadata.
--
-- Parses S-expression formulas into abstract syntax trees, constructing
-- a 'Fact' with the given conditions, floating hypotheses, and restrictions.
--
-- Returns @Left parseError@ if any formula fails to parse,
-- @Right fact@ if all formulas parse successfully.
mkFact :: Sexpr -> [(Maybe Sexpr, Sexpr)] -> [FHyp] -> [DVR] -> Language -> Either ParseError Fact
mkFact claim conds fHyps dvrs lang = do
  let parse = parseFormula lang
  claimWff <- parse claim
  let parseCond (supp, cond) = do
        suppWff <- traverse parse supp
        condWff <- parse cond
        return $ Condition suppWff condWff
  parsedConds <- traverse parseCond conds
  return $ Fact (RelContext []) claimWff parsedConds fHyps dvrs

-- | Create a definition from S-expression strings.
--
-- Returns @Left parseError@ if parsing fails,
-- @Right def@ if successful.
mkDef :: Sexpr -> Sexpr -> AllowedSubs -> Language -> Either ParseError Definition
mkDef definiendum definiens allowedSubs lang = do
  let parse = parseFormula lang
  definiendumWff <- parse definiendum
  definiensWff <- parse definiens
  let fHyps = sortVars $ S.elems $ varsInWff definiendumWff <> varsInWff definiensWff
      dvrs = inferDVRs allowedSubs definiendumWff <> inferDVRs allowedSubs definiensWff
  return $ Definition definiendumWff definiensWff fHyps dvrs

-- | Insert a declaration into the map.
insertDecl :: DeclMap -> Label -> Declaration -> DeclMap
insertDecl (DeclMap declMap lang) label decl = DeclMap (M.insert label decl declMap) lang

-- | Insert a symbol type into the language signature.
-- Registers a symbol (predicate, function, or constant) with its type information.
insertSymbol :: DeclMap -> T.Text -> SymbolType -> DeclMap
insertSymbol (DeclMap declMap lang) symbol symbolType = DeclMap declMap (M.insert symbol symbolType lang)

-- | An empty declaration map.
emptyDeclMap :: DeclMap
emptyDeclMap = DeclMap M.empty M.empty

-- The base set of logical axioms and definitions.
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
          [mkDVR (VarHyp "a") (VarHyp "x")]
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
          [mkDVR (VarHyp "a") (VarHyp "x")]
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
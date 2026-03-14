{-# LANGUAGE OverloadedStrings #-}

module FitchToMM.Pretty
  ( printProof,
    prettyProof,
    prettyWff,
    prettyTrm,
    prettyPacked,
    prettyNormal,
    prettyCompressed,
    prettyDVR,
    prettyDefinition,
  )
where

import Data.List ((\\))
import qualified Data.Set as S
import qualified Data.Text as T
import FitchToMM.Compressed
import FitchToMM.Context
import FitchToMM.Declarations (Condition (..), Definition (..))
import FitchToMM.MMProof
import FitchToMM.Parser
import FitchToMM.ProofWriter
import FitchToMM.SyntaxProver (constStep, funcStep, prdStep)
import FitchToMM.Variable
import Prettyprinter

printProof :: MMProof -> IO ()
printProof proof = print $ prettyNormal proof

prettyNormal :: MMProof -> Doc a
prettyNormal (MMProof name fact fHyps djVars rpnStack _) =
  let proof = fillSep $ map pretty $ listStack name rpnStack
   in prettyProof name fact fHyps djVars proof

prettyPacked :: PackedProof -> Doc a
prettyPacked (PackedProof name fact fHyps djVars rpnStack _) =
  prettyProof name fact fHyps djVars proof
  where
    proof = fillSep $ map prettyLabel $ rpnStack
    prettyLabel UnknownStep = "?"
    prettyLabel (Backreference n) = pretty n
    prettyLabel (PackedStep (Just n) stepLabel) =
      pretty n <> ":" <> pretty stepLabel
    prettyLabel (PackedStep Nothing stepLabel) = pretty stepLabel

prettyCompressed :: CompressedProof -> Doc a
prettyCompressed (CompressedProof name fact fHyps djVars labels rpnStack _) =
  let prettyStack = fillCat $ map pretty $ T.unpack rpnStack
      prettyLabels = lparen <+> fillSep (map pretty labels) <+> rparen
   in prettyProof name fact fHyps djVars (prettyLabels <+> prettyStack)

prettyDefinition :: Label -> SymbolType -> T.Text -> Definition -> Doc a
prettyDefinition label symbolType definedTerm definition =
  vsep [prettySyntax, prettyDef]
  where
    prettySyntax = vsep [cStmt, synStmt]
    prettyDef =
      frame $
        vsep $
          prettyVars label localVars
            ++ [sep $ map prettyCompoundDVR compounds | not $ null dvrs]
            ++ [defStmt]
    cStmt = "$c" <+> pretty definedTerm <+> "$."
    synStmt = case symbolType of
      SymPredicate _ ->
        let RpnStep _ synLabel = prdStep definedTerm
         in pretty synLabel <+> "$a prd" <+> pretty definedTerm <+> "$."
      SymFunction _ ->
        let RpnStep _ synLabel = funcStep label
         in pretty synLabel <+> "$a func" <+> pretty definedTerm <+> "$."
      SymConstant ->
        let RpnStep _ synLabel = constStep label
         in pretty synLabel <+> "$a trm" <+> pretty definedTerm <+> "$."
    defStmt =
      nest 2 $
        group $
          pretty label
            <+> "$a ;"
            <+> prettyWff definiendum
            <+> ":="
            <> line
            <> prettyWff definiens
            <+> "$."
    localVars = fHyps \\ preDeclaredVars
    compounds = compoundDVRs fHyps dvrs
    Definition definiendum definiens fHyps dvrs = definition

prettyProof :: Label -> Fact -> [FHyp] -> [DVR] -> Doc a -> Doc a
prettyProof name fact fHyps dvrs prettyStack =
  frame $
    vsep $
      prettyVars name localVars
        ++ [sep $ map prettyCompoundDVR compounds | not $ null dvrs]
        ++ zipWith (prettyEHyp ctx) (map pad eLabels) eHyps
        ++ [prettyPStmt ctx (pad name) claim prettyStack]
  where
    (Fact ctx claim eHyps _ _) = fact
    eLabels = map (number name) [1 .. length eHyps]
    labelLen = maximum $ map T.length (name : eLabels)
    pad = T.justifyLeft labelLen ' '
    localVars = fHyps \\ preDeclaredVars
    compounds = compoundDVRs fHyps dvrs

frame :: Doc a -> Doc a
frame doc = nest 2 (vsep ["${", doc]) <> line <> "$}"

number :: T.Text -> Int -> T.Text
number text n = text <> "." <> T.pack (show n)

prettyVars :: T.Text -> [FHyp] -> [Doc a]
prettyVars _ [] = []
prettyVars itemLabel vars =
  ("$v" <+> align (fillSep $ map (pretty . fHypName) vars) <+> "$.")
    : map (prettyFHyp (itemLabel <> ".")) vars

prettyFHyp :: T.Text -> FHyp -> Doc a
prettyFHyp prefix (WffHyp n) = pretty prefix <> "wff." <> pretty n <+> "$f wff" <+> pretty n <+> "$."
prettyFHyp prefix (VarHyp n) = pretty prefix <> "var." <> pretty n <+> "$f var" <+> pretty n <+> "$."
prettyFHyp prefix (TrmHyp n) = pretty prefix <> "trm." <> pretty n <+> "$f trm" <+> pretty n <+> "$."
prettyFHyp prefix (CtxHyp n) = pretty prefix <> "ctx." <> pretty n <+> "$f ctx" <+> pretty n <+> "$."

prettyDVR :: DVR -> Doc a
prettyDVR (DVR v1 v2) =
  "$d"
    <+> pretty (fHypName $ v1)
    <+> pretty (fHypName $ v2)
    <+> "$."

prettyCompoundDVR :: CompoundDVR -> Doc a
prettyCompoundDVR dvr = "$d" <+> fillSep names <+> "$."
  where
    names = map (pretty . fHypName) $ S.toList dvr

prettyPStmt :: Context -> T.Text -> Wff -> Doc a -> Doc a
prettyPStmt ctx label claim proof =
  pretty label
    <+> "$p ;"
    <+> prettyCtx ctx
    <> "|-"
    <+> prettyWff claim
    <+> "$="
    <+> nest 2 (line <> proof)
    <+> "$."

prettyEHyp :: Context -> T.Text -> Condition -> Doc a
prettyEHyp ctx label (Condition (Just sup) hyp) =
  pretty label
    <+> "$e ;"
    <+> prettyCtx ctx
    <> prettyWff sup
    <+> "|-"
    <+> prettyWff hyp
    <+> "$."
prettyEHyp ctx label (Condition Nothing hyp) =
  pretty label
    <+> "$e ;"
    <+> prettyCtx ctx
    <> "|-"
    <+> prettyWff hyp
    <+> "$."

prettyCtx :: Context -> Doc a
prettyCtx (RelContext []) = "..." <> space
prettyCtx (RelContext ctx) = "..." <+> sep (map prettyWff $ reverse ctx) <> space
prettyCtx (AbsContext []) = mempty
prettyCtx (AbsContext ctx) = sep (map prettyWff $ reverse ctx) <> space

prettyWff :: Wff -> Doc a
prettyWff (WffBinOp op lhs rhs) =
  prettySExpr [prettyOp op, prettyWff lhs, prettyWff rhs]
prettyWff (WffNot wff) = prettySExpr ["not", prettyWff wff]
prettyWff WffTrue = "true"
prettyWff WffFalse = "false"
prettyWff (WffQnt q var wff) =
  prettySExpr [prettyQnt q, pretty var, prettyWff wff]
prettyWff (WffAtom p args) = prettySExpr $ pretty p : map prettyTrm args
prettyWff (WffMetavar v) = pretty v
prettyWff (WffSub trm v wff) = prettySExpr ["sub", prettyTrm trm, pretty v, prettyWff wff]

prettyTrm :: Term -> Doc a
prettyTrm (TrmVar var) = pretty var
prettyTrm (TrmFunc f args) = prettySExpr $ pretty f : map prettyTrm args
prettyTrm (TrmConst c) = pretty c
prettyTrm (TrmMetavar m) = pretty m
prettyTrm (TrmSub t1 v t2) = prettySExpr ["sub", prettyTrm t1, pretty v, prettyTrm t2]

prettyOp :: BinOp -> Doc a
prettyOp OpAnd = "and"
prettyOp OpOr = "or"
prettyOp OpImplies = "implies"
prettyOp OpIff = "iff"

prettyQnt :: Quantifier -> Doc a
prettyQnt QntForall = "forall"
prettyQnt QntExists = "exists"
prettyQnt QntUnique = "unique"

prettySExpr :: [Doc a] -> Doc a
prettySExpr items = lparen <+> align (sep items) <+> rparen

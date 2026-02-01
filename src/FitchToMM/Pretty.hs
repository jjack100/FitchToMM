{-# LANGUAGE OverloadedStrings #-}

module FitchToMM.Pretty
  ( printProof,
    prettyProof,
    prettyWff,
    prettyTrm,
    prettyPacked,
    prettyNormal,
  )
where

import Data.List ((\\))
import qualified Data.Text as T
import FitchToMM.Axioms
import FitchToMM.Compressed (PackedProof (PackedProof), PackedStep (Backreference, PackedStep, UnknownStep))
import FitchToMM.FitchProof
import FitchToMM.MMProof
import FitchToMM.Parser
import FitchToMM.ProofWriter
import Prettyprinter

printProof :: MMProof -> IO ()
printProof proof = print $ prettyNormal proof

prettyNormal :: MMProof -> Doc a
prettyNormal (MMProof name fact fHyps djVars rpnStack _) =
  let proof = fillSep $ map pretty $ listStack rpnStack
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

prettyProof :: Label -> Fact -> [FHyp] -> [DVR] -> Doc a -> Doc a
prettyProof name fact fHyps djVars prettyStack =
  frame $
    vsep $
      prettyVars localVars
        ++ [sep $ map prettyDVR djVars | not $ null djVars]
        ++ zipWith prettyEHyp (map pad eLabels) eHyps
        ++ [prettyPStmt (pad name) claim prettyStack]
  where
    (Fact claim _ eHyps _) = fact
    eLabels = map (number name) [1 .. length eHyps]
    labelLen = maximum $ map T.length (name : eLabels)
    pad = T.justifyLeft labelLen ' '
    localVars = fHyps \\ preDeclaredVars
    frame doc = nest 2 (vsep ["${", doc]) <> line <> "$}"

number :: T.Text -> Int -> T.Text
number text n = text <> "." <> T.pack (show n)

prettyVars :: [FHyp] -> [Doc a]
prettyVars [] = []
prettyVars vars =
  ("$v" <+> align (fillSep $ map (pretty . fHypName) vars) <+> "$.")
    : map prettyFHyp vars

prettyFHyp :: FHyp -> Doc a
prettyFHyp (WffHyp n) = "wff." <> pretty n <+> "$f wff" <+> pretty n <+> "$."
prettyFHyp (VarHyp n) = "var." <> pretty n <+> "$f var" <+> pretty n <+> "$."
prettyFHyp (TrmHyp n) = "trm." <> pretty n <+> "$f trm" <+> pretty n <+> "$."
prettyFHyp (CtxHyp n) = "ctx." <> pretty n <+> "$f ctx" <+> pretty n <+> "$."

prettyDVR :: DVR -> Doc a
prettyDVR (DVR var1 var2) =
  "$d"
    <+> pretty (fHypName var1)
    <+> pretty (fHypName var2)
    <+> "$."

prettyPStmt :: T.Text -> Wff -> Doc a -> Doc a
prettyPStmt label claim proof =
  pretty label
    <+> "$p ; ... |-"
    <+> prettyWff claim
    <+> "$="
    <+> nest 2 (line <> proof)
    <+> "$."

prettyEHyp :: T.Text -> Condition -> Doc a
prettyEHyp label (Condition (Just sup) hyp) =
  pretty label
    <+> "$e ; ..."
    <+> prettyWff sup
    <+> "|-"
    <+> prettyWff hyp
    <+> "$."
prettyEHyp label (Condition Nothing hyp) =
  pretty label
    <+> "$e ; ... |-"
    <+> prettyWff hyp
    <+> "$."

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

prettyTrm :: Term -> Doc a
prettyTrm (TrmVar var) = pretty var
prettyTrm (TrmFunc f args) = prettySExpr $ pretty f : map prettyTrm args
prettyTrm (TrmConst c) = pretty c
prettyTrm (TrmMetavar m) = pretty m

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

{-# LANGUAGE OverloadedStrings #-}

module Display
  ( prettyFlat,
    prettyFitch,
    withColor,
    withBold,
    withItalics,
  )
where

import Control.Exception
import Data.List
import qualified Data.Text as T
import FitchToMM.FitchProof
import FitchToMM.Parser
import FitchToMM.Pretty
import GHC.IO.Handle
import Prettyprinter
import Prettyprinter.Render.Text
import System.Console.ANSI
import Text.Regex.TDFA

-- Display a flattened proof in sequent-style
prettyFlat :: Bool -> T.Text -> AllowedSubs -> [FlatStep] -> T.Text
prettyFlat asSExpr name allowedSubs steps =
  name
    <> ":\n\n"
    <> ( T.intercalate "\n" $
           zipWith4
             (\num ctx wff just -> num <> " " <> ctx <> " ⊢ " <> wff <> " " <> just)
             (padR nums)
             (padR ctxs)
             (padL wffs)
             justs
       )
  where
    -- Print line numbers
    nums = map T.show [1 .. length steps]
    -- Print context
    printCtx ctx = T.intercalate ", " $ "Γ" : map render (reverse ctx)
    ctxs = map (\(FlatStep ctx _ _ _ _) -> printCtx ctx) steps
    -- Print the expression
    wffs = map (\(FlatStep _ wff _ _ _) -> render wff) steps
    -- Print the justification for the step
    justs = map (\(FlatStep _ _ just cites _) -> printJust just <> " " <> printCites cites) steps
    printJust (Reference ref) = ref
    printJust (Premise n) = "Premise #" <> T.show (n + 1)
    printJust Assumption = "Assumption"
    printJust Reiteration = "Reiteration"
    -- Print the citations
    printCites = T.intercalate ", " . map printCite
    printCite (Line n) = T.show (n + 1)
    printCite (Range from to) = T.show (from + 1) <> "–" <> T.show (to + 1)
    render = if asSExpr then wffToText else prettierWff allowedSubs

-- Draw proof in Fitch-style using box-drawing characters
prettyFitch :: Bool -> FitchProof -> T.Text
prettyFitch asSExpr (FitchProof name allowedSubs prems steps) =
  name
    <> ":\n\n"
    <> ( T.intercalate "\n" $
           zipWith3
             (\num expr just -> num <> " " <> expr <> "  " <> just)
             (padR nums)
             (padL exprs)
             justs
       )
  where
    (hasLineNum, exprs, justs) =
      unzip3 $
        if null prems
          then printedSteps
          else printedPrems ++ premDivider ++ printedSteps
    -- Print the premises
    prettyPrem :: Int -> Condition -> [(Bool, T.Text, T.Text)]
    prettyPrem num (Condition Nothing prem) =
      let premTxt = render prem
       in [(True, "│ " <> premTxt, "Premise #" <> T.show num)]
    prettyPrem num (Condition (Just sup) prem) =
      let premTxt = render prem
          supTxt = render sup
       in [ (True, "│ │ " <> supTxt, "Assumption"),
            (False, "│ ├─" <> premTxt, ""),
            (True, "│ │ " <> premTxt, "Premise #" <> T.show num),
            (False, "│", "")
          ]
    printedPrems = concat $ zipWith prettyPrem [1 ..] prems
    premMaxLen = maximum $ map (\(_, expr, _) -> T.length expr) printedPrems
    premDivider = [(False, "╞" <> T.replicate premMaxLen "═", "")]
    -- Print the body of the proof
    prettyStep :: Int -> FitchStep -> [(Bool, T.Text, T.Text)]
    prettyStep indnt (FitchStep wff rule cites) =
      let bars = T.replicate indnt "│ "
       in [ (True, bars <> render wff, rule <> " " <> printCites cites)
          ]
    prettyStep indnt (FitchSubproof assump substeps) =
      let bars = T.replicate indnt "│ "
          expr = render assump
          assumpLines =
            [ (True, bars <> "│ " <> expr, "Assumption"),
              (False, bars <> "├─" <> T.replicate (T.length expr) "─", "")
            ]
       in assumpLines ++ concatMap (prettyStep (indnt + 1)) substeps ++ [(False, bars, "")]
    printedSteps = concatMap (prettyStep 1) steps
    -- Print line numbers
    nums =
      let step :: Int -> Bool -> (Int, T.Text)
          step n True = (n + 1, T.show n)
          step n False = (n, "")
       in snd $ mapAccumL step 1 hasLineNum
    -- Print the citations (unlike FlatProof, these already use 1-based indexing)
    printCites = T.intercalate ", " . map printCite
    printCite (Line n) = T.show n
    printCite (Range from to) = T.show from <> "–" <> T.show to
    render = if asSExpr then wffToText else prettierWff allowedSubs

padL :: [T.Text] -> [T.Text]
padL txts = map (T.justifyLeft (maximum $ map T.length txts) ' ') txts

padR :: [T.Text] -> [T.Text]
padR txts = map (T.justifyRight (maximum $ map T.length txts) ' ') txts

prettierWff :: AllowedSubs -> Wff -> T.Text
prettierWff a (WffBinOp OpAnd lhs rhs) =
  "(" <> prettierWff a lhs <> " ∧ " <> prettierWff a rhs <> ")"
prettierWff a (WffBinOp OpOr lhs rhs) =
  "(" <> prettierWff a lhs <> " ∨ " <> prettierWff a rhs <> ")"
prettierWff a (WffBinOp OpImplies lhs rhs) =
  "(" <> prettierWff a lhs <> " → " <> prettierWff a rhs <> ")"
prettierWff a (WffBinOp OpIff lhs rhs) =
  "(" <> prettierWff a lhs <> " ↔ " <> prettierWff a rhs <> ")"
prettierWff a (WffNot rhs) = "¬" <> prettierWff a rhs
prettierWff _ (WffTrue) = "⊤"
prettierWff _ (WffFalse) = "⊥"
prettierWff a (WffQnt QntForall var wff) =
  "∀" <> var <> prettierWff a wff
prettierWff a (WffQnt QntExists var wff) =
  "∃" <> var <> prettierWff a wff
prettierWff a (WffQnt QntUnique var wff) =
  "∃!" <> var <> prettierWff a wff
prettierWff a (WffSub trm var wff) =
  let wffTxt = case wff of
        -- Add parens around prefix operators to prevent possible ambiguity
        (WffNot _) -> "(" <> prettierWff a wff <> ")"
        (WffQnt _ _ _) -> "(" <> prettierWff a wff <> ")"
        _ -> prettierWff a wff
   in wffTxt <> "[" <> prettierTerm a trm <> "/" <> var <> "]"
prettierWff a (WffAtom "eq" [lhs, rhs]) =
  (prettierTerm a lhs) <> " = " <> (prettierTerm a rhs)
prettierWff a (WffAtom label args) =
  label <> "(" <> T.intercalate ", " (map (prettierTerm a) args) <> ")"
prettierWff a (WffMetavar label) = prettierVar a label

prettierTerm :: AllowedSubs -> Term -> T.Text
prettierTerm a (TrmVar label) = prettierVar a label
prettierTerm a (TrmMetavar label) = prettierVar a label
prettierTerm _ (TrmConst label) = label
prettierTerm a (TrmFunc label args) =
  label <> "(" <> T.intercalate ", " (map (prettierTerm a) args) <> ")"

prettierVar :: AllowedSubs -> T.Text -> T.Text
prettierVar a var = case groups of
  [letter, _, subscript] ->
    toLetter letter <> T.map toSubscript subscript <> freeVars
  _ -> var
  where
    pat = "^(phi|psi|chi|trm|[a-z])(_([0-9]+))?$" :: T.Text
    res = (var =~ pat) :: (T.Text, T.Text, T.Text, [T.Text])
    (_, _, _, groups) = res
    freeVars =
      if null $ a var
        then ""
        else "(" <> T.intercalate "," (a var) <> ")"
    toLetter "phi" = "φ"
    toLetter "psi" = "ψ"
    toLetter "chi" = "χ"
    toLetter "trm" = "τ"
    toLetter other = other
    toSubscript '0' = '₀'
    toSubscript '1' = '₁'
    toSubscript '2' = '₂'
    toSubscript '3' = '₃'
    toSubscript '4' = '₄'
    toSubscript '5' = '₅'
    toSubscript '6' = '₆'
    toSubscript '7' = '₇'
    toSubscript '8' = '₈'
    toSubscript '9' = '₉'
    toSubscript other = other

wffToText :: Wff -> T.Text
wffToText = renderStrict . layoutPretty (LayoutOptions Unbounded) . prettyWff

-- ANSI escape sequence helpers

withColor :: Handle -> ColorIntensity -> Color -> IO a -> IO a
withColor h intensity color ioAction = do
  useANSI <- hSupportsANSI h
  let set = hSetSGR h [SetColor Foreground intensity color]
      reset = hSetSGR h [SetDefaultColor Foreground]
  if useANSI then set >> ioAction `finally` reset else ioAction

withBold :: Handle -> IO a -> IO a
withBold h ioAction = do
  useANSI <- hSupportsANSI h
  let set = hSetSGR h [SetConsoleIntensity BoldIntensity]
      reset = hSetSGR h [SetConsoleIntensity NormalIntensity]
  if useANSI then set >> ioAction `finally` reset else ioAction

withItalics :: Handle -> IO a -> IO a
withItalics h ioAction = do
  useANSI <- hSupportsANSI h
  let set = hSetSGR h [SetItalicized True]
      reset = hSetSGR h [SetItalicized False]
  if useANSI then set >> ioAction `finally` reset else ioAction
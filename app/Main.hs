{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module Main (main) where

import Cli (Commands (..), DisplayStyle (..), ProofFormat (..), execCli)
import Control.Monad (foldM)
import Data.Aeson (eitherDecode)
import qualified Data.ByteString.Lazy as BL
import Data.Foldable (traverse_)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Display
import FitchToMM.Collection (Collection (..), Item (..), findItem)
import FitchToMM.Compressed (compressProof, packProof)
import FitchToMM.Declarations
import FitchToMM.FitchProof (EquivProof (EquivProof), FitchProof (FitchProof), flattenEquivProof, flattenProof)
import FitchToMM.MMProof
import FitchToMM.Parser (SymbolType)
import FitchToMM.Pretty
import FitchToMM.ProofWriter
import qualified FitchToMM.Serialize as S
import Paths_fitch_to_mm
import Prettyprinter
import Prettyprinter.Render.Text
import System.Console.ANSI
import System.Exit (exitFailure)
import System.IO (stderr, stdout)

newtype Database = Database T.Text

main :: IO ()
main = do
  cmd <- execCli
  let inputFile = cmdInputFile cmd
  content <- BL.readFile inputFile
  collection <- either (errorOut . T.pack) pure $ eitherDecode content
  parsedCollection <- either errorOut pure $ S.parseCollection base collection
  case cmd of
    (GenOptions _ outputFile format) ->
      genDatabase
        parsedCollection
        format
        outputFile
    (ShowOptions _ label dispStyle asSExpr) ->
      displayItem asSExpr dispStyle parsedCollection label

genDatabase :: Collection -> ProofFormat -> FilePath -> IO ()
genDatabase (Collection title _ items) format outputFile = do
  let heading = "\n\n" <> (makeHeading title)
  folPath <- getDataFileName "fol.mm"
  folMM <- TIO.readFile folPath
  let baseContent = Database (folMM <> heading)
  Database result <- foldM (appendItem format) baseContent items
  TIO.writeFile outputFile (result <> "\n")

  withColor stdout Vivid Green $ do
    TIO.putStr $ "Success! File generated at: "
    withBold stdout $ putStrLn outputFile

appendItem :: ProofFormat -> Database -> Item -> IO Database
appendItem format db (TheoremItem _ proof) = appendTheorem format db proof
appendItem _ db (DefinitionItem label _ symbolType definedTerm def) =
  appendDefinition db label symbolType definedTerm def
appendItem format db (EquivItem _ proof) = appendTheorem format db proof

appendTheorem :: ProofFormat -> Database -> MMProof -> IO Database
appendTheorem format (Database content) proof = do
  let options = defaultLayoutOptions
      proofDoc = case format of
        Normal -> prettyNormal proof
        Packed -> prettyPacked $ packProof $ proof
        Compressed -> prettyCompressed $ compressProof $ packProof proof
      proofText = renderStrict $ layoutSmart options proofDoc
  printMistakes (proofLabel proof) (proofMistakes proof)
  return $ Database $ content <> "\n\n" <> proofText

appendDefinition :: Database -> Label -> SymbolType -> T.Text -> Definition -> IO Database
appendDefinition (Database content) label symbolType definedTerm definition = do
  let options = defaultLayoutOptions
      defDoc = prettyDefinition label symbolType definedTerm definition
      defText = renderStrict $ layoutSmart options defDoc
  return $ Database $ content <> "\n\n" <> defText

printMistakes :: T.Text -> [(Int, Mistake)] -> IO ()
printMistakes _ [] = pure ()
printMistakes thm mistakes = withColor stderr Dull Yellow $ do
  -- Print warning message
  withBold stderr $ TIO.hPutStr stderr $ "Warning: "
  TIO.hPutStr stderr $ "Mistakes were found in "
  withItalics stderr $ TIO.hPutStr stderr thm
  TIO.hPutStrLn stderr $ ". The generated proof may be incomplete."
  -- List mistakes
  traverse_ (uncurry printMistake) mistakes
  hSetSGR stderr [Reset]
  where
    printMistake :: Int -> Mistake -> IO ()
    printMistake i mistake =
      TIO.hPutStrLn stderr $ "\tStep " <> (T.show (i + 1)) <> ": " <> (describe mistake)
    describe :: Mistake -> T.Text
    describe BadAssumption = "Malformed assumption"
    describe BadCiteCount = "Cites the wrong number of lines"
    describe CitesDischarged = "Cites a line that depends on a discharged assumption"
    describe CitesLater = "Cites a line that comes afterwards"
    describe CitesNonexistent = "Cites a line that does not exist"
    describe CitesSelf = "Cites itself"
    describe EmptyList = "Predicate or function has 0 arguments"
    describe Inapplicable = "Referenced justification is not applicable"
    describe LeftUndischarged = "Proof ends with 1 or more undischarged assumptions"
    describe NotASubproof = "Cites a range of lines that is not a subproof"
    describe UnrecognizedFact = "References an unrecognized fact"

makeHeading :: T.Text -> T.Text
makeHeading text =
  "$(\n"
    <> T.replicate 80 "#"
    <> "\n"
    <> text
    <> "\n"
    <> T.replicate 80 "#"
    <> "\n"
    <> "$)"

displayItem :: Bool -> DisplayStyle -> Collection -> Label -> IO ()
displayItem asSExpr dispStyle collection label = do
  item <- try (findItem collection label) ("Item not found: " <> label)
  case item of
    (TheoremItem fitchProof _) -> displayTheorem asSExpr dispStyle fitchProof
    (DefinitionItem name allowedSubs _ _ def) -> displayDefinition asSExpr name allowedSubs def
    (EquivItem eqvProof _) -> displayEquiv asSExpr dispStyle eqvProof

displayTheorem :: Bool -> DisplayStyle -> FitchProof -> IO ()
displayTheorem asSExpr dispStyle theorem = do
  let FitchProof label allowed _ _ = theorem
  TIO.putStrLn $ case dispStyle of
    Fitch -> prettyFitch asSExpr theorem
    Sequent -> prettyFlat asSExpr label allowed (flattenProof theorem)

displayDefinition :: Bool -> Label -> AllowedSubs -> Definition -> IO ()
displayDefinition asSExpr label allowedSubs def = do
  TIO.putStrLn $ prettyDef asSExpr label allowedSubs def

displayEquiv :: Bool -> DisplayStyle -> EquivProof -> IO ()
displayEquiv asSExpr dispStyle theorem = do
  let EquivProof label allowed steps = theorem
  TIO.putStrLn $ case dispStyle of
    Fitch -> prettyFitch asSExpr (FitchProof label allowed [] steps)
    Sequent -> prettyFlat asSExpr label allowed (flattenEquivProof theorem)

try :: Maybe a -> T.Text -> IO a
try result msg = maybe (errorOut msg) pure result

errorOut :: T.Text -> IO a
errorOut msg = withColor stderr Vivid Red $ do
  withBold stderr $ TIO.hPutStr stderr "Error: "
  TIO.hPutStrLn stderr msg
  exitFailure

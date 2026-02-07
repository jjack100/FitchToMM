{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (foldM, when)
import Data.Aeson (FromJSON, eitherDecode)
import qualified Data.ByteString.Lazy as BL
import Data.Foldable (find, traverse_)
import qualified Data.Map.Strict as M
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Display
import FitchToMM.Compressed (compressProof, packProof)
import FitchToMM.FitchProof (FitchProof (FitchProof), flattenProof)
import FitchToMM.MMProof
import FitchToMM.Parser (Language, primitives)
import FitchToMM.Pretty
import FitchToMM.ProofWriter
import FitchToMM.Schema (parseTheorem)
import qualified FitchToMM.Schema as Schema
import GHC.Generics (Generic)
import Options.Applicative
import Paths_fitch_to_mm
import Prettyprinter
import Prettyprinter.Render.Text
import System.Console.ANSI
import System.Exit (exitFailure)
import System.IO (stderr, stdout)

data Collection = Collection [Schema.Theorem]
  deriving (Generic)

instance FromJSON Collection

data Database = Database T.Text (M.Map T.Text Fact) Language

data ProofFormat = Normal | Packed | Compressed

data DisplayStyle = Fitch | Sequent

data Options
  = OutputOptions FilePath ProofFormat
  | DisplayOptions T.Text DisplayStyle Bool

data Args = Args Options FilePath

outputOptionsParser :: Parser Options
outputOptionsParser =
  parserOptionGroup "Output Mode Options" $
    OutputOptions
      <$> strOption
        ( long "output"
            <> short 'o'
            <> value "out.mm"
            <> showDefault
            <> metavar "OUTPUT_FILE"
            <> help "File the generated Metamath will be written to"
        )
      <*> formatParser

formatParser :: Parser ProofFormat
formatParser =
  flag Compressed Normal (long "normal" <> short 'n' <> hidden <> help "Output normal (uncompressed) format")
    <|> flag Compressed Packed (long "packed" <> short 'p' <> hidden <> help "Output packed format")
    <|> flag Compressed Compressed (long "compressed" <> short 'c' <> hidden <> help "Output compressed format (default)")

displayOptionsParser :: Parser Options
displayOptionsParser =
  parserOptionGroup "Display Mode Options" $
    DisplayOptions
      <$> strOption
        ( long "display"
            <> short 'd'
            <> metavar "PROOF_NAME"
            <> help "Display a specific proof instead of generating Metamath"
        )
      <*> styleParser
      <*> switch (long "sexpr" <> help "Display formulae as raw S-Expressions (as they appear in the Metamath database)")

styleParser :: Parser DisplayStyle
styleParser =
  flag Fitch Fitch (long "fitch" <> short 'f' <> hidden <> help "Show displayed proof in Fitch-style (default)")
    <|> flag Fitch Sequent (long "sequent" <> short 's' <> hidden <> help "Show displayed proof in sequent style")

argsParser :: Parser Args
argsParser =
  Args
    <$> (outputOptionsParser <|> displayOptionsParser)
    <*> strArgument (metavar "INPUT_FILE")

main :: IO ()
main = do
  Args options inputFile <-
    execParser $ info (argsParser <**> helper) briefDesc
  content <- BL.readFile inputFile
  collection <- either (errorOut . T.pack) pure $ eitherDecode content
  case options of
    (OutputOptions outputFile format) ->
      generateDatabase
        (T.pack inputFile)
        collection
        format
        outputFile
    (DisplayOptions thmName dispStyle asSExpr) ->
      displayTheorem asSExpr thmName collection dispStyle

generateDatabase :: T.Text -> Collection -> ProofFormat -> FilePath -> IO ()
generateDatabase name (Collection theorems) format outputFile = do
  let heading = "\n\n" <> (makeHeading name)
  folPath <- getDataFileName "fol.mm"
  folMM <- TIO.readFile folPath
  let base = Database (folMM <> heading) M.empty primitives
  Database result _ _ <- foldM (appendTheorem format) base theorems
  TIO.writeFile outputFile (result <> "\n")

  withColor stdout Vivid Green $ do
    TIO.putStr $ "Success! File generated at: "
    withBold stdout $ putStrLn outputFile

displayTheorem :: Bool -> T.Text -> Collection -> DisplayStyle -> IO ()
displayTheorem asSExpr thmName (Collection theorems) dispStyle = do
  theorem <-
    try
      (find (\thm -> Schema.getName thm == thmName) theorems)
      ("Theorem not found: " <> thmName)
  fitchProof <- either errorOut pure $ parseTheorem primitives theorem
  let (FitchProof _ allowedSubs _ _) = fitchProof
  TIO.putStrLn $ case dispStyle of
    Fitch -> prettyFitch asSExpr fitchProof
    Sequent -> prettyFlat asSExpr thmName allowedSubs (flattenProof fitchProof)

appendTheorem :: ProofFormat -> Database -> Schema.Theorem -> IO Database
appendTheorem format (Database metamath facts lang) thm = do
  fitchProof@(FitchProof name _ _ _) <- either errorOut pure $ parseTheorem lang thm
  mmProof <-
    try
      (fromFitchProof ((M.!?) facts) fitchProof)
      ("Empty theorem: " <> name)
  let mmLabel = proofLabel mmProof
  when (M.member mmLabel facts) (errorOut $ "Duplicate label encountered: " <> mmLabel)
  (printMistakes name) (proofMistakes mmProof)
  let options = defaultLayoutOptions
  let proofDoc = case format of
        Normal -> prettyNormal mmProof
        Packed -> prettyPacked $ packProof $ mmProof
        Compressed -> prettyCompressed $ compressProof $ packProof mmProof
  let proofText = renderStrict $ layoutSmart options proofDoc
  let newDB = metamath <> "\n\n" <> proofText
  let newFacts = M.insert mmLabel (proofFact mmProof) facts
  return $ Database newDB newFacts lang

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
    <> T.replicate 80 "-"
    <> "\n"
    <> text
    <> "\n"
    <> T.replicate 80 "-"
    <> "\n"
    <> "$)"

try :: Maybe a -> T.Text -> IO a
try result msg = maybe (errorOut msg) pure result

errorOut :: T.Text -> IO a
errorOut msg = withColor stderr Vivid Red $ do
  withBold stderr $ TIO.hPutStr stderr "Error: "
  TIO.hPutStrLn stderr msg
  exitFailure

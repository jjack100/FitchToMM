{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (foldM, when)
import Data.Aeson (FromJSON)
import Data.Aeson.Decoding
import qualified Data.ByteString.Lazy as BL
import Data.Char
import Data.Foldable
import qualified Data.Map.Strict as M
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import FitchToMM.Compressed (packProof)
import FitchToMM.FitchProof (FitchProof (FitchProof))
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
import System.IO

data Collection = Collection [Schema.Theorem]
  deriving (Generic)

instance FromJSON Collection

data Database = Database T.Text (M.Map T.Text Fact) Language

data ProofFormat = Normal | Packed
  deriving (Show, Read, Eq)

data Options = Options
  { optFormat :: ProofFormat,
    optOutputFile :: FilePath,
    optInputFile :: FilePath
  }
  deriving (Show)

parseFormat :: String -> Either String ProofFormat
parseFormat s = case map toLower s of
  "normal" -> Right Normal
  "packed" -> Right Packed
  _ -> Left $ "Invalid format: " ++ s ++ ". Must be Normal or Packed"

optionsParser :: Parser Options
optionsParser =
  Options
    <$> option
      (eitherReader parseFormat)
      ( long "format"
          <> short 'f'
          <> value Normal
          <> showDefault
          <> metavar "FORMAT"
          <> help "Output format: Normal or Packed"
      )
    <*> strOption
      ( long "output"
          <> short 'o'
          <> value "out.mm"
          <> showDefault
          <> metavar "OUTPUT_FILE"
          <> help "File the generated Metamath will be written to"
      )
    <*> strArgument (metavar "INPUT_FILE")

main :: IO ()
main = do
  Options format outputFile inputFile <-
    execParser $ info (optionsParser <**> helper) fullDesc
  content <- BL.readFile inputFile
  folPath <- getDataFileName "fol.mm"
  folMM <- TIO.readFile folPath
  Collection theorems <- either fail pure $ eitherDecode content
  let heading = "\n\n" <> (makeHeading $ T.pack inputFile)
  let base = Database (folMM <> heading) M.empty primitives
  Database result _ _ <- foldM (appendTheorem format) base theorems
  TIO.writeFile outputFile (result <> "\n")

  setSGR [SetColor Foreground Vivid Green]
  putStr $ "Success! File generated at: "
  setSGR [SetConsoleIntensity BoldIntensity]
  putStr $ outputFile
  setSGR [Reset]

appendTheorem :: ProofFormat -> Database -> Schema.Theorem -> IO Database
appendTheorem format (Database metamath facts lang) thm = do
  fitchProof@(FitchProof name _ _ _) <- either (fail . T.unpack) pure $ parseTheorem lang thm
  mmProof <-
    maybe
      (fail $ "Empty theorem: " <> T.unpack name)
      pure
      (fromFitchProof ((M.!?) facts) fitchProof)
  let mmLabel = proofLabel mmProof
  when (M.member mmLabel facts) (fail $ "Duplicate label encountered: " <> T.unpack mmLabel)
  (printMistakes name) (proofMistakes mmProof)
  let options = defaultLayoutOptions
  let proofDoc = case format of
        Normal -> prettyNormal mmProof
        Packed -> prettyPacked $ packProof $ mmProof
  let proofText = renderStrict $ layoutSmart options proofDoc
  let newDB = metamath <> "\n\n" <> proofText
  let newFacts = M.insert mmLabel (proofFact mmProof) facts
  return $ Database newDB newFacts lang

printMistakes :: T.Text -> [(Int, Mistake)] -> IO ()
printMistakes _ [] = pure ()
printMistakes thm mistakes = do
  hSetSGR stderr [SetColor Foreground Dull Yellow]
  TIO.hPutStr stderr $ "Warning: Mistakes were found in "
  hSetSGR stderr [SetItalicized True]
  TIO.hPutStr stderr thm
  hSetSGR stderr [SetItalicized False]
  TIO.hPutStrLn stderr $ ". The generated proof may be incomplete."
  traverse_ (uncurry printMistake) mistakes
  TIO.hPutStr stderr "\n"
  hSetSGR stderr [Reset]
  where
    printMistake :: Int -> Mistake -> IO ()
    printMistake i mistake =
      TIO.hPutStrLn stderr $
        "\tStep " <> (T.show (i + 1)) <> ": " <> (describe mistake)
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
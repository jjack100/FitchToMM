{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad (foldM, when)
import Data.Aeson (FromJSON)
import Data.Aeson.Decoding
import qualified Data.ByteString.Lazy as BL
import Data.Foldable
import qualified Data.Map.Strict as M
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import FitchToMM.FitchProof (FitchProof (FitchProof))
import FitchToMM.MMProof
import FitchToMM.Parser (Language, primitives)
import FitchToMM.Pretty (prettyProof)
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

data Options = Options
  { inputFile :: FilePath,
    outputFile :: FilePath
  }
  deriving (Show)

optionsParser :: Parser Options
optionsParser =
  Options
    <$> strArgument (metavar "FILE")
    <*> strOption
      ( long "output"
          <> short 'o'
          <> value "out.mm"
          <> metavar "FILENAME"
          <> help "File the generated Metamath will be written to"
      )

main :: IO ()
main = do
  opts <- execParser $ info optionsParser fullDesc
  content <- BL.readFile (inputFile opts)
  folPath <- getDataFileName "fol.mm"
  folMM <- TIO.readFile folPath
  Collection theorems <- either fail pure $ eitherDecode content
  let heading = "\n\n" <> (makeHeading $ T.pack $ inputFile opts)
  let base = Database (folMM <> heading) M.empty primitives
  Database result _ _ <- foldM appendTheorem base theorems
  TIO.writeFile (outputFile opts) (result <> "\n")

  setSGR [SetColor Foreground Vivid Green]
  putStr $ "Success! File generated at: "
  setSGR [SetConsoleIntensity BoldIntensity]
  putStr $ outputFile opts
  setSGR [Reset]

appendTheorem :: Database -> Schema.Theorem -> IO Database
appendTheorem (Database metamath facts lang) thm = do
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
  let proofText = renderStrict $ layoutSmart options (prettyProof mmProof)
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
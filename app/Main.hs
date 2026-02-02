{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Exception (finally)
import Control.Monad (foldM, when)
import Data.Aeson (FromJSON, eitherDecode)
import qualified Data.ByteString.Lazy as BL
import Data.Char
import Data.Foldable (find, traverse_)
import qualified Data.Map.Strict as M
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
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
import System.IO (Handle, stderr, stdout)

data Collection = Collection [Schema.Theorem]
  deriving (Generic)

instance FromJSON Collection

data Database = Database T.Text (M.Map T.Text Fact) Language

data ProofFormat = Normal | Packed | Compressed
  deriving (Show, Read, Eq)

data Options = Options
  { optOutputFile :: FilePath,
    optFormat :: ProofFormat,
    optDisplay :: Maybe T.Text
  }
  deriving (Show)

data Input = Input Options FilePath
  deriving (Show)

parseFormat :: String -> Either String ProofFormat
parseFormat s = case map toLower s of
  "normal" -> Right Normal
  "packed" -> Right Packed
  "compressed" -> Right Compressed
  _ -> Left $ "Invalid format: " ++ s ++ ". Must be Normal, Packed or Compressed"

inputParser :: Parser Input
inputParser =
  Input
    <$> (optionsParser)
    <*> strArgument (metavar "INPUT_FILE")

optionsParser :: Parser Options
optionsParser =
  Options
    <$> strOption
      ( long "output"
          <> short 'o'
          <> value "out.mm"
          <> showDefault
          <> metavar "OUTPUT_FILE"
          <> help "File the generated Metamath will be written to"
      )
    <*> option
      (eitherReader parseFormat)
      ( long "format"
          <> short 'f'
          <> value Compressed
          <> showDefault
          <> metavar "FORMAT"
          <> help "Output format: Normal, Packed, or Compressed"
      )
    <*> optional
      ( T.pack
          <$> strOption
            ( long "display"
                <> short 'd'
                <> metavar "THEOREM_NAME"
                <> help "Display a specific theorem instead of generating Metamath"
            )
      )

main :: IO ()
main = do
  Input options inputFile <-
    execParser $ info (inputParser <**> helper) briefDesc
  content <- BL.readFile inputFile
  collection <- either (errorOut . T.pack) pure $ eitherDecode content
  case optDisplay options of
    Nothing ->
      generateDatabase
        (T.pack inputFile)
        collection
        (optFormat options)
        (optOutputFile options)
    Just thmName -> displayTheorem thmName collection

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

displayTheorem :: T.Text -> Collection -> IO ()
displayTheorem thmName (Collection theorems) = do
  theorem <-
    try
      (find (\thm -> Schema.getName thm == thmName) theorems)
      ("Theorem not found: " <> thmName)
  fitchProof <- either errorOut pure $ parseTheorem primitives theorem
  TIO.putStrLn $ prettyFlat $ flattenProof fitchProof

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
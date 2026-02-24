{-# LANGUAGE OverloadedStrings #-}

module Cli
  ( Commands (..),
    ProofFormat (..),
    DisplayStyle (..),
    execCli,
  )
where

import qualified Data.Text as T
import Options.Applicative

data ProofFormat = Normal | Packed | Compressed

data DisplayStyle = Fitch | Sequent

data Commands
  = GenOptions
      { cmdInputFile :: FilePath,
        cmdOutputFile :: FilePath,
        cmdFormat :: ProofFormat
      }
  | ShowOptions
      { cmdInputFile :: FilePath,
        cmdItemLabel :: T.Text,
        cmdStyle :: DisplayStyle,
        cmdSExpr :: Bool
      }

execCli :: IO Commands
execCli = execParser $ info (commandParser <**> helper) briefDesc

commandParser :: Parser Commands
commandParser =
  subparser
    ( command
        "gen"
        ( info
            (genParser <**> helper)
            (progDesc "Generate a Metamath file from JSON input")
        )
        <> command
          "show"
          ( info
              (showParser <**> helper)
              (progDesc "Display a specific theorem")
          )
    )

genParser :: Parser Commands
genParser =
  GenOptions
    <$> strArgument (metavar "INPUT_FILE")
    <*> strOption
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
  flag Compressed Normal (long "normal" <> short 'n' <> help "Output normal (uncompressed) format")
    <|> flag Compressed Packed (long "packed" <> short 'p' <> help "Output packed format")
    <|> flag Compressed Compressed (long "compressed" <> short 'c' <> help "Output compressed format (default)")

showParser :: Parser Commands
showParser =
  ShowOptions
    <$> strArgument (metavar "INPUT_FILE")
    <*> strOption
      ( long "label"
          <> short 'l'
          <> metavar "ITEM_LABEL"
          <> help "Label of the item to display"
      )
    <*> styleParser
    <*> switch (long "sexpr" <> help "Display formulae as raw S-Expressions (as they appear in the Metamath database)")

styleParser :: Parser DisplayStyle
styleParser =
  flag Fitch Fitch (long "fitch" <> short 'f' <> help "Show proof in Fitch-style (default)")
    <|> flag Fitch Sequent (long "sequent" <> short 's' <> help "Show proof in sequent style")
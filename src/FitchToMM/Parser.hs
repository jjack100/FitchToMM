{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module FitchToMM.Parser
  ( Language (..),
    Wff (..),
    BinOp (..),
    Quantifier (..),
    Term (..),
    Arity,
    SymbolType (..),
    parseFormula,
    unsafeParseFormula,
    union,
  )
where

import qualified Control.Applicative as A
import Control.Monad
import Data.Char
import qualified Data.Text as T
import Text.Parsec
import Text.Parsec.Text

type Arity = Int

data SymbolType = SymPredicate Arity | SymFunction Arity | SymConstant

newtype Language = Language (T.Text -> Maybe SymbolType)

data Wff
  = WffBinOp BinOp Wff Wff
  | WffNot Wff
  | WffTrue
  | WffFalse
  | WffQnt Quantifier T.Text Wff
  | WffAtom T.Text [Term]
  | WffMetavar T.Text
  | WffSub Term T.Text Wff
  deriving (Show, Eq, Ord)

data BinOp = OpAnd | OpOr | OpImplies | OpIff
  deriving (Show, Eq, Ord)

data Quantifier = QntForall | QntExists | QntUnique
  deriving (Show, Eq, Ord)

data Term
  = TrmFunc T.Text [Term]
  | TrmVar T.Text
  | TrmConst T.Text
  | TrmMetavar T.Text
  | TrmSub Term T.Text Term
  deriving (Show, Eq, Ord)

parseFormula :: Language -> T.Text -> Either ParseError Wff
parseFormula l = parse (parseWff l <* eof) ""

unsafeParseFormula :: Language -> T.Text -> Wff
unsafeParseFormula l form = case parseFormula l form of
  (Left err) -> error (show err)
  (Right wff) -> wff

primitives :: Language
primitives = Language $ \case
  "eq" -> Just $ SymPredicate 2
  "in" -> Just $ SymPredicate 2
  _ -> Nothing

union :: Language -> Language -> Language
union (Language sig1) (Language sig2) =
  let signature symbol = sig1 symbol A.<|> sig2 symbol
   in Language signature

parseWff :: Language -> Parser Wff
parseWff lang = strip $ do
  let l = union primitives lang
  WffTrue <$ word "true"
    <|> WffFalse <$ word "false"
    <|> try parseMetavariable
    <|> try (parseBinaryOp l)
    <|> try (parseUnaryOp l)
    <|> try (parseQuantifier l)
    <|> try (parseSubWff l)
    <|> parsePredicate l

parseBinaryOp :: Language -> Parser Wff
parseBinaryOp l = parens $ do
  op <-
    OpAnd <$ word "and"
      <|> OpOr <$ word "or"
      <|> OpImplies <$ word "implies"
      <|> OpIff <$ word "iff"
  lhs <- parseWff l
  rhs <- parseWff l
  return $ WffBinOp op lhs rhs

parseUnaryOp :: Language -> Parser Wff
parseUnaryOp l = parens $ WffNot <$> (word "not" >> parseWff l)

parseQuantifier :: Language -> Parser Wff
parseQuantifier l = parens $ do
  qnt <-
    QntForall <$ word "forall"
      <|> QntExists <$ word "exists"
      <|> QntUnique <$ word "unique"
  spaces
  TrmVar var <- parseVariable
  expr <- parseWff l
  return $ WffQnt qnt var expr

parsePredicate :: Language -> Parser Wff
parsePredicate lang = parens $ do
  name <- T.pack <$> many1 asciiLetter
  arity <- tryMaybe (findPred lang name) ("Unknown predicate: " <> name)
  args <- count arity (parseTerm lang)
  return $ WffAtom name args

parseMetavariable :: Parser Wff
parseMetavariable = do
  var <- word "phi" <|> word "psi" <|> word "chi"
  subscript <- option "" parseSubscript
  return $ WffMetavar $ var <> subscript

parseSubWff :: Language -> Parser Wff
parseSubWff l = parens $ do
  _ <- word "sub"
  trm <- parseTerm l
  TrmVar var <- parseVariable
  wff <- parseWff l
  return $ WffSub trm var wff

parseTerm :: Language -> Parser Term
parseTerm l = strip $ do
  try parseTermMetavar
    <|> try (parseFunction l)
    <|> try parseVariable
    <|> try (parseConstant l)
    <|> parseSubTrm l

parseTermMetavar :: Parser Term
parseTermMetavar = do
  var <- word "trm"
  subscript <- option "" parseSubscript
  return $ TrmMetavar $ var <> subscript

parseFunction :: Language -> Parser Term
parseFunction lang = parens $ do
  name <- T.pack <$> many1 asciiLetter
  arity <- tryMaybe (findFunc lang name) ("Unknown function: " <> name)
  args <- count arity (parseTerm lang)
  return $ TrmFunc name args

parseVariable :: Parser Term
parseVariable = do
  varLetter <- satisfy isAsciiLower
  subscript <- option "" parseSubscript
  endWord
  return $ TrmVar $ T.cons varLetter subscript

parseConstant :: Language -> Parser Term
parseConstant lang = do
  name <- T.pack <$> many1 asciiLetter
  guard $ existsConst lang name
  return $ TrmConst name

parseSubTrm :: Language -> Parser Term
parseSubTrm l = parens $ do
  _ <- word "sub"
  trm1 <- parseTerm l
  TrmVar var <- parseVariable
  trm2 <- parseTerm l
  return $ TrmSub trm1 var trm2

parseSubscript :: Parser T.Text
parseSubscript = do
  underscore <- char '_'
  number <- many1 digit
  return $ T.pack $ underscore : number

word :: String -> Parser T.Text
word str = T.pack <$> string' str <* endWord

endWord :: Parser ()
endWord = notFollowedBy alphaNum

asciiLetter :: Parser Char
asciiLetter = satisfy $ \c -> isAscii c && isLetter c

parens :: Parser a -> Parser a
parens = between (char '(') (char ')') . strip

strip :: Parser a -> Parser a
strip = between spaces spaces

tryMaybe :: Maybe a -> T.Text -> Parser a
tryMaybe val msg = maybe (fail $ T.unpack msg) pure val

findPred :: Language -> T.Text -> Maybe Arity
findPred (Language signature) name
  | Just (SymPredicate arity) <- signature name = Just arity
  | otherwise = Nothing

findFunc :: Language -> T.Text -> Maybe Arity
findFunc (Language signature) name
  | Just (SymFunction arity) <- signature name = Just arity
  | otherwise = Nothing

existsConst :: Language -> T.Text -> Bool
existsConst (Language signature) name
  | Just SymConstant <- signature name = True
  | otherwise = False
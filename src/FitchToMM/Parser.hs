{-# LANGUAGE OverloadedStrings #-}

module FitchToMM.Parser
  ( Language (..),
    Wff (..),
    BinOp (..),
    Quantifier (..),
    Term (..),
    parseFormula,
    unsafeParseFormula,
    primitives,
  )
where

import Control.Monad
import Data.Char
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.Text as T
import Text.Parsec
import Text.Parsec.Text

data Language = Language PredicateNames FunctionNames ConstantNames

type PredicateNames = M.Map T.Text Int

type FunctionNames = M.Map T.Text Int

type ConstantNames = S.Set T.Text

instance Semigroup Language where
  (Language p1 f1 c1) <> (Language p2 f2 c2) =
    Language
      (p1 <> p2)
      (f1 <> f2)
      (c1 <> c2)

instance Monoid Language where
  mempty = Language M.empty M.empty S.empty

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

data Quantifier = QntForall | QntExists | QntUnique | QntFor
  deriving (Show, Eq, Ord)

data Term
  = TrmFunc T.Text [Term]
  | TrmVar T.Text
  | TrmConst T.Text
  | TrmMetavar T.Text
  deriving (Show, Eq, Ord)

parseFormula :: Language -> T.Text -> Either ParseError Wff
parseFormula l = parse (parseWff l <* eof) ""

unsafeParseFormula :: Language -> T.Text -> Wff
unsafeParseFormula l form = case parseFormula l form of
  (Left err) -> error (show err)
  (Right wff) -> wff

primitives :: Language
primitives =
  Language
    (M.fromList [("eq", 2), ("in", 2)])
    M.empty
    S.empty

parseWff :: Language -> Parser Wff
parseWff l = strip $ do
  WffTrue <$ word "true"
    <|> WffFalse <$ word "false"
    <|> try parseMetavariable
    <|> try (parseBinaryOp l)
    <|> try (parseUnaryOp l)
    <|> try (parseQuantifier l)
    <|> try (parseSub l)
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
parsePredicate l@(Language predicates _ _) = parens $ do
  name <- T.pack <$> many1 asciiLetter
  guard $ name `M.member` predicates
  arity <- tryMaybe (predicates M.!? name) ("Unknown predicate: " <> name)
  args <- count arity (parseTerm l)
  return $ WffAtom name args

parseMetavariable :: Parser Wff
parseMetavariable = do
  var <- word "phi" <|> word "psi" <|> word "chi"
  subscript <- option "" parseSubscript
  return $ WffMetavar $ var <> subscript

parseSub :: Language -> Parser Wff
parseSub l = parens $ do
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
    <|> parseConstant l

parseTermMetavar :: Parser Term
parseTermMetavar = do
  var <- word "trm"
  subscript <- option "" parseSubscript
  return $ TrmMetavar $ var <> subscript

parseFunction :: Language -> Parser Term
parseFunction l@(Language _ functions _) = parens $ do
  name <- T.pack <$> many1 asciiLetter
  guard $ name `M.member` functions
  arity <- tryMaybe (functions M.!? name) ("Unknown function: " <> name)
  args <- count arity (parseTerm l)
  return $ TrmFunc name args

parseVariable :: Parser Term
parseVariable = do
  varLetter <- satisfy isAsciiLower
  subscript <- option "" parseSubscript
  endWord
  return $ TrmVar $ T.cons varLetter subscript

parseConstant :: Language -> Parser Term
parseConstant (Language _ _ constants) = do
  name <- T.pack <$> many1 asciiLetter
  guard $ name `S.member` constants
  return $ TrmConst name

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
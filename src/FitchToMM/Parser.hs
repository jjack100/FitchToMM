{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : FitchToMM.Parser
-- Description : Parser for first-order logic formulas 
--
-- This module provides a parser for well-formed formulas (WFFs) in first-order logic.
-- It supports binary operators (@and@, @or@, @implies@, @iff@), unary negation,
-- quantifiers (@forall@, @exists@, @unique@), predicates, functions, constants,
-- and formula/term substitutions.
--
-- The parser is parameterized by a 'Language' that specifies the signature
-- (predicates, functions, constants) available for parsing. Multiple languages
-- can be combined using 'union'.
--
-- == Examples
--
-- Parse a simple formula with built-in predicates:
--
-- > let lang = Language $ \case "pred" -> Just (SymPredicate 1); _ -> Nothing
-- > parseFormula lang "(pred x)"
--
-- Parse a quantified formula:
--
-- > parseFormula lang "(forall x (pred x))"
--
-- == Syntax
--
-- Formulas use S-expression syntax:
--
-- - Atoms: @(predicate <term1> <term2> ...)@
-- - Binary ops: @(and <wff1> <wff2>)@, @(or ...)@, @(implies ...)@, @(iff ...)@
-- - Negation: @(not <wff>)@
-- - Quantifiers: @(forall <var> <wff>)@, @(exists <var> <wff>)@, @(unique var wff)@
-- - Substitution: @(sub <term> <var> <wff>)@
-- - Metavariables ranging over WFFs: @phi@, @psi@, @chi@ (optionally suffixed with @_n@ to indicate a subscript, where @n@ is a number)
-- - Terms can be variables @x@, constants @c@, functions @(f x y)@, or term metavariables @trm_1@
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

-- | The arity of a function or predicate, i.e., the number of arguments it takes.
type Arity = Int

-- | Describes the type and arity of a symbol in a language signature.
data SymbolType
  = -- | A predicate with the given arity
    SymPredicate Arity
  | -- | A function with the given arity
    SymFunction Arity
  | -- | A constant (arity 0)
    SymConstant
  deriving (Show, Eq)

-- | A language signature that maps symbol names to their types.
--
-- This determines which predicates, functions, and constants are available
-- for parsing. Custom languages can be created with a function that returns
-- @Just@ the symbol type for known symbols and @Nothing@ for unknown ones.
newtype Language = Language (T.Text -> Maybe SymbolType)

-- | The abstract syntax tree of a well-formed formula (WFF) in first-order logic.
--
-- WFFs support binary operators, negation, quantifiers, atoms, substitutions,
-- and metavariables.
data Wff
  = -- | Binary operation over two formulas: @and@, @or@, @implies@, or @iff@
    WffBinOp BinOp Wff Wff
  | -- | Logical negation
    WffNot Wff
  | -- | The logical constant True
    WffTrue
  | -- | The logical constant False
    WffFalse
  | -- | A quantifier binding to a variable
    WffQnt Quantifier T.Text Wff
  | -- | An atomic formula (predicate applied to arguments)
    WffAtom T.Text [Term]
  | -- | A metavariable ranging over WFFs
    WffMetavar T.Text
  | -- | Formula substitution: substitute a term for a variable in a formula
    WffSub Term T.Text Wff
  deriving (Show, Eq, Ord)

-- | Binary logical operators.
data BinOp
  = -- | Logical conjunction
    OpAnd
  | -- | Logical disjunction
    OpOr
  | -- | Logical implication
    OpImplies
  | -- | Logical biconditional (if and only if)
    OpIff
  deriving (Show, Eq, Ord)

-- | Logical quantifiers.
data Quantifier
  = -- | Universal quantification (for all)
    QntForall
  | -- | Existential quantification (there exists)
    QntExists
  | -- | Uniqueness quantification (there exists exactly one)
    QntUnique
  deriving (Show, Eq, Ord)

-- | A term in first-order logic.
--
-- Terms represent values and can be composed into atomic formulas.
data Term
  = -- | Function application to arguments
    TrmFunc T.Text [Term]
  | -- | A variable (lowercase identifier, optionally with subscript)
    TrmVar T.Text
  | -- | A constant
    TrmConst T.Text
  | -- | A metavariable ranging over terms
    TrmMetavar T.Text
  | -- | Term substitution: substitute a term for a variable in a term
    TrmSub Term T.Text Term
  deriving (Show, Eq, Ord)

-- | Parse a formula string using the given language signature.
--
-- This is the main parsing function. It parses a complete formula string
-- (with no trailing input) into an abstract syntax tree.
--
-- Returns @Left@ with parse error details if parsing fails,
-- or @Right@ with the parsed formula if successful.
--
-- Examples:
--
-- > parseFormula lang "true"                    -- Right WffTrue
-- > parseFormula lang "(not false)"             -- Right (WffNot WffFalse)
-- > parseFormula lang "(and phi psi)"           -- Left (parse error)
parseFormula :: Language -> T.Text -> Either ParseError Wff
parseFormula l = parse (parseWff l <* eof) ""

-- | Unsafely parse a formula, throwing an exception on parse failure.
unsafeParseFormula :: Language -> T.Text -> Wff
unsafeParseFormula l form = case parseFormula l form of
  (Left err) -> error (show err)
  (Right wff) -> wff

-- | The primitive language containing only the built-in predicates.
--
-- Currently includes:
--
-- - @eq@: Equality predicate (arity 2)
-- - @in@: Set membership predicate (arity 2)
--
-- This language is automatically included in any parsing context.
primitives :: Language
primitives = Language $ \case
  "eq" -> Just $ SymPredicate 2
  "in" -> Just $ SymPredicate 2
  _ -> Nothing

-- | Combine two language signatures.
--
-- The result language recognizes symbols from both languages.
-- If a symbol is defined in both languages, the first language takes precedence.
union :: Language -> Language -> Language
union (Language sig1) (Language sig2) =
  let signature symbol = sig1 symbol A.<|> sig2 symbol
   in Language signature

-- Parse a well-formed formula in the given language.
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

-- Parse a binary operation formula
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

-- Parse a unary negation formula
parseUnaryOp :: Language -> Parser Wff
parseUnaryOp l = parens $ WffNot <$> (word "not" >> parseWff l)

-- Parse a quantified formula
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

-- Parse an atomic formula
parsePredicate :: Language -> Parser Wff
parsePredicate lang = parens $ do
  name <- T.pack <$> many1 asciiLetter
  arity <- tryMaybe (findPred lang name) ("Unknown predicate: " <> name)
  args <- count arity (parseTerm lang)
  return $ WffAtom name args

-- Parse a formula metavariable: phi, psi, or chi (optionally with _n subscript)
parseMetavariable :: Parser Wff
parseMetavariable = do
  var <- word "phi" <|> word "psi" <|> word "chi"
  subscript <- option "" parseSubscript
  return $ WffMetavar $ var <> subscript

-- Parse a formula substitution: (sub term var wff)
parseSubWff :: Language -> Parser Wff
parseSubWff l = parens $ do
  _ <- word "sub"
  trm <- parseTerm l
  TrmVar var <- parseVariable
  wff <- parseWff l
  return $ WffSub trm var wff

-- Parse a term in the given language.
-- Terms can be variables, constants, function applications, metavariables, or substitutions.
parseTerm :: Language -> Parser Term
parseTerm l = strip $ do
  try parseTermMetavar
    <|> try (parseFunction l)
    <|> try parseVariable
    <|> try (parseConstant l)
    <|> parseSubTrm l

-- Parse a term metavariable: 'trm' (optionally with _n subscript)
parseTermMetavar :: Parser Term
parseTermMetavar = do
  var <- word "trm"
  subscript <- option "" parseSubscript
  return $ TrmMetavar $ var <> subscript

-- Parse a function application: (func term1 term2 ...)
parseFunction :: Language -> Parser Term
parseFunction lang = parens $ do
  name <- T.pack <$> many1 asciiLetter
  arity <- tryMaybe (findFunc lang name) ("Unknown function: " <> name)
  args <- count arity (parseTerm lang)
  return $ TrmFunc name args

-- Parse a variable: a lowercase letter optionally followed by a subscript
parseVariable :: Parser Term
parseVariable = do
  varLetter <- satisfy isAsciiLower
  subscript <- option "" parseSubscript
  endWord
  return $ TrmVar $ T.cons varLetter subscript

-- Parse a constant
parseConstant :: Language -> Parser Term
parseConstant lang = do
  name <- T.pack <$> many1 asciiLetter
  guard $ existsConst lang name
  return $ TrmConst name

-- Parse a term substitution: (sub term1 var term2)
parseSubTrm :: Language -> Parser Term
parseSubTrm l = parens $ do
  _ <- word "sub"
  trm1 <- parseTerm l
  TrmVar var <- parseVariable
  trm2 <- parseTerm l
  return $ TrmSub trm1 var trm2

-- Parse a subscript: _n where n is a sequence of digits
parseSubscript :: Parser T.Text
parseSubscript = do
  underscore <- char '_'
  number <- many1 digit
  return $ T.pack $ underscore : number

-- Parse a word (case-insensitive string), ensuring it's not followed by alphanumeric characters
word :: String -> Parser T.Text
word str = T.pack <$> string' str <* endWord

-- Ensure the next character is not alphanumeric (word boundary)
endWord :: Parser ()
endWord = notFollowedBy alphaNum

-- Parse an ASCII letter
asciiLetter :: Parser Char
asciiLetter = satisfy $ \c -> isAscii c && isLetter c

-- Parse a value between parentheses, with surrounding whitespace stripped
parens :: Parser a -> Parser a
parens = between (char '(') (char ')') . strip

-- Strip leading and trailing whitespace from a parser
strip :: Parser a -> Parser a
strip = between spaces spaces

-- Convert a 'Maybe' value to a parser, failing with the given message if 'Nothing'
tryMaybe :: Maybe a -> T.Text -> Parser a
tryMaybe val msg = maybe (fail $ T.unpack msg) pure val

-- Look up a predicate's arity in the language signature
findPred :: Language -> T.Text -> Maybe Arity
findPred (Language signature) name
  | Just (SymPredicate arity) <- signature name = Just arity
  | otherwise = Nothing

-- Look up a function's arity in the language signature
findFunc :: Language -> T.Text -> Maybe Arity
findFunc (Language signature) name
  | Just (SymFunction arity) <- signature name = Just arity
  | otherwise = Nothing

-- Check if a symbol is a constant in the language signature
existsConst :: Language -> T.Text -> Bool
existsConst (Language signature) name
  | Just SymConstant <- signature name = True
  | otherwise = False
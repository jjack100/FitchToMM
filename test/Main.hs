module Main (main) where
import Test.Hspec
import qualified SyntaxProverSpec
import qualified MMProofSpec
import qualified NonfreeSpec
import qualified ReplacementSpec
import qualified CollectionSpec
import qualified DvrSpec

main :: IO ()
main = hspec $ do
  MMProofSpec.spec
  SyntaxProverSpec.spec
  NonfreeSpec.spec
  ReplacementSpec.spec
  CollectionSpec.spec
  DvrSpec.spec
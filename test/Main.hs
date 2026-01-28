module Main (main) where
import Test.Hspec
import qualified SyntaxProverSpec
import qualified MMProofSpec

main :: IO ()
main = hspec $ do
  MMProofSpec.spec
  SyntaxProverSpec.spec
import qualified Data.Map as M
import Control.Monad.State
import LambdaPi
import Test.Hspec

cVar :: Id -> CTerm
cVar = Inf . Var

cNat :: CTerm
cNat = Inf Nat

z :: CTerm
z = Inf Zero

s :: CTerm -> CTerm
s = Inf . Succ

one :: CTerm
one = s z

two :: CTerm
two = s one

three :: CTerm
three = s two

plus :: ITerm
plus =
  Lam
    "n"
    ( Inf $
        NatElim
          (Lam "n" (Inf $ Pi "x" cNat cNat))
          (Lam "n" (cVar "n"))
          (Lam "l" (Lam "rec" (Lam "x" (Inf (Succ $ Inf (Var "rec" :@: cVar "x"))))))
          (cVar "n")
    )
    ::: Inf (Pi "x" cNat (Inf $ Pi "y" cNat cNat))

main :: IO ()
main = hspec $ do
  describe "LambdaPi.subst" $ do
    it "[x -> y] λx. x == λx. x" $ do
      subst "x" (vfree "y") (VLam "x" (vfree "x")) `shouldBe` Right (VLam "x" (vfree "x"))
    it "[x -> y] λy. x == λy1. y" $ do
      subst "x" (vfree "y") (VLam "y" (vfree "x")) `shouldBe` Right (VLam "y1" (vfree "y"))
    it "[x -> y] λz. x == λz. y" $ do
      subst "x" (vfree "y") (VLam "z" (vfree "x")) `shouldBe` Right (VLam "z" (vfree "y"))

  describe "LambdaPi.typeInfer" $ do
    it "supports term-dependents-on-term" $ do
      let id' = Lam "x" (cVar "x") ::: Inf (Pi "_" (cVar "Bool") (cVar "Bool"))
      evalStateT (typeInfer id') (M.singleton "Bool" VStar) `shouldBe` Right (VPi "_" (vfree "Bool") (vfree "Bool"))

    it "supports term-dependents-on-type" $ do
      -- (λα x → x) :: ∀(α :: *).α -> α
      let id' = Lam "A" (Lam "x" (cVar "x")) ::: Inf (Pi "A" (Inf Star) (Inf (Pi "a" (cVar "A") (cVar "A"))))
      runTI (typeInfer id') `shouldBe` Right (VPi "A" VStar (VPi "a" (vfree "A") (vfree "A")))

    it "supports type-dependents-on-type" $ do
      -- λa. a :: * -> *
      let t = Lam "A" (cVar "A") ::: Inf (Pi "_" (Inf Star) (Inf Star))
      runTI (typeInfer t) `shouldBe` Right (VPi "_" VStar VStar)

  describe "LambdaPi.NatElimator" $ do
    it "plus works correctly" $ do
      eval (plus :@: one :@: two) `shouldBe` eval three

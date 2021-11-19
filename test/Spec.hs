import qualified Data.Map as M

import LambdaPi
-- import LambdaPi (CTerm (..))
import Test.Hspec

cVar :: Id -> Term C
cVar = Inf . Var

cNat :: Term C
cNat = Inf Nat

z :: Term C
z = Inf Zero

s :: Term C -> Term C
s = Inf . Succ

one :: Term C
one = s z

two :: Term C
two = s one

three :: Term C
three = s two

plus :: Term I
plus =
  Ann (Lam
    "n"
    ( Inf $
        NatElim
          (Lam "n" (Inf $ Pi "x" cNat cNat))
          (Lam "n" (cVar "n"))
          (Lam "l" (Lam "rec" (Lam "x" (Inf (Succ $ Inf (App (Var "rec") (cVar "x")))))))
          (cVar "n")
    ))
    (Inf (Pi "x" cNat (Inf $ Pi "y" cNat cNat)))

main :: IO ()
main = hspec $ do
  describe "Value Eq" $ do
    it "λx. x == λy. y" $ do
      VLam "x" (vfree "x") == VLam "y" (vfree "y") `shouldBe` True

    it "Ɐ(A : *). A == Ɐ(B : *). B" $ do
      VPi "A" VStar (vfree "A") == VPi "B" VStar (vfree "B") `shouldBe` True

    it "Ɐ(A : *). B =/= Ɐ(B : *). B" $ do
      VPi "A" VStar (vfree "B") /= VPi "B" VStar (vfree "B") `shouldBe` True

    it "Pi (A : *) (A : A). A == Pi (A : *) (B : A). B" $ do
      VPi "A" VStar (VPi "A" (vfree "A") (vfree "A")) == VPi "A" VStar (VPi "B" (vfree "A") (vfree "B")) `shouldBe` True

  describe "LambdaPi.subst" $ do
    it "[x -> y] λx. x == λx. x" $ do
      subst "x" (vfree "y") (VLam "x" (vfree "x")) `shouldBe` VLam "x" (vfree "x")
    it "[x -> y] λy. x == λy1. y" $ do
      subst "x" (vfree "y") (VLam "y" (vfree "x")) `shouldBe` VLam "y1" (vfree "y")
    it "[x -> y] λz. x == λz. y" $ do
      subst "x" (vfree "y") (VLam "z" (vfree "x")) `shouldBe` VLam "z" (vfree "y")

  describe "LambdaPi.typeInfer" $ do
    it "supports term-dependents-on-term" $ do
      let id' = Ann (Lam "x" (cVar "x")) (Inf (Pi "_" (cVar "Bool") (cVar "Bool")))
      runTIWith (M.singleton "Bool" VStar) (typeInfer id') `shouldBe` Right (VPi "_" (vfree "Bool") (vfree "Bool"))

    it "supports term-dependents-on-type" $ do
      -- (λα x → x) :: ∀(α :: *).α -> α
      let id' = Ann (Lam "A" (Lam "x" (cVar "x"))) (Inf (Pi "A" (Inf Star) (Inf (Pi "a" (cVar "A") (cVar "A")))))
      runTI (typeInfer id') `shouldBe` Right (VPi "A" VStar (VPi "a" (vfree "A") (vfree "A")))

    it "supports type-dependents-on-type" $ do
      -- λa. a :: * -> *
      let t = Ann (Lam "A" (cVar "A")) (Inf (Pi "_" (Inf Star) (Inf Star)))
      runTI (typeInfer t) `shouldBe` Right (VPi "_" VStar VStar)

    it "supports type-dependents-on-term" $ do
      let t = Ann (Lam "n" (Refl (Inf Nat) (cVar "n"))) (Inf (Pi "n" (Inf Nat) (Inf $ Eq (Inf Nat) (cVar "n") (cVar "n"))))
      runTI (typeInfer t) `shouldBe` Right (VPi "n" VNat (VEq VNat (vfree "n") (vfree "n")))

  describe "LambdaPi.NatElimator" $ do
    -- it "plus works correctly" $ do
    --   eval (App (App plus one) two) `shouldBe` eval three

    it "Eq (1 + 2) 3" $ do
      let lemma = Ann (Refl (Inf Nat) three) (Inf (Eq (Inf Nat) (Inf (App (App plus one) two)) three))
      let v3 = VSucc (VSucc (VSucc VZero))
      runTI (typeInfer lemma) `shouldBe` Right (VEq VNat v3 v3)

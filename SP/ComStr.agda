module SP.ComStr where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.RPn.Base renaming (Bool* to BoolRefl)
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Data.Sigma
open import Cubical.Data.Bool renaming (elim to makepair)

record commf (X Y : Type) : Type₁ where
    field
        f : (Bool → X) → Y
        comstr : (B : 2-EltType₀) → (fst B → X) → Y
        coh : comstr BoolRefl ≡ f

composeCommf : {X Y Z : Type} → commf X Y → (Y → Z) → commf X Z
composeCommf (record {f = f; comstr = comstr; coh = coh}) g = record { 
        f = λ x → g (f x); 
        comstr = λ B x → g (comstr B x); 
        coh = cong (λ a x → g (a x)) coh 
    }

constantIsCommutative : {X Y : Type} → (y : Y) → (f : (Bool → X) → Y) → ((x : Bool → X) → f x ≡ y) → commf X Y
constantIsCommutative {X} {Y} y f const = record {
        f = f;
        comstr = λ B x → y;
        coh = sym (funExt const)
    }

BoolFlip : 2-EltType₀
BoolFlip = Bool , ∣ notEquiv ∣₁

flipPath : BoolRefl ≡ BoolFlip
flipPath = Σ≡Prop (λ _ → isPropPropTrunc) refl

applyType : {X : Type} → (b : 2-EltType₀) → ∥ ((Bool → X) → (fst b → X)) ∥₁
applyType (b , equiv) = PT.rec isPropPropTrunc (λ eqv → ∣ (λ f b → f (fst eqv b)) ∣₁) equiv

{-
commfComm : {X Y : Type} → (f : commf X Y) → (a b : X) → f .commf.f (makepair a b) ≡ f .commf.f (makepair b a)
commfComm {X} {Y} f a b = (def1 a b) ∙ defsEqual ∙ (sym def2) where

    def1 : (a b : X) → f .commf.f (makepair a b) ≡ f .commf.comstr BoolRefl (makepair a b)
    def1 a b = sym (cong (λ g → g (makepair a b)) (f .commf.coh))

    def15 : f .commf.comstr BoolRefl ≡ f .commf.comstr BoolFlip
    def15 = cong (λ g → f .commf.comstr g) flipPath

    def2 : f .commf.f (makepair b a) ≡ f .commf.comstr BoolFlip (makepair b a)
    def2 = (def1 b a) ∙ cong (λ g → g (makepair b a)) def15

    defsEqual : f .commf.comstr BoolRefl (makepair a b) ≡ f .commf.comstr BoolFlip (makepair b a)
    defsEqual = {!!}
-}
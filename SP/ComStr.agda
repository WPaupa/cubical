module SP.ComStr where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.RPn.Base renaming (Bool* to BoolRefl)
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Data.Bool

record commf (X Y : Type) : Type₁ where
    field
        f : (Bool → X) → Y
        comstr : (B : 2-EltType₀) → (fst B → X) → Y
        coh : comstr BoolRefl ≡ f

apply : {X Y : Type} → (f : commf X Y) → (a b : X) → Y
apply {X} {Y} f a b = f .commf.f helper where
    helper : Bool → X
    helper true = a
    helper false = b

composeCommf : {X Y Z : Type} → commf X Y → (Y → Z) → commf X Z
composeCommf (record {f = f; comstr = comstr; coh = coh}) g = record { 
        f = λ x → g (f x); 
        comstr = λ B x → g (comstr B x); 
        coh = cong (λ a x → g (a x)) coh 
    }

BoolFlip : 2-EltType₀
BoolFlip = Bool , ∣ notEquiv ∣₁

flipPath : ∥ BoolRefl ≡ BoolFlip ∥₁
flipPath = {!!}

commfcomm : {X Y : Type} → (f : commf X Y) → (a b : X) → apply f a b ≡ apply f b a
commfcomm = {!!} where
    f2 : (Bool → X) → Y
    f2 = comstr BoolFlip 
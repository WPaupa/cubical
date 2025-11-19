module SP.SP3 where

open import SP.Axiomatic
open import SP.ComStr

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Structures.TypeEqvTo

open import Cubical.HITs.PropositionalTruncation as PT
open import SP.RPn

open import Cubical.Data.Sigma
open import Cubical.Data.Sum as DS
open import Cubical.Data.Unit
open import Cubical.Data.Bool hiding (Bool*)

Three = Bool ⊎ Unit
3-EltType₀ = TypeEqvTo ℓ-zero Three
extend : 2-EltType₀ → 3-EltType₀
extend (B , eqv) = (B ⊎ Unit , PT.map (λ eq → ⊎-equiv eq (idEquiv _)) eqv)
Three* : 3-EltType₀
Three* = extend Bool* 
record comm3 (X Y : Type) : Type₁ where
    field
        f : (Three → X) → Y
        comstr : (B : 3-EltType₀) → (fst B → X) → Y
        coh : comstr Three* ≡ f

isSP³ : Type → Type → Type₁
isSP³ X SPX = Σ[ f ∈ comm3 X SPX ] ((T : Type) → (g : comm3 X T) → ∃![ h ∈ (SPX → T) ] ((x : Three → X) → h (f .comm3.f x) ≡ g .comm3.f x))

module SP²X→SP³X
    {X : Type}
    (bp : X)
    (SP²X SP³X : Type)
    (isSP²X : isSP X SP²X)
    (isSP³X : isSP³ X SP³X) where

    injOnRepr : commf X SP³X
    injOnRepr = record {
            f = λ x → fst isSP³X .comm3.f (DS.rec x (λ _ → bp));
            comstr = λ B x → fst isSP³X .comm3.comstr (extend B) 
                (DS.rec x (λ _ → bp));
            coh = cong (λ h x → h (DS.rec x (λ _ → bp))) (fst isSP³X .comm3.coh)
        }
 
    inj : SP²X → SP³X
    inj = snd isSP²X SP³X injOnRepr .fst .fst
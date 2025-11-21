module SP.SumSP where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv 
open import Cubical.Foundations.Univalence

open import SP.RPn

open import Cubical.Data.Bool hiding (Bool*)
open import Cubical.Data.Sigma

open import SP.ComStr
open import SP.Axiomatic

SP : Type₁ → Type₁
SP X = Σ[ B ∈ 2-EltType₀ ] (fst B → X)

inj : {X : Type₁} → commf X (SP X)
inj = record {
        f = λ x → (Bool* , x);
        comstr = λ B x → (B , x);
        coh = refl
    }

isSPSPX : {X : Type₁} → isSP X (SP X)
isSPSPX {X} = (inj , univ) where
    univ : (T : Type₁) → (g : commf X T) → ∃![ h ∈ (SP X → T) ] ((x : Bool → X) → h (inj .commf.f x) ≡ g .commf.f x)
    univ T g = uniqueExists liftg liftcoh liftcohuniv {!!} where
        liftg : SP X → T
        liftg (B , x) = g .commf.comstr B x

        liftcoh : (x : Bool → X) → liftg (inj .commf.f x) ≡ g .commf.f x
        liftcoh x = cong (λ f → f x) (g .commf.coh)

        liftuniv : (h : SP X → T) → ((x : Bool → X) → h (Bool* , x) ≡ g .commf.f x) → liftg ≡ h
        liftuniv h pf = funExt liftunivX where
            liftunivX : (x : SP X) → liftg x ≡ h x
            liftunivX (B , x) = {!!} where
                k : (x₁ : fst B) → (x₀ : fst B → X) → Σ[ x₂ ∈ (Bool → X) ] (h (B , x₀) ≡ h (Bool* , x₂))
                k x₁ = JRP∞ (λ B₀ t → ((x₀ : fst B₀ → X) → Σ[ x ∈ (Bool → X) ] h (B₀ , x₀) ≡ h (Bool* , x))) (λ x₀ → (x₀ , refl)) {B} {x₁} 

        liftcohuniv : (h : SP X → T) → (q r : (x : Bool → X) → h (Bool* , x) ≡ g .commf.f x) → q ≡ r
        liftcohuniv h q r = funExt liftcohunivX where
            liftcohunivX : (x : Bool → X) → q x ≡ r x
            liftcohunivX x = {!!}
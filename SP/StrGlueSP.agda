module SP.StrGlueSP where

open import SP.ComStr
open import SP.Axiomatic

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

open import Cubical.HITs.PropositionalTruncation as PT
open import SP.RPn -- by Ljungstrom and Warn

open import Cubical.Data.Bool hiding (Bool*) renaming (elim to makepair)
open import Cubical.Data.Unit
open import Cubical.Data.Sigma

data SP (X : Type) : Type₁ where
    com : (B : 2-EltType₀) → (fst B → X) → SP X
    coh : (B₁ B₂ : 2-EltType₀) → (b₁ : fst B₁) → (b₂ : fst B₂) → (x y : X) → 
        com B₁ (CasesRP B₁ b₁ x y) ≡ com B₂ (CasesRP B₂ b₂ x y)

recSP : {X Y : Type} → commf X Y → SP X → Y
recSP str (com B f) = str .commf.comstr B f
recSP str (coh B₁ B₂ b₁ b₂ x y i) = thesis i where
    s = str .commf.comstr

    mainLemma : (B : 2-EltType₀) → (b : fst B) → s B (CasesRP B b x y) ≡ s Bool* (makepair x y) 
    mainLemma B b = JRP∞ (λ B₀ b₀ → s B₀ (CasesRP B₀ b₀ x y) ≡ s Bool* (makepair x y)) (cong (s Bool*) (casesTrueFun x y))

    thesis : s B₁ (CasesRP B₁ b₁ x y) ≡ s B₂ (CasesRP B₂ b₂ x y)
    thesis = mainLemma B₁ b₁ ∙ sym (mainLemma B₂ b₂)
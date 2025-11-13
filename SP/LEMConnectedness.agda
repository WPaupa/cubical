module SP.LEMConnectedness where


open import Cubical.Foundations.Prelude

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.S1.Base

open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Sum
open import Cubical.Data.Bool

lem : Type₁
lem = (X : Type) → isProp X → (X ⊎ (X → ⊥))

lemOnTrue : (em : lem) → (X : Type) → (pr : isProp X) → (x : X) → em X pr ≡ inl x
lemOnTrue em X pr x = bycases (em X pr) where
  bycases : (k : (X ⊎ (X → ⊥))) → k ≡ inl x
  bycases (inl y) = cong inl (pr y x)
  bycases (inr u) = Cubical.Data.Empty.rec (u x)

lemOnFalse : (em : lem) → (X : Type) → (pr : isProp X) → (nx : X → ⊥) → em X pr ≡ inr nx
lemOnFalse em X pr nx = bycases (em X pr) where
  isPropX→⊥ : isProp (X → ⊥)
  isPropX→⊥ f g = funExt (λ x → isProp⊥ (f x) (g x))

  bycases : (k : (X ⊎ (X → ⊥))) → k ≡ inr nx
  bycases (inl y) = Cubical.Data.Empty.rec (nx y)
  bycases (inr u) = cong inr (isPropX→⊥ u nx)

connectedF : Type₁
connectedF = (X : Type) → (bp : X) →
  ((f : X → Bool) → (x : X) → f x ≡ f bp) → (x : X) → ∥ x ≡ bp ∥₁

classicality : lem → connectedF
classicality lem X bp eq x = by (cases x) where
  cases : (x : X) → (∥ x ≡ bp ∥₁) ⊎ (∥ x ≡ bp ∥₁ → ⊥)
  cases x = lem (∥ x ≡ bp ∥₁) isPropPropTrunc

  fromcases : {y : X} → ((∥ y ≡ bp ∥₁) ⊎ (∥ y ≡ bp ∥₁ → ⊥)) → Bool
  fromcases (inl x) = true
  fromcases (inr x) = false

  f : X → Bool
  f y = fromcases (cases y)

  xEq : fromcases (cases x) ≡ fromcases (cases bp)
  xEq = eq f x

  bpEq : fromcases (cases bp) ≡ true
  bpEq = cong fromcases (lemOnTrue lem (∥ bp ≡ bp ∥₁) isPropPropTrunc (∣ refl ∣₁))

  hardcase : (∥ x ≡ bp ∥₁ → ⊥) → ∥ x ≡ bp ∥₁
  hardcase conv = Cubical.Data.Empty.rec (false≢true false≡true) where
    xEqFalse : fromcases (cases x) ≡ false
    xEqFalse = cong fromcases (lemOnFalse lem (∥ x ≡ bp ∥₁) isPropPropTrunc conv)

    false≡true : false ≡ true
    false≡true = (sym xEqFalse) ∙ xEq ∙ bpEq

  by : ((∥ x ≡ bp ∥₁) ⊎ (∥ x ≡ bp ∥₁ → ⊥)) → ∥ x ≡ bp ∥₁
  by (inl x) = x
  by (inr x) = hardcase x

nonclassicality : connectedF → lem
nonclassicality connectedF X propX = {!!}
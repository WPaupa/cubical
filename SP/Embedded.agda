module SP.Embedded where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv 
open import Cubical.Foundations.Univalence

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.RPn.Base

open import Cubical.Data.Bool hiding (Bool*)
open import Cubical.Data.Unit

-- Definiujemy uproszczoną wersję SP X,
-- jako po prostu funkcje z każdego elementu RP∞ w X
data comSP (X : Type₁) : Type₁ where
  com : (B : 2-EltType₀) → (fst B → X) → comSP X

-- I faktyczne SP X jako takie funkcje plus constraint,
-- że na funkcji z basepointu RP∞ musi się zgadzać
-- z injekcją z X^2 w SP X (czyli de facto
-- chcielibyśmy, żeby to była ta injekcja + jej
-- struktura komutacji)
data comSP' (X : Type₁) : Type₁ where
  com' : (B : 2-EltType₀) → (fst B → X) → comSP' X
  inj' : (Bool → X) → comSP' X
  coh' : (f : Bool → X) → com' Bool* f ≡ inj' f

-- Ale możemy pokazać, że te dwie wersje SP X
-- są zgodne (przynajmniej dla typów na poziomie 1,
-- dla prostoty rozumowania)
consist : {X : Type₁} → comSP X ≡ comSP' X
consist {X} = ua (isoToEquiv (iso f g sec ret)) where
  f : comSP X → comSP' X
  f (com B x) = com' B x

  g : comSP' X → comSP X
  g (com' B x) = com B x
  g (inj' x) = com Bool* x
  g (coh' x i) = com Bool* x

  sec : (b : comSP' X) → f (g b) ≡ b
  sec (com' B x) = refl
  sec (inj' x) = coh' x
  sec (coh' x i) j = coh' x (i ∧ j)

  ret : (b : comSP X) → g (f b) ≡ b
  ret (com B x) = refl


-- A teraz pokażemy, że uproszczone SP
-- dla przestrzeni ściągalnej
-- daje RP∞ (więc jest niepoprawnie zdefiniowane)

-- Skoro Unit jest jednopunktowa,
-- to przestrzeń funkcji z dowolnego X do Unit też.
isPropXToUnit : (X : Type) → isProp (X → Unit* {ℓ-suc ℓ-zero})
isPropXToUnit X f g = funExt (λ x → isPropUnit* (f x) (g x))

-- Ta niepoprawność w tym wariancie jest dosyć intuicyjna:
-- nasza przestrzeń jest konstruowana przez com x c,
-- gdzie x : RP∞, a c : Unit, więc de facto sprowadza się do RP∞.
comOneRP : comSP Unit* ≡ 2-EltType₀
comOneRP = ua (isoToEquiv (iso f g sec ret)) where
  f : comSP Unit* → 2-EltType₀
  f (com (bool , path) c) = (bool , path)
  g : 2-EltType₀ → comSP Unit*
  g (bool , path) = com (bool , path) (λ x → tt*)
  sec : (b : 2-EltType₀) → f (g b) ≡ b
  sec (bool , path) = refl
  ret : (b : comSP Unit*) → g (f b) ≡ b
  ret (com (bool , path) c) =
      com (bool , path) (λ x → tt*)
    ≡⟨ cong (com (bool , path)) (isPropXToUnit bool (λ x → tt*) c) ⟩
      com (bool , path) c ∎
module SP.Naive where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

open import Cubical.HITs.S1

open import Cubical.Data.Unit


data NaiveSP (X : Type₀) : Type₀ where
    inj : X → X → NaiveSP X
    trunc : (a b : X) → inj a b ≡ inj b a


naiveDoesntWork : NaiveSP Unit ≡ S¹
naiveDoesntWork = isoToPath (iso f g eq1 eq2) where
    f : NaiveSP Unit → S¹
    f (inj x x₁) = base
    f (trunc a b i) = loop i

    g : S¹ → NaiveSP Unit
    g base = inj tt tt
    g (loop i) = trunc tt tt i

    eq1 : section f g
    eq1 base = refl
    eq1 (loop i) = refl

    eq2 : retract f g
    eq2 (inj tt tt) = refl
    eq2 (trunc tt tt i) = refl
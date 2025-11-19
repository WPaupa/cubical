{-

   A defintion of the real projective spaces following:

   [BR17] U. Buchholtz, E. Rijke, The real projective spaces in homotopy type theory.
           (2017) https://arxiv.org/abs/1704.05770

-}
{-# OPTIONS --safe #-}
module SP.RPn where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous

open import Cubical.Relation.Nullary

open import Cubical.Functions.Bundle

open import Cubical.Foundations.SIP
open import Cubical.Structures.Pointed
open import Cubical.Structures.TypeEqvTo

open import Cubical.Data.Bool hiding (elim ; Bool*)
open import Cubical.Data.Nat hiding (elim)
open import Cubical.Data.NatMinusOne
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥ hiding (elim)
open import Cubical.Data.Sum as ⊎ hiding (elim)

open import Cubical.HITs.PropositionalTruncation as PropTrunc hiding (elim)
open import Cubical.HITs.Sn
open import Cubical.HITs.Susp
open import Cubical.HITs.Join
open import Cubical.HITs.Pushout
open import Cubical.HITs.Pushout.Flattening

private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Type ℓ

-- PR² as a HIT
data RP² : Type₀ where
  point : RP²
  line : point ≡ point
  square : line ≡ sym line

-- RP²-lemmas
RP²Fun : (a : A) (p : a ≡ a) (p∼p⁻¹ : p ≡ sym p)
  → RP² → A
RP²Fun a p p∼p⁻¹ point = a
RP²Fun a p p∼p⁻¹ (line i) = p i
RP²Fun a p p∼p⁻¹ (square i i₁) = p∼p⁻¹ i i₁

elimSetRP² : {A : RP² → Type ℓ} → ((x : RP²) → isSet (A x))
  → (point* : A point)
  → PathP (λ i → A (line i)) point* point*
  → (x : RP²) → A x
elimSetRP² set point* p point = point*
elimSetRP² set point* p (line i) = p i
elimSetRP² {A = A} set point* p (square i j) =
  isOfHLevel→isOfHLevelDep 2 {B = A} set point* point* p (symP p) square i j

elimPropRP² : {A : RP² → Type ℓ} → ((x : RP²) → isProp (A x))
  → (point* : A point)
  → (x : RP²) → A x
elimPropRP² pr point* =
  elimSetRP² (λ x → isProp→isSet (pr _))
    point* (isProp→PathP (λ _ → pr _) _ _)

characRP²Fun : ∀ {ℓ} {A : Type ℓ} (f : RP² → A)
  → RP²Fun (f point) (cong f line) (λ i j → f (square i j)) ≡ f
characRP²Fun f =
  funExt λ { point → refl ; (line i) → refl ; (square i i₁) → refl}

-- Definition II.1 in [BR17], see also Cubical.Functions.Bundle

2-EltType₀    = TypeEqvTo    ℓ-zero Bool -- Σ[ X ∈ Type₀ ] ∥ X ≃ Bool ∥
2-EltPointed₀ = PointedEqvTo ℓ-zero Bool -- Σ[ X ∈ Type₀ ] X × ∥ X ≃ Bool ∥

RP∞ = 2-EltType₀

Bool* : 2-EltType₀
Bool* = Bool , ∣ idEquiv _ ∣₁

ua-2-EltType₀ : (X Y : RP∞) → fst X ≃ fst Y → X ≡ Y
ua-2-EltType₀ X Y p = Σ≡Prop (λ _ → squash₁) (ua p)

ua-2-EltType₀-idEquiv : (X : RP∞) → ua-2-EltType₀ X X (idEquiv (fst X)) ≡ refl
ua-2-EltType₀-idEquiv X =
  ΣSquareSet (λ _ → isProp→isSet squash₁) uaIdEquiv

2-EltType₀→Prop : {B : RP∞ → Type ℓ}
  → ((x : _) → isProp (B x))
  → B Bool*
  → (x : _) → B x
2-EltType₀→Prop {B = B} p b =
  uncurry λ X → PropTrunc.elim (λ _ → p _)
    λ x → subst B (ua-2-EltType₀ Bool* (X , ∣ x ∣₁) (invEquiv x)) b

2-EltType₀→Propβ : {B : RP∞ → Type ℓ}
  → (pr : (x : _) → isProp (B x))
  → (b : B Bool*)
  → 2-EltType₀→Prop {B = B} pr b Bool* ≡ b
2-EltType₀→Propβ {B = B} p q =
    (λ i → subst B (ua-2-EltType₀ Bool* Bool* (invEquivIdEquiv Bool i)) q)
  ∙ (λ i → subst B (ua-2-EltType₀-idEquiv Bool* i) q)
  ∙ transportRefl q

-- Our first goal is to 'lift' `_⊕_ : Bool → Bool ≃ Bool` to a function `_⊕_ : A → A ≃ Bool`
--  for any 2-element type (A, ∣e∣).

-- `isContrBoolPointedEquiv` and `isContr-2-EltPointedEquiv` are contained in the proof
--  of Lemma II.2 in [BR17], though we prove `isContr-BoolPointedEquiv` more directly
--  with ⊕ -- [BR17] proves it for just the x = false case and uses notEquiv to get
--  the x = true case.

-- (λ y → x ⊕ y) is the unqiue pointed isomorphism (Bool , false) ≃ (Bool , x)
isContrBoolPointedEquiv : ∀ x → isContr ((Bool , false) ≃[ PointedEquivStr ] (Bool , x))
fst (isContrBoolPointedEquiv x) = ((λ y → x ⊕ y) , isEquiv-⊕ x) , ⊕-comm x false
snd (isContrBoolPointedEquiv x) (e , p)
  = Σ≡Prop (λ e → isSetBool (equivFun e false) x)
           (Σ≡Prop isPropIsEquiv (funExt λ { false → ⊕-comm x false ∙ sym p
                                           ; true  → ⊕-comm x true  ∙ sym q }))
  where q : e .fst true ≡ not x
        q with dichotomyBool (invEq e (not x))
        ... | inl q = invEq≡→equivFun≡ e q
        ... | inr q = ⊥.rec (not≢const x (sym (invEq≡→equivFun≡ e q) ∙ p))

-- Since isContr is a mere proposition, we can eliminate a witness ∣e∣ : ∥ X ≃ Bool ∥ to get
--  that there is therefore a unique pointed isomorphism (Bool , false) ≃ (X , x) for any
--  2-element pointed type (X , x, ∣e∣).
isContr-2-EltPointedEquiv : (X∙ : 2-EltPointed₀)
                         → isContr ((Bool , false , ∣ idEquiv Bool ∣₁) ≃[ PointedEqvToEquivStr Bool ] X∙)
isContr-2-EltPointedEquiv (X , x , ∣e∣)
  = PropTrunc.rec isPropIsContr
                  (λ e → J (λ X∙ _ → isContr ((Bool , false) ≃[ PointedEquivStr ] X∙))
                           (isContrBoolPointedEquiv (e .fst x))
                           (sym (pointed-sip _ _ (e , refl))))
                  ∣e∣

-- This unique isomorphism must be _⊕_ 'lifted' to X. This idea is alluded to at the end of the
--  proof of Theorem III.4 in [BR17], where the authors reference needing ⊕-comm.
module ⊕* (X : 2-EltType₀) where

  _⊕*_ : typ X → typ X → Bool
  y ⊕* z = invEquiv (fst (fst (isContr-2-EltPointedEquiv (fst X , y , snd X)))) .fst z

  -- we've already shown that this map is an equivalence on the right

  isEquivʳ : (y : typ X) → isEquiv (y ⊕*_)
  isEquivʳ y = invEquiv (fst (fst (isContr-2-EltPointedEquiv (fst X , y , snd X)))) .snd

  Equivʳ : typ X → typ X ≃ Bool
  Equivʳ y = (y ⊕*_) , isEquivʳ y

  -- any mere proposition that holds for (Bool, _⊕_) holds for (typ X, _⊕*_)
  -- this amounts to just carefully unfolding the PropTrunc.elim and J in isContr-2-EltPointedEquiv
  elim : ∀ {ℓ'} (P : (A : Type₀) (_⊕'_ : A → A → Bool) → Type ℓ') (propP : ∀ A _⊕'_ → isProp (P A _⊕'_))
         → P Bool _⊕_ → P (typ X) _⊕*_
  elim {ℓ'} P propP r = PropTrunc.elim {P = λ ∣e∣ → P (typ X) (R₁ ∣e∣)} (λ _ → propP _ _)
                                       (λ e → EquivJ (λ A e → P A (R₂ A e)) r e)
                                       (snd X)
    where R₁ : ∥ fst X ≃ Bool ∥₁ → typ X → typ X → Bool
          R₁ ∣e∣ y = invEq (fst (fst (isContr-2-EltPointedEquiv (fst X , y , ∣e∣))))
          R₂ : (B : Type₀) → B ≃ Bool → B → B → Bool
          R₂ A e y = invEq (fst (fst (J (λ A∙ _ → isContr ((Bool , false) ≃[ PointedEquivStr ] A∙))
                                        (isContrBoolPointedEquiv (e .fst y))
                                        (sym (pointed-sip (A , y) (Bool , e .fst y) (e , refl))))))

  -- as a consequence, we get that ⊕* is commutative, and is therefore also an equivalence on the left

  comm : (y z : typ X) → y ⊕* z ≡ z ⊕* y
  comm = elim (λ A _⊕'_ → (x y : A) → x ⊕' y ≡ y ⊕' x)
              (λ _ _ → isPropΠ2 (λ _ _ → isSetBool _ _))
              ⊕-comm

  isEquivˡ : (y : typ X) → isEquiv (_⊕* y)
  isEquivˡ y = subst isEquiv (funExt (λ z → comm y z)) (isEquivʳ y)

  Equivˡ : typ X → typ X ≃ Bool
  Equivˡ y = (_⊕* y) , isEquivˡ y

-- Lemma II.2 in [BR17], though we do not use it here
-- Note: Lemma II.3 is `pointed-sip`, used in `PointedEqvTo-sip`
isContr-2-EltPointed : isContr (2-EltPointed₀)
fst isContr-2-EltPointed = (Bool , false , ∣ idEquiv Bool ∣₁)
snd isContr-2-EltPointed A∙ = PointedEqvTo-sip Bool _ A∙ (fst (isContr-2-EltPointedEquiv A∙))


--------------------------------------------------------------------------------

-- Now we mutually define RP n and its double cover (Definition III.1 in [BR17]),
--  and show that the total space of this double cover is S n (Theorem III.4).

RP  : ℕ₋₁ → Type₀
cov⁻¹ : (n : ℕ₋₁) → RP n → 2-EltType₀ -- (see Cubical.Functions.Bundle)

RP neg1 = ⊥
RP (ℕ→ℕ₋₁ n) = Pushout (pr (cov⁻¹ (-1+ n))) (λ _ → tt)
{-
                         tt
   Total (cov⁻¹ (n-1)) — — — > Unit
            |                    ∙
        pr  |                    ∙  inr
            |                    ∙
            V                    V
        RP (n-1) ∙ ∙ ∙ ∙ ∙ ∙ > RP n := Pushout pr (const tt)
                      inl
-}

cov⁻¹ neg1 x = Bool*
cov⁻¹ (ℕ→ℕ₋₁ n) (inl x)          = cov⁻¹ (-1+ n) x
cov⁻¹ (ℕ→ℕ₋₁ n) (inr _)          = Bool*
cov⁻¹ (ℕ→ℕ₋₁ n) (push (x , y) i) = ua ((λ z → y ⊕* z) , ⊕*.isEquivʳ (cov⁻¹ (-1+ n) x) y) i , ∣p∣ i
  where open ⊕* (cov⁻¹ (-1+ n) x)
        ∣p∣ = isProp→PathP (λ i → squash₁ {A = ua (⊕*.Equivʳ (cov⁻¹ (-1+ n) x) y) i ≃ Bool})
                           (str (cov⁻¹ (-1+ n) x)) (∣ idEquiv _ ∣₁)
{-
                         tt
   Total (cov⁻¹ (n-1)) — — — > Unit
            |                    |
        pr  |     // ua α //     | Bool
            |                    |
            V                    V
        RP (n-1) - - - - - - > Type
                  cov⁻¹ (n-1)

   where α : ∀ (x : Total (cov⁻¹ (n-1))) → cov⁻¹ (n-1) (pr x) ≃ Bool
         α (x , y) = (λ z → y ⊕* z) , ⊕*.isEquivʳ y
-}

TotalCov≃Sn : ∀ n → Total (cov⁻¹ n) ≃ S n
TotalCov≃Sn neg1 = isoToEquiv (iso (λ { () }) (λ { () }) (λ { () }) (λ { () }))
TotalCov≃Sn (ℕ→ℕ₋₁ n) =
  Total (cov⁻¹ (ℕ→ℕ₋₁ n))           ≃⟨ i ⟩
  Pushout Σf Σg                      ≃⟨ ii ⟩
  join (Total (cov⁻¹ (-1+ n))) Bool  ≃⟨ iii ⟩
  S (ℕ→ℕ₋₁ n)                       ■
  where
{-
    (i) First we want to show that `Total (cov⁻¹ (ℕ→ℕ₋₁ n))` is equivalent to a pushout.
    We do this using the flattening lemma, which states:

    Given f,g,F,G,e such that the following square commutes:

             g
       A — — — — > C                 Define:   E : Pushout f g → Type
       |           |                           E (inl b) = F b
    f  |   ua e    |  G                        E (inr c) = G c
       V           V                           E (push a i) = ua (e a) i
       B — — — — > Type
             F

    Then, the total space `Σ (Pushout f g) E` is the following pushout:

                                Σg := (g , e a)
            Σ[ a ∈ A ] F (f a) — — — — — — — — > Σ[ c ∈ C ] G c
                   |                                ∙
    Σf := (f , id) |                                ∙
                   V                                V
            Σ[ b ∈ B ] F b ∙ ∙ ∙ ∙ ∙ ∙ ∙ ∙ ∙ ∙ > Σ (Pushout f g) E

    In our case, setting `f = pr (cov⁻¹ (n-1))`, `g = λ _ → tt`, `F = cov⁻¹ (n-1)`, `G = λ _ → Bool`,
     and `e = λ (x , y) → ⊕*.Equivʳ (cov⁻¹ (n-1) x) y` makes E equal (up to funExt) to `cov⁻¹ n`.

    Thus the flattening lemma gives us that `Total (cov⁻¹ n) ≃ Pushout Σf Σg`.
-}
    open FlatteningLemma {- f = -} (λ x → pr (cov⁻¹ (-1+ n)) x)  {- g = -} (λ _ → tt)
                         {- F = -} (λ x → typ (cov⁻¹ (-1+ n) x)) {- G = -} (λ _ → Bool)
                         {- e = -} (λ { (x , y) → ⊕*.Equivʳ (cov⁻¹ (-1+ n) x) y })
                         hiding (Σf ; Σg)

    cov⁻¹≃E : ∀ x → typ (cov⁻¹ (ℕ→ℕ₋₁ n) x) ≃ E x
    cov⁻¹≃E (inl x) = idEquiv _
    cov⁻¹≃E (inr x) = idEquiv _
    cov⁻¹≃E (push a i) = idEquiv _

    -- for easier reference, we copy these definitons here
    Σf : Σ[ x ∈ Total (cov⁻¹ (-1+ n)) ] typ (cov⁻¹ (-1+ n) (fst x)) → Total (cov⁻¹ (-1+ n))
    Σg : Σ[ x ∈ Total (cov⁻¹ (-1+ n)) ] typ (cov⁻¹ (-1+ n) (fst x)) → Unit × Bool
    Σf ((x , y) , z) = (x , z)       -- ≡ (f a , x)
    Σg ((x , y) , z) = (tt , y ⊕* z) -- ≡ (g a , (e a) .fst x)
      where open ⊕* (cov⁻¹ (-1+ n) x)

    i : Total (cov⁻¹ (ℕ→ℕ₋₁ n)) ≃ Pushout Σf Σg
    i = (Σ[ x ∈ RP (ℕ→ℕ₋₁ n) ] typ (cov⁻¹ (ℕ→ℕ₋₁ n) x)) ≃⟨ Σ-cong-equiv-snd cov⁻¹≃E ⟩
        (Σ[ x ∈ RP (ℕ→ℕ₋₁ n) ] E x)                     ≃⟨ flatten ⟩
        Pushout Σf Σg                                   ■
{-
    (ii) Next we want to show that `Pushout Σf Σg` is equivalent to `join (Total (cov⁻¹ (n-1))) Bool`.
    Since both are pushouts, this can be done by defining a diagram equivalence:

                          Σf                                                  Σg
    Total (cov⁻¹ (n-1)) < — — Σ[ x ∈ Total (cov⁻¹ (n-1)) ] cov⁻¹ (n-1) (pr x) — — > Unit × Bool
            |                                        ∙                                   |
        id  |≃                                    u  ∙≃                             snd  |≃
            V                                        V                                   V
    Total (cov⁻¹ (n-1)) < — — — — — — — Total (cov⁻¹ (n-1)) × Bool — — — — — — — — — > Bool
                              proj₁                                      proj₂

    where the equivalence u above must therefore satisfy: `u .fst x ≡ (Σf x , snd (Σg x))`
    Unfolding this, we get: `u .fst ((x , y) , z) ≡ ((x , z) , (y ⊕* z))`

    It suffices to show that the map y ↦ y ⊕* z is an equivalence, since we can then express u as
     the following composition of equivalences:
    ((x , y) , z) ↦ (x , (y , z)) ↦ (x , (z , y)) ↦ (x , (z , y ⊕* z)) ↦ ((x , z) , y ⊕* z)

    This was proved above by ⊕*.isEquivˡ.
-}
    u : ∀ {n} → (Σ[ x ∈ Total (cov⁻¹ n) ] typ (cov⁻¹ n (fst x))) ≃ (Total (cov⁻¹ n) × Bool)
    u {n} = Σ[ x ∈ Total (cov⁻¹ n) ] typ (cov⁻¹ n (fst x))      ≃⟨ Σ-assoc-≃ ⟩
            Σ[ x ∈ RP n ] (typ (cov⁻¹ n x)) × (typ (cov⁻¹ n x)) ≃⟨ Σ-cong-equiv-snd (λ x → Σ-swap-≃) ⟩
            Σ[ x ∈ RP n ] (typ (cov⁻¹ n x)) × (typ (cov⁻¹ n x)) ≃⟨ Σ-cong-equiv-snd
                                                                   (λ x → Σ-cong-equiv-snd
                                                                     (λ y → ⊕*.Equivˡ (cov⁻¹ n x) y)) ⟩
            Σ[ x ∈ RP n ] (typ (cov⁻¹ n x)) × Bool              ≃⟨ invEquiv Σ-assoc-≃ ⟩
            Total (cov⁻¹ n) × Bool                              ■

    H : ∀ x → u .fst x ≡ (Σf x , snd (Σg x))
    H x = refl

    nat : 3-span-equiv (3span Σf Σg) (3span {A2 = Total (cov⁻¹ (-1+ n)) × Bool} fst snd)
    nat = record { e0 = idEquiv _ ; e2 = u ; e4 = ΣUnit _
                 ; H1 = λ x → cong fst (H x)
                 ; H3 = λ x → cong snd (H x) }

    ii : Pushout Σf Σg ≃ join (Total (cov⁻¹ (-1+ n))) Bool
    ii = compEquiv (pathToEquiv (spanEquivToPushoutPath nat)) (joinPushout≃join _ _)

{-
    (iii) Finally, it's trivial to show that `join (Total (cov⁻¹ (n-1))) Bool` is equivalent to
     `Susp (Total (cov⁻¹ (n-1)))`. Induction then gives us that `Susp (Total (cov⁻¹ (n-1)))`
     is equivalent to `S n`, which completes the proof.
-}

    iii : join (Total (cov⁻¹ (-1+ n))) Bool ≃ S (ℕ→ℕ₋₁ n)
    iii = join (Total (cov⁻¹ (-1+ n))) Bool ≃⟨ invEquiv Susp≃joinBool ⟩
          Susp (Total (cov⁻¹ (-1+ n)))      ≃⟨ congSuspEquiv (TotalCov≃Sn (-1+ n)) ⟩
          S (ℕ→ℕ₋₁ n)                      ■

-- the usual covering map S n → RP n, with fibers exactly cov⁻¹

cov : (n : ℕ₋₁) → S n → RP n
cov n = pr (cov⁻¹ n) ∘ invEq (TotalCov≃Sn n)

fibcov≡cov⁻¹ : ∀ n (x : RP n) → fiber (cov n) x ≡ cov⁻¹ n x .fst
fibcov≡cov⁻¹ n x =
  fiber (cov n)        x ≡[ i ]⟨ fiber {A = ua e i} (pr (cov⁻¹ n) ∘ ua-unglue e i) x ⟩
  fiber (pr (cov⁻¹ n)) x ≡⟨ ua (fibPrEquiv (cov⁻¹ n) x) ⟩
  cov⁻¹ n x .fst         ∎
  where e = invEquiv (TotalCov≃Sn n)


--------------------------------------------------------------------------------

-- Finally, we state the trivial equivalences for RP 0 and RP 1 (Example III.3 in [BR17])

RP0≃Unit : RP 0 ≃ Unit
RP0≃Unit = isoToEquiv (iso (λ _ → tt) (λ _ → inr tt) (λ _ → refl) (λ { (inr tt) → refl }))

RP1≡S1 : RP 1 ≡ S 1
RP1≡S1 = Pushout {A = Total (cov⁻¹ 0)} {B = RP 0} (pr (cov⁻¹ 0)) (λ _ → tt) ≡⟨ i ⟩
         Pushout {A = Total (cov⁻¹ 0)} {B = Unit} (λ _ → tt)     (λ _ → tt) ≡⟨ ii ⟩
         Pushout {A = S 0}             {B = Unit} (λ _ → tt)     (λ _ → tt) ≡⟨ PushoutSusp≡Susp ⟩
         S 1                                                                ∎
  where i = λ i → Pushout {A = Total (cov⁻¹ 0)}
                          {B = ua RP0≃Unit i}
                          (λ x → ua-gluePt RP0≃Unit i (pr (cov⁻¹ 0) x))
                          (λ _ → tt)
        ii = λ j → Pushout {A = ua (TotalCov≃Sn 0) j} (λ _ → tt) (λ _ → tt)

-- properties of RP∞
≡RP∞-charac : (X Y : RP∞) → Iso (fst X ≡ fst Y) (X ≡ Y)
Iso.fun (≡RP∞-charac X Y) p = Σ≡Prop (λ _ → squash₁) p
Iso.inv (≡RP∞-charac X Y) = cong fst
Iso.rightInv (≡RP∞-charac X Y) p =
  ΣSquareSet (λ _ → isProp→isSet squash₁) λ _ i → p i .fst
Iso.leftInv (≡RP∞-charac X Y) p = refl

Bool≃Charac : Iso (Bool ≃ Bool) Bool
Bool≃Charac = iso F G
    (λ { false → refl ; true → refl})
    λ e → Σ≡Prop isPropIsEquiv (funExt (F→G→F e))
    where
    F : Bool ≃ Bool → Bool
    F e = fst e true

    G : Bool → Bool ≃ Bool
    G false = notEquiv
    G true = idEquiv Bool

    F→G→F : (e : Bool ≃ Bool) (x : Bool) → G (F e) .fst x ≡ e .fst x
    F→G→F e with (dichotomyBool (fst e true))
                | (dichotomyBool (fst e false))
    ... | inl p | inl q = ⊥.rec
        (true≢false (sym (retEq e true)
                ∙∙ cong (invEq e) (p ∙ sym q)
                ∙∙ retEq e false))
    ... | inl p | inr q =
        λ { false → (λ i → G (p i) .fst false) ∙ sym q
        ; true → (λ i → G (p i) .fst true) ∙ sym p}
    ... | inr p | inl q =
        λ { false → (λ i → G (p i) .fst false) ∙ sym q
        ; true → (λ i → G (p i) .fst true) ∙ sym p}
    ... | inr p | inr q =
        ⊥.rec (true≢false  (sym (retEq e true)
                        ∙∙ cong (invEq e) (p ∙ sym q)
                        ∙∙ retEq e false))

isGroupoidRP∞ : isGroupoid RP∞
isGroupoidRP∞ =
 uncurry λ X → PropTrunc.elim (λ _ → isPropΠ λ _ → isPropIsSet)
  (EquivJ (λ X x → (b : RP∞) → isSet (Path RP∞ (X , ∣ x ∣₁) b))
    (uncurry λ Y → PropTrunc.elim (λ _ → isPropIsSet)
      (EquivJ (λ Y x → isSet (Path RP∞ (Bool , ∣ idEquiv Bool ∣₁) (Y , ∣ x ∣₁)))
        (isOfHLevelRetractFromIso 2
          (compIso (invIso (≡RP∞-charac Bool* Bool*))
            (compIso (equivToIso univalence) Bool≃Charac)) isSetBool))))

isSet-2elt : (X : RP∞) → isSet (fst X)
isSet-2elt = 2-EltType₀→Prop (λ _ → isPropIsSet) isSetBool

isContrTotalRP∞ : isContr (Σ[ X ∈ RP∞ ] fst X)
fst isContrTotalRP∞ = Bool* , true
snd isContrTotalRP∞ = isContr→isProp isC _
  where
  totIso : Iso (Σ[ X ∈ RP∞ ] fst X) 2-EltPointed₀
  totIso = compIso Σ-assoc-Iso (Σ-cong-iso-snd λ X → Σ-swap-Iso)

  isC : isContr (Σ[ X ∈ RP∞ ] fst X)
  isC = isOfHLevelRetractFromIso 0 totIso isContr-2-EltPointed

JRP∞ : ∀ {ℓ} (A : (X : RP∞) (x : fst X) → Type ℓ)
  → A Bool* true
  → {X : _} {x : _} → A X x
JRP∞ A t {X = X} {x = x} = A'Sec (X , x)
  where
  A' : Σ[ X ∈ RP∞ ] (fst X) → Type _
  A' (X , x) = A X x

  A'Sec : (m : Σ[ X ∈ RP∞ ] (fst X)) → A' m
  A'Sec m = subst A' (isContrTotalRP∞ .snd m) t

-- direct construction of involution for two element types
notRP∞Equiv : (X : RP∞) → Σ[ e ∈ (fst X ≃ fst X) ] ¬ e ≡ idEquiv (fst X)
notRP∞Equiv =
  2-EltType₀→Prop isPropNegRP∞
    (notEquiv , (λ p → true≢false (funExt⁻ (cong fst p) false)))
  where
  isPropNegBool : isProp (Σ[ e ∈ (Bool ≃ Bool) ] ¬ e ≡ idEquiv Bool)
  isPropNegBool = isContr→isProp help
    where
    help : isContr (Σ[ e ∈ (Bool ≃ Bool) ] ¬ e ≡ idEquiv Bool)
    fst help = notEquiv , (λ p → true≢false (funExt⁻ (cong fst p) false))
    snd help (e , g) =
      Σ≡Prop (λ _ → isProp¬ _)
        (⊎.rec (λ p → ⊥.rec (g (sym (Iso.leftInv Bool≃Charac e)
                      ∙ cong (Iso.inv Bool≃Charac) p)))
                (λ p → sym (cong (Iso.inv Bool≃Charac) p)
                          ∙ (Iso.leftInv Bool≃Charac e))
                (dichotomyBool (fst e true)))

  isPropNegRP∞ : (X : RP∞) → isProp (Σ[ e ∈ (fst X ≃ fst X) ] ¬ e ≡ idEquiv (fst X))
  isPropNegRP∞ = 2-EltType₀→Prop (λ _ → isPropIsProp) isPropNegBool

notRP∞ : (X : RP∞) → fst X → fst X
notRP∞ X = fst (fst (notRP∞Equiv X))

notRP∞-notConst : (X : RP∞) → ¬ ((x : fst X) → notRP∞ X x ≡ x)
notRP∞-notConst =
  uncurry λ X → PropTrunc.elim (λ _ → isProp¬ _)
    (EquivJ (λ X x → ¬ ((x₁ : X) → notRP∞ (X , ∣ x ∣₁) x₁ ≡ x₁))
      λ p → true≢false (p false))

-- Direct construction of the elimination principle for two element types

CasesBool-true : ∀ {ℓ} {A : Bool → Type ℓ} (x₀ : Bool)
  → A true → A false → A x₀
CasesBool-true false p q = q
CasesBool-true true p q = p

CasesBool : ∀ {ℓ} {A : Bool → Type ℓ} (x₀ : Bool)
  → A x₀ → A (not x₀) → (x : _) → A x
CasesBool {A = A} false p q y = CasesBool-true {A = A} y q p
CasesBool {A = A} true p q y = CasesBool-true {A = A} y p q

CasesBoolβ : ∀ {ℓ} {A : Bool → Type ℓ} (x₀ : Bool)
  → (l : A x₀) (r : A (not x₀))
  → (CasesBool {A = A} x₀ l r x₀ ≡ l)
   × (CasesBool {A = A} x₀ l r (not x₀) ≡ r)
CasesBoolβ {A = A} false l r = refl , refl
CasesBoolβ {A = A} true l r = refl , refl

CasesBoolη : ∀ {ℓ} {A : Bool → Type ℓ} (f : (x : Bool) → A x)
  → CasesBool {A = A} true (f true) (f false) ≡ f
CasesBoolη f i false = f false
CasesBoolη f i true = f true

ΠBool→× : ∀ {ℓ} {A : Bool → Type ℓ} → ((x : _) → A x) → A true × A false
ΠBool→× f = f true , f false

×→ΠBool : ∀ {ℓ} {A : Bool → Type ℓ} → A true × A false → ((x : _) → A x)
×→ΠBool (a , b) = CasesBool true a b

ΠBool×Iso : ∀ {ℓ} {A : Bool → Type ℓ}
  → Iso ((x : _) → A x) (A true × A false)
Iso.fun ΠBool×Iso = ΠBool→×
Iso.inv ΠBool×Iso = ×→ΠBool
Iso.rightInv ΠBool×Iso a = refl
Iso.leftInv ΠBool×Iso a i false = a false
Iso.leftInv ΠBool×Iso a i true = a true

-- setup
private
  RP∞-elim-ty' : (X : RP∞) (x : fst X) (A : fst X → Type ℓ) → Type ℓ
  RP∞-elim-ty' X x A =
    Σ[ f ∈ ((a : A x) (b : A (notRP∞ X x)) → (x : _) → A x) ]
     ((a : _) (b : _) → (f a b x ≡ a) × (f a b (notRP∞ X x) ≡ b))

  RP∞-elim-ty : (X : RP∞) (A : fst X → Type ℓ) → Type ℓ
  RP∞-elim-ty X A = (x : fst X) → RP∞-elim-ty' X x A

  isPropRP∞-elim-ty : (X : RP∞) (A : fst X → Type ℓ) → isProp (RP∞-elim-ty X A)
  isPropRP∞-elim-ty {ℓ = ℓ} X A = isPropΠ λ x
    → JRP∞ (λ X x → (A : fst X → Type ℓ) → isProp (RP∞-elim-ty' X x A))
            (λ A → isContr→isProp CasesBool*) {X = X} {x} A
    where
    CasesBool* : {A : Bool → Type ℓ}
      → isContr (Σ[ f ∈ (A true → A false → (x : _) → A x) ]
          ((a : A true) (b : A false) → (f a b true ≡ a) × (f a b false ≡ b)))
    fst (fst CasesBool*) a b false = b
    fst (fst CasesBool*) a b true = a
    snd (fst CasesBool*) a b = refl , refl
    fst (snd CasesBool* (f , p) i) a b false = p a b .snd (~ i)
    fst (snd CasesBool* (f , p) i) a b true = p a b .fst (~ i)
    fst (snd (snd CasesBool* (f , p) i) a b) j = p a b .fst (~ i ∨ j)
    snd (snd (snd CasesBool* (f , p) i) a b) j = p a b .snd (~ i ∨ j)

  CasesRP' : (X : RP∞) (A : fst X → Type ℓ) → RP∞-elim-ty X A
  CasesRP' {ℓ = ℓ} =
    uncurry λ X
    → PropTrunc.elim (λ x → isPropΠ (isPropRP∞-elim-ty (X , x)))
        (CasesRP-base X)
    where
    CasesRP-base : (X : Type) (x : X ≃ Bool) (A : X → Type ℓ)
      → RP∞-elim-ty (X , ∣ x ∣₁) A
    CasesRP-base X =
      EquivJ (λ X x → (A : X → Type ℓ) → RP∞-elim-ty (X , ∣ x ∣₁) A)
              λ A g → CasesBool {A = A} g , CasesBoolβ {A = A} g

-- elimination
CasesRP : ∀ {ℓ} (X : RP∞) {A : fst X → Type ℓ} (x₀ : fst X)
  → A x₀ → A (notRP∞ X x₀) → (x : _) → A x
CasesRP X {A = A} x₀ = CasesRP' X A x₀ .fst

CasesRPβ : ∀ {ℓ} (X : RP∞) {A : fst X → Type ℓ} (x₀ : fst X)
  → (l : A x₀) (r : A (notRP∞ X x₀))
  → (CasesRP X {A = A} x₀ l r x₀ ≡ l)
   × (CasesRP X {A = A} x₀ l r (notRP∞ X x₀) ≡ r)
CasesRPβ X x₀ = CasesRP' X _ x₀ .snd

-- alternative definition of RP∞, useful to get strict
-- computation rules
is2Type : (ℓ' : Level) (X : Type) → Type (ℓ-suc ℓ')
is2Type ℓ' X =
  Σ[ neg ∈ (X → X) ]
    (¬ ((x : X) → neg x ≡ x)) × (((B : X → Type ℓ')
      → Σ[ elim ∈ ((x : X) (a : B x) (a' : B (neg x)) → (x : _) → B x) ]
         ((x : X) (a : B x) (a' : B (neg x))
           → (elim x a a' x ≡ a) × (elim x a a' (neg x) ≡ a'))))

isRP∞ : (ℓ : Level) → (X : Type) → Type (ℓ-suc ℓ)
isRP∞ ℓ X = is2Type ℓ X × ∥ X ∥₁

RP∞' : (ℓ : Level) → Type (ℓ-suc ℓ)
RP∞' ℓ = Σ[ X ∈ Type ] isRP∞ ℓ X

module RP∞'-fields {ℓ} (I : RP∞' ℓ) where
  notRP∞' = snd I .fst .fst
  elimRP∞' : {B : fst I → Type ℓ} → _
  elimRP∞' {B = B} = snd I .fst .snd .snd B .fst
  elimRP∞'β : {B : fst I → Type ℓ} → _
  elimRP∞'β {B = B} = snd I .fst .snd .snd B .snd

isRP∞→≃Bool : (ℓ : Level) (X : Type) → is2Type ℓ X → X → X ≃ Bool
isRP∞→≃Bool ℓ X f x = compEquiv (isoToEquiv (theIs f x)) (invEquiv LiftEquiv)
  where
  module _ (f : is2Type ℓ X) (x : X) where
    help : X → Lift Bool
    help = fst (f .snd .snd (λ _ → Lift Bool)) x (lift true)
      (lift false)

    LiftB→X : Lift Bool → X
    LiftB→X (lift false) = fst f x
    LiftB→X (lift true) = x

    theIs : Iso X (Lift Bool)
    Iso.fun theIs = help
    Iso.inv theIs = LiftB→X
    Iso.rightInv theIs (lift false) =
      f .snd .snd (λ _ → Lift Bool) .snd x (lift true) (lift false) .snd
    Iso.rightInv theIs (lift true) =
      f .snd .snd (λ _ → Lift Bool) .snd x (lift true) (lift false) .fst
    Iso.leftInv theIs x' = cong (invEq (LiftEquiv {ℓ' = ℓ})) (liftEq x')
      where
      liftEq : (x' : X) → lift (LiftB→X (help x')) ≡ lift x'
      liftEq =  f .snd .snd _ .fst x
        (cong lift (cong LiftB→X
          (f .snd .snd (λ _ → Lift Bool) .snd x (lift true) (lift false) .fst)))
        (cong lift (cong LiftB→X (f .snd .snd (λ _ → Lift Bool) .snd
          x (lift true) (lift false) .snd)))

-- instances
is2TypeBool : (ℓ : Level) → is2Type ℓ Bool
fst (is2TypeBool ℓ) = not
fst (snd (is2TypeBool ℓ)) = notRP∞-notConst Bool*
fst (snd (snd (is2TypeBool ℓ)) B) = CasesBool
snd (snd (snd (is2TypeBool ℓ)) B) = CasesBoolβ

RP∞'∙ : (ℓ : Level) → RP∞' ℓ
RP∞'∙ ℓ = Bool , ((is2TypeBool ℓ) , ∣ true ∣₁)

-- Every (X : RP∞ is a 2-type)
RP∞-2Type : (ℓ : Level) (X : RP∞) → is2Type ℓ (fst X)
fst (RP∞-2Type ℓ X) = notRP∞ X
fst (snd (RP∞-2Type ℓ X)) = notRP∞-notConst X
fst (snd (snd (RP∞-2Type ℓ X)) B) = CasesRP X
snd (snd (snd (RP∞-2Type ℓ X)) B) = CasesRPβ X {B}

isPropis2Type : ∀ {ℓ} (X : RP∞) → isProp (is2Type ℓ (fst X))
isPropis2Type {ℓ = ℓ} =
  2-EltType₀→Prop (λ _ → isPropIsProp) (isContr→isProp isContrIs2TypeBool)
  where
  isContrIs2TypeBool : isContr (is2Type ℓ Bool)
  fst isContrIs2TypeBool = is2TypeBool _
  snd isContrIs2TypeBool (f , (n , p)) =
    ΣPathP ((sym f≡not) , isProp→PathP (λ j → isProp× (isProp¬ _)
      (isPropΠ λ B
      → transport (λ k → isProp
        (Σ ((x : Bool) → B x → B (f≡not (~ j ∨ ~ k) x)
                       → (a : Bool) → B a)
         (λ elim₁ → (x : Bool) (a : B x) (a' : B (f≡not (~ j ∨ ~ k) x))
          → (elim₁ x a a' x ≡ a) × (elim₁ x a a' (f≡not (~ j ∨ ~ k) x) ≡ a'))))
              (isPr B))) _ _)
    where
    isPr : (B : Bool → Type ℓ) → isProp _
    isPr B (f , p) (g , q) i =
        (λ x a b y → id1 x a b y i)
      , (λ x a a' → id2 x a a' i)
      where
      id1 : (x : Bool) (a : _) (b : _) (y : Bool) → f x a b y ≡ g x a b y
      id1 false a b false = p false a b .fst  ∙∙ refl ∙∙ sym (q false a b .fst)
      id1 false a b true = p false a b .snd ∙∙ refl ∙∙ sym (q false a b .snd)
      id1 true a b false = p true a b .snd ∙∙ refl ∙∙ sym (q true a b .snd)
      id1 true a b true = p true a b .fst ∙∙ refl ∙∙ sym (q true a b .fst)

      id2 : (x : Bool) (a : B x) (a' : B (not x))
        → PathP (λ i → (id1 x a a' x i ≡ a) × (id1 x a a' (not x) i ≡ a'))
                 (p x a a') (q x a a')
      fst (id2 false a a' i) j =
        doubleCompPath-filler (fst (p false a a')) refl (sym (fst (q false a a'))) (~ j) i
      snd (id2 false a a' i) j =
        doubleCompPath-filler (snd (p false a a')) refl (sym (snd (q false a a'))) (~ j) i
      fst (id2 true a a' i) j =
        doubleCompPath-filler (fst (p true a a')) refl (sym (fst (q true a a'))) (~ j) i
      snd (id2 true a a' i) j =
        doubleCompPath-filler (snd (p true a a')) refl (sym (snd (q true a a'))) (~ j) i

    notConst : ¬ (f false ≡ f true)
    notConst r = true≢false (isContr→isProp isContrBool _ _)
      where
      Lift→ : ∀ {ℓ'} {A : Type} → Lift {ℓ-zero} {ℓ'} A → A
      Lift→ (lift lower₁) = lower₁

      main : (x : _) → f false ≡ x → (z : Bool) → z ≡ f false
      main false ha x = cong (Lift→ {ℓ})
        (p (λ x → lift x ≡ lift (f false)) .fst false (cong lift (sym ha)) refl x)
      main true ha x = cong (Lift→ {ℓ})
        (p _ .fst true (cong lift (sym ha)) (cong lift (sym r)) x)

      isContrBool : isContr Bool
      isContrBool = (f false) , sym ∘ main (f false) refl

    lem : (y y' : Bool) → f true ≡ y → f false ≡ y' → (x : _) → f x ≡ not x
    lem false false p q = ⊥.rec (notConst (q ∙ sym p))
    lem false true p q = λ { false → q ; true → p}
    lem true false p q = ⊥.rec (n λ { false → q ; true → p})
    lem true true p q = ⊥.rec (notConst (q ∙ sym p))

    f≡not : f ≡ not
    f≡not = funExt (lem (f true) (f false) refl refl)

isPropIsRP∞ : ∀ (ℓ) (X : Type) → isProp (isRP∞ ℓ X)
isPropIsRP∞ ℓ X (totY , y) (totY' , y') =
  isPropΣ (isPropis2Type (X , PropTrunc.map (isRP∞→≃Bool ℓ X totY) y')) (λ _ → squash₁) _ _

-- The two definitions are equivalent
RP∞'≃RP∞ : (ℓ : Level) → RP∞' ℓ ≃ RP∞
RP∞'≃RP∞ ℓ =
  isoToEquiv
    (iso
     (λ X → fst X , PropTrunc.map (isRP∞→≃Bool ℓ (fst X) (snd X .fst)) (snd X .snd))
     (λ X → (fst X) , (PropTrunc.rec (isPropΣ (isPropis2Type X) (λ _ → squash₁))
       ((λ x → fst x , ∣ x .snd ∣₁)
       ∘ (≃Bool→isRP∞ ℓ (fst X))) (snd X)))
     (λ X → Σ≡Prop (λ _ → squash₁) refl)
     λ X → Σ≡Prop (isPropIsRP∞ ℓ) refl)
  where
  ≃Bool→isRP∞ : (ℓ : Level) (X : Type) → X ≃ Bool → is2Type ℓ X × X
  fst (≃Bool→isRP∞ ℓ X eq) = help eq
    where
    help : X ≃ Bool → is2Type ℓ X
    help = EquivJ (λ X _ → is2Type ℓ X) (is2TypeBool _)
  snd (≃Bool→isRP∞ ℓ X eq) = invEq eq true

isGroupoidRP∞' : ∀ {ℓ} → isGroupoid (RP∞' ℓ)
isGroupoidRP∞' = isOfHLevelRetractFromIso 3 (equivToIso (RP∞'≃RP∞ _)) isGroupoidRP∞

isContrSiglRP∞' : (ℓ : Level) → isContr (Σ[ I ∈ RP∞' ℓ ] fst I)
fst (isContrSiglRP∞' ℓ) = RP∞'∙ ℓ , true
snd (isContrSiglRP∞' ℓ) (I , i) = ΣPathP ((lem I i)
  , (toPathP λ j → transp (λ _ → fst I) j i))
  where
  lem : (I : RP∞' ℓ) (i : fst I) → RP∞'∙ ℓ ≡ I
  lem I i =
    Σ≡Prop (λ _ → isPropIsRP∞ _ _)
     (ua (invEquiv (isRP∞→≃Bool ℓ (fst I) (snd I .fst) i)))

-- J for RP∞'
module _ {ℓ ℓ' : Level} {B : (I : RP∞' ℓ) → fst I → Type ℓ'} (c : B (RP∞'∙ _) true) where
  private
    B* : Σ[ I ∈ RP∞' ℓ ] fst I → Type ℓ'
    B* (I , i) = B I i

    JRP∞'-c : (x : _) → B* x
    JRP∞'-c p = subst B* (isContrSiglRP∞' ℓ .snd p) c

  JRP∞' : (I : RP∞' ℓ) (i : fst I) → B I i
  JRP∞' I i = JRP∞'-c (I , i)

  JRP∞'∙ : JRP∞' (RP∞'∙ _) true ≡ c
  JRP∞'∙ = (λ i → subst B* (isProp→isSet (isContr→isProp (isContrSiglRP∞' ℓ)) _ _
    (isContrSiglRP∞' ℓ .snd (RP∞'∙ _ , true)) refl i) c) ∙ transportRefl c

≡RP∞'-charac : {ℓ : Level} (I J : RP∞' ℓ) → Iso (I ≡ J) (fst I ≃ fst J)
≡RP∞'-charac {ℓ} I J =
  (iso (λ p → pathToEquiv (cong fst p ))
       (λ p → Σ≡Prop (isPropIsRP∞ ℓ) (ua p))
       (λ p → Σ≡Prop (λ _ → isPropIsEquiv _)
                 (funExt λ a → transportRefl (fst p a)))
       λ p → ΣSquareSet (λ _ → isProp→isSet (isPropIsRP∞ ℓ _))
               (retEq univalence (cong fst p)))

-- EquivJ for RP'∞
module _ {ℓ ℓ' : Level} (I : RP∞' ℓ)
         {B : (J : RP∞' ℓ) → fst I ≃ fst J → Type ℓ'}
         (c : B I (idEquiv _)) where
  private
    isContrTot : isContr (Σ[ J ∈ RP∞' ℓ ] fst I ≃ fst J)
    isContrTot =
      isOfHLevelRetractFromIso 0
        (Σ-cong-iso-snd (λ J → invIso (≡RP∞'-charac I J))) (isContrSingl I)

    B* : Σ[ J ∈ RP∞' ℓ ] fst I ≃ fst J → Type _
    B* (J , e) = B J e

  EquivJRP∞' : (J : RP∞' ℓ) (i : fst I ≃ fst J) → B J i
  EquivJRP∞' J i =
    subst B* (isContr→isProp isContrTot (I , idEquiv (fst I)) (J , i)) c

  EquivJRP∞'-idEquiv : EquivJRP∞' I (idEquiv (fst I)) ≡ c
  EquivJRP∞'-idEquiv =
    (λ i → subst B* (isProp→isSet (isContr→isProp isContrTot) _ _
                     (isContr→isProp isContrTot
                       (I , idEquiv (fst I)) (I , idEquiv (fst I))) refl i) c)
   ∙ transportRefl c

-- prop elimination for RP∞'
module _  {ℓ ℓ'} {B : (I : RP∞' ℓ) → Type ℓ'}
  (pr : (x : _) → isProp (B x))
  (c : B (RP∞'∙ ℓ)) where
  private
    contr : (X : RP∞' ℓ) (x : fst X) → fst X ≡ Bool
    contr X x = ua (isRP∞→≃Bool _ (fst X) (snd X .fst) x)

    isRP∞→≃Bool∙ : (isRP∞→≃Bool _ Bool (fst (snd (RP∞'∙ ℓ))) true) ≡ idEquiv Bool
    isRP∞→≃Bool∙ = Σ≡Prop (λ _ → isPropIsEquiv _) (funExt (CasesBool true refl refl))

    contr' : (X : RP∞' ℓ) (x : fst X) → X ≡ RP∞'∙ ℓ
    contr' X x = Σ≡Prop (λ x → isPropIsRP∞ _ x) (contr X x)

    contr≡ : contr' (RP∞'∙ ℓ) true ≡ refl
    contr≡ = ΣSquareSet (λ _ → isProp→isSet (isPropIsRP∞ _ _))
             (cong ua isRP∞→≃Bool∙ ∙ uaIdEquiv)

    abstract
      inder : (X : RP∞' ℓ) (x : fst X) → B (RP∞'∙ ℓ) → B X
      inder X x = subst B (sym (contr' X x))

      help' : inder (RP∞'∙ ℓ) true ≡ idfun _
      help' = cong (subst B) (cong sym contr≡) ∙ funExt transportRefl

  RP∞'pt→Prop : (x : _) → B x
  RP∞'pt→Prop =
    uncurry λ X
    → uncurry λ 2t
    → PropTrunc.elim (λ _ → pr _)
        (λ x → inder (X , 2t , ∣ x ∣₁) x c)

  RP∞'pt→Propβ :
      RP∞'pt→Prop (RP∞'∙ ℓ) ≡ c
  RP∞'pt→Propβ j = help' j c

RP∞'→SetRec : ∀ {ℓ} {A : Type ℓ} (s : isSet A) (X : RP∞' ℓ)
         → (f : fst X → A)
         → ((x : _) → f x ≡ f (RP∞'-fields.notRP∞' X x))
         → A
RP∞'→SetRec s = uncurry λ X
  → uncurry λ 2tx
  → elim→Set (λ _ → isSetΠ2 λ _ _ → s)
               (λ x f coh → f x)
               λ x → RP∞'-fields.elimRP∞' (X , 2tx , ∣ x ∣₁) x
                 (λ i f coh → f x)
                 λ i f coh → coh x i


RP∞'→SetRecβ :
  ∀ {ℓ} {A : Type ℓ} (s : isSet A) (X : _)
     (f : fst X → A)
     (h : (x : fst X) → f x ≡ f (RP∞'-fields.notRP∞' X x))
     (x : fst X)
     → RP∞'→SetRec s X f h ≡ f x
RP∞'→SetRecβ {A = A} s = uncurry λ X → uncurry
  λ 2x → PropTrunc.elim (λ _ → isPropΠ3 λ _ _ _ → s _ _)
    λ x f h → RP∞'-fields.elimRP∞' (X , 2x , ∣ x ∣₁) x
      refl
      (h x)


abstract
  notNotRP∞' : ∀ {ℓ} (X : RP∞' ℓ) (x : fst X)
    → RP∞'-fields.notRP∞' X (RP∞'-fields.notRP∞' X x) ≡ x
  notNotRP∞' = JRP∞' refl

RP∞'→GroupoidRec : ∀ {ℓ} {A : Type ℓ} (s : isGroupoid A) (X : RP∞' ℓ)
  → (f : fst X → A)
  → (f-coh : (x : _) → f x ≡ f (RP∞'-fields.notRP∞' X x))
  → (p : (x : fst X)
    → PathP (λ i → f (notNotRP∞' X x (~ i)) ≡ f (RP∞'-fields.notRP∞' X x))
             (f-coh x)
             (sym (f-coh (RP∞'-fields.notRP∞' X x))))
  → A
RP∞'→GroupoidRec {ℓ = ℓ} {A = A} grA = uncurry λ X
  → uncurry λ 2tx
  → elim→Gpd _ (λ _ → isGroupoidΠ3 λ _ _ _ → grA)
      (F1 X 2tx)
      (F2 X 2tx)
      λ x → F3 (X , 2tx , ∣ x ∣₁) x
  where
  F1 : (X : Type) (2tx : is2Type ℓ X) (x : X) (f : X → A)
       (f-coh : (x' : X) → f x' ≡ f (RP∞'-fields.notRP∞' (X , 2tx , ∣ x ∣₁) x')) →
      ((x' : X) →
       PathP (λ i → f (notNotRP∞' (X , 2tx , ∣ x ∣₁) x' (~ i))
                   ≡ f (RP∞'-fields.notRP∞' (X , 2tx , ∣ x ∣₁) x'))
             (f-coh x')
             (sym (f-coh (RP∞'-fields.notRP∞' (X , 2tx , ∣ x ∣₁) x'))))
      → A
  F1 X 2tx x f coh p = f x

  F2 : (X : Type) (2tx : is2Type ℓ X) (x y : X) →
      PathP (λ i →
            (f : X → A)
            (f-coh : (x' : X)
             → f x' ≡ f (RP∞'-fields.notRP∞' (X , 2tx , squash₁ ∣ x ∣₁ ∣ y ∣₁ i) x'))
        → ((x' : X) →
          PathP (λ i₁ →
             f (notNotRP∞' (X , 2tx , squash₁ ∣ x ∣₁ ∣ y ∣₁ i) x' (~ i₁))
           ≡ f (RP∞'-fields.notRP∞' (X , 2tx , squash₁ ∣ x ∣₁ ∣ y ∣₁ i) x'))
          (f-coh x')
          (sym (f-coh (RP∞'-fields.notRP∞' (X , 2tx , squash₁ ∣ x ∣₁ ∣ y ∣₁ i) x')))) → A)
          (F1 X 2tx x)
          (F1 X 2tx y)
  F2 X 2tx x =
    RP∞'-fields.elimRP∞' (X , 2tx , ∣ x ∣₁) x
      (λ i f coh p → f x)
      λ i f coh p → coh x i

  F3 : (X : RP∞' ℓ) (x y z : fst X) →
      SquareP
        (λ i j → (f : fst X → A)
                  (f-coh : (x' : fst X)
                → f x'
                 ≡ f (RP∞'-fields.notRP∞' (fst X , fst (snd X) , squash₁ᵗ x y z i j) x'))
         → ((x' : fst X) →
          PathP
          (λ i₁ →
             f (notNotRP∞' (fst X , fst (snd X) , squash₁ᵗ x y z i j) x' (~ i₁))
           ≡ f (RP∞'-fields.notRP∞' (fst X , fst (snd X) , squash₁ᵗ x y z i j) x'))
          (f-coh x')
          (sym (f-coh (RP∞'-fields.notRP∞' (fst X , fst (snd X) , squash₁ᵗ x y z i j) x')))) → A)
      (F2 (fst X) (fst (snd X)) x y) (F2 (fst X) (fst (snd X)) x z)
      (λ i f f-coh p → f x) (F2 (fst X) (fst (snd X)) y z)
  F3 = JRP∞' (CasesBool true
        (CasesBool true (λ i j f f-coh _ → f true)
                        λ i j f f-coh p → f-coh true (i ∧ j))
        (CasesBool true
          (λ i j f f-coh p
            → hcomp (λ k → λ {(i = i0) → p true (~ k) j
                              ; (i = i1) → f true
                              ; (j = i0) → f (notNotRP∞' (RP∞'∙ ℓ) true (k ∨ i))
                              ; (j = i1) → f-coh false i})
                (hcomp (λ k → λ {(i = i0) → f-coh false (~ j)
                                ; (i = i1) → f true
                                ; (j = i0) → f (isSetBool _ _ refl (notNotRP∞' (RP∞'∙ ℓ) true) k i)
                                ; (j = i1) → f-coh false i})
                       (f-coh false (i ∨ ~ j))))
          λ i j f f-coh p → f-coh true j))

-- understanding mapping spaces (I → J) where I, J : RP∞'
eval⊎≃ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → B ⊎ (A ≃ B) → A → B
eval⊎≃ (inl x) _ = x
eval⊎≃ (inr x) = fst x

eval⊎≃Equiv : ∀ {ℓ} (I J : RP∞' ℓ)
  → (fst J ⊎ (fst I ≃ fst J)) ≃ (fst I → fst J)
eval⊎≃Equiv {ℓ} I J = eval⊎≃ ,
  RP∞'pt→Prop {B = λ I → isEquiv {A = fst J ⊎ (fst I ≃ fst J)} eval⊎≃}
    (λ _ → isPropIsEquiv _)
    (isoToIsEquiv (invIso iso₂)) I
  where
  f₁ : (J : RP∞' ℓ) → Lift (fst J ⊎ (Bool ≃ fst J)) → _
  f₁ J = invEq LiftEquiv

  f₂ : (J : RP∞' ℓ) → fst J × fst J → Lift (fst J ⊎ (Bool ≃ fst J))
  f₂ J = uncurry λ j
   → RP∞'-fields.elimRP∞' J j
       (lift (inl j))
       (lift (inr (invEquiv (isRP∞→≃Bool _ (fst J) (snd J .fst) j))))

  βs : (J : RP∞' ℓ) → (j : fst J) → _
  βs J j = RP∞'-fields.elimRP∞'β J
    {B = λ _ → Lift (fst J ⊎ (Bool ≃ fst J))} j
    (lift (inl j))
    (lift (inr (invEquiv (isRP∞→≃Bool _ (fst J) (snd J .fst) j))))

  inr* : Bool ≃ Bool → Bool ⊎ (Bool ≃ Bool)
  inr* = inr

  iso₁ : Iso (fst J × fst J) (fst J ⊎ (Bool ≃ fst J))
  Iso.fun iso₁ = f₁ J ∘ (f₂ J)
  Iso.inv iso₁ f = Iso.fun ΠBool×Iso (eval⊎≃ f)
  Iso.rightInv iso₁ (inl j) =
    cong (invEq (LiftEquiv {ℓ' = ℓ})) (βs J j .fst)
  Iso.rightInv iso₁ (inr eq) =
    EquivJRP∞' (RP∞'∙ ℓ) {B = λ J eq
      → invEq LiftEquiv (f₂ J (ΠBool→× (fst eq))) ≡ inr eq}
      (cong inr* (Σ≡Prop (λ _ → isPropIsEquiv _)
        (funExt (CasesBool true refl refl)))) J eq
  Iso.leftInv iso₁ =
    uncurry (JRP∞' {B = λ J x → (y : fst J)
                → ΠBool→× (eval⊎≃ (f₁ J (f₂ J (x , y)))) ≡ (x , y)}
      (CasesBool true refl refl) J)

  iso₂ : Iso (Bool → fst J) (fst J ⊎ (Bool ≃ fst J))
  Iso.fun iso₂ = f₁ J ∘ f₂ J ∘ Iso.fun ΠBool×Iso
  Iso.inv iso₂ = eval⊎≃
  Iso.rightInv iso₂ x = Iso.rightInv iso₁ x
  Iso.leftInv iso₂ x =
    (sym (Iso.leftInv ΠBool×Iso (eval⊎≃ (f₁ J (f₂ J (x true , x false)))))
    ∙ cong (Iso.inv ΠBool×Iso) (Iso.leftInv iso₁ (x true , x false)))
    ∙ funExt (CasesBool true refl refl)

-- elimination principle for (I → J)
private
  eval⊎≃Equiv-elim' : ∀ {ℓ ℓ'} {A B : Type ℓ} {C : B → Type ℓ'} (e : A ≃ B)
    → (ind : (a : A) → C (fst e a))
    → (x : _) → subst C (secEq e _) (ind (invEq e (fst e x))) ≡ ind x
  eval⊎≃Equiv-elim' {A = A} {B = B} {C = C} =
    EquivJ (λ A e → (ind : (a : A) → C (fst e a))
      → (x : _) → subst C (secEq e _) (ind (invEq e (fst e x))) ≡ ind x)
      λ ind x → transportRefl (ind x)

module _ {ℓ : Level} {I J : RP∞' ℓ} {A : (fst I → fst J) → Type ℓ}
  (ind : (x : _) → A (fst (eval⊎≃Equiv I J) x)) where
  eval⊎≃Equiv-elim : (x : _) → A x
  eval⊎≃Equiv-elim f =
    subst A (secEq (eval⊎≃Equiv I J) f)
            (ind (invEq (eval⊎≃Equiv I J) f))

  eval⊎≃Equiv-elim-coh : (x : _)
    → eval⊎≃Equiv-elim (fst (eval⊎≃Equiv I J) x) ≡ ind x
  eval⊎≃Equiv-elim-coh =
    eval⊎≃Equiv-elim' {C = A} (eval⊎≃Equiv I J) ind
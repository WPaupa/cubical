module SP.Axiomatic where

open import SP.LEMConnectedness

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.RPn.Base 
open import Cubical.HITs.S1
open import Cubical.HITs.S2
open import Cubical.HITs.Susp

open import Cubical.Homotopy.Connected

open import Cubical.Data.Bool hiding (Bool*)
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Sum
open import Cubical.Data.Sigma


record commf (X Y : Type) : Type₁ where
    field
        f : (Bool → X) → Y
        comstr : (B : 2-EltType₀) → (fst B → X) → Y
        coh : comstr Bool* ≡ f

composeCommf : {X Y Z : Type} → commf X Y → (Y → Z) → commf X Z
composeCommf (record {f = f; comstr = comstr; coh = coh}) g = record { 
        f = λ x → g (f x); 
        comstr = λ B x → g (comstr B x); 
        coh = cong (λ a x → g (a x)) coh 
    }

isSP : Type → Type → Type₁
isSP X SPX = Σ[ f ∈ commf X SPX ] ((T : Type) → (g : commf X T) → ∃![ h ∈ (SPX → T) ] ((x : Bool → X) → h (f .commf.f x) ≡ g .commf.f x))

module _
    {X : Type}
    (bp : X)
    (SPX : Type)
    (SPX=SPX : isSP X SPX) 
    (AC : {A : Type} {B : A → Type} → ((a : A) → ∥ B a ∥₁) → ∥ ((a : A) → B a) ∥₁)
    (LEM : (X : Type) → isProp X → (X ⊎ (X → ⊥))) where

    injSPX : (Bool → X) → SPX
    injSPX = fst SPX=SPX .commf.f

    univSPX : (T : Type) → (g : commf X T) → ∃![ h ∈ (SPX → T) ] ((x : Bool → X) → h (injSPX x) ≡ g .commf.f x)
    univSPX = snd SPX=SPX

    bpSPX : SPX
    bpSPX = injSPX (λ x → bp)
    

    isConnectedSPX : ((x : X) → ∥ x ≡ bp ∥₁) → (x : SPX) → ∥ x ≡ bpSPX ∥₁
    isConnectedSPX connectedX = SP.LEMConnectedness.classicality LEM bpSPX (λ f x → 
        let map : commf X Bool
            map = composeCommf (fst SPX=SPX) f

            univmapStr = univSPX Bool map
            
            univmap : SPX → Bool
            univmap = fst (fst univmapStr)
            
            univmapCoh : (y : Bool → X) → univmap (injSPX y) ≡ map .commf.f y
            univmapCoh = snd (fst univmapStr)
            
            univmapUniv : (g : Σ[ h ∈ (SPX → Bool) ] ((y : Bool → X) → h (injSPX y) ≡ map .commf.f y)) → univmap ≡ g .fst
            univmapUniv g = cong fst (snd univmapStr g)

            univmapEqF : univmap ≡ f
            univmapEqF = univmapUniv (f , λ y → refl)

            mapValue : Bool
            mapValue = map .commf.f (λ x → bp)

            Bool→Xconnected : (x : Bool → X) → ∥ x ≡ (λ x → bp) ∥₁
            Bool→Xconnected x = PT.rec2 isPropPropTrunc (λ xt xf → ∣ funExt (λ b → Cubical.Data.Bool.elim {ℓ-zero} {λ b → x b ≡ bp} xt xf b) ∣₁) (connectedX (x true)) (connectedX (x false))

            mapIsMerelyConstant : (y : Bool → X) → ∥ mapValue ≡ map .commf.f y ∥₁
            mapIsMerelyConstant y = PT.rec isPropPropTrunc (λ path → ∣ cong (λ t → f (fst SPX=SPX .commf.f t)) (sym path) ∣₁) (Bool→Xconnected y)

            trivialMap : SPX → Bool
            trivialMap x = mapValue

            trivialCoh : ∥ ((y : Bool → X) → trivialMap (injSPX y) ≡ map .commf.f y) ∥₁
            trivialCoh = AC mapIsMerelyConstant

            univmapIsMerelyTrivial : ∥ univmap ≡ trivialMap ∥₁
            univmapIsMerelyTrivial = PT.rec isPropPropTrunc (λ pf → ∣ univmapUniv (trivialMap , pf) ∣₁) trivialCoh

            thesis : f x ≡ trivialMap x 
            thesis = PT.rec (isSetBool (f x) (trivialMap x)) (λ path → (funExtS⁻ (sym univmapEqF) x) ∙ (funExtS⁻ path x)) univmapIsMerelyTrivial

            in thesis
        )


unitUniq : (X : Type) → (bp : X) → 
    ((Y : Type) → (f : X → Y) → (x : X) → f x ≡ f bp) → X ≡ Unit
unitUniq X bp eq = ua (isoToEquiv (iso f g sec ret)) where
    f : X → Unit
    f x = tt
    g : Unit → X
    g tt = bp
    sec : (b : Unit) → f (g b) ≡ b
    sec tt = refl

    ret : (x : X) → g (f x) ≡ x
    ret x = sym (eq X (λ x → x) x) 
module SP.Axiomatic where

open import SP.LEMConnectedness
open import SP.ComStr

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetTruncation as ST

open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.EilenbergMacLane.Base

open import Cubical.Algebra.AbGroup.Base

open import Cubical.Data.Bool
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Nat

open import Cubical.Cohomology.EilenbergMacLane.Base

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
            Bool→Xconnected x = PT.map2 (λ xt xf → funExt (λ b → Cubical.Data.Bool.elim {ℓ-zero} {λ b → x b ≡ bp} xt xf b)) (connectedX (x true)) (connectedX (x false))

            mapIsMerelyConstant : (y : Bool → X) → ∥ mapValue ≡ map .commf.f y ∥₁
            mapIsMerelyConstant y = PT.map (λ path → cong (λ t → f (fst SPX=SPX .commf.f t)) (sym path) ) (Bool→Xconnected y)

            trivialMap : SPX → Bool
            trivialMap x = mapValue

            trivialCoh : ∥ ((y : Bool → X) → trivialMap (injSPX y) ≡ map .commf.f y) ∥₁
            trivialCoh = AC mapIsMerelyConstant

            univmapIsMerelyTrivial : ∥ univmap ≡ trivialMap ∥₁
            univmapIsMerelyTrivial = PT.map (λ pf → univmapUniv (trivialMap , pf) ) trivialCoh

            thesis : f x ≡ trivialMap x 
            thesis = PT.rec (isSetBool (f x) (trivialMap x)) (λ path → (funExtS⁻ (sym univmapEqF) x) ∙ (funExtS⁻ path x)) univmapIsMerelyTrivial

            in thesis
        )
    
    inheritsTrivialCohSPX : {G : AbGroup ℓ-zero} → (n : ℕ) → isProp (coHom n G (Bool → X)) → isProp (coHom n G SPX)
    inheritsTrivialCohSPX {G} n cohX cl1 cl2 = ST.elim2 (λ a b → isProp→isSet (isSetSetTrunc a b)) (λ a b → (thesis a) ∙ (sym (thesis b))) cl1 cl2 where

        zeroX : (Bool → X) → EM G n
        zeroX x = 0ₖ n

        zeroSPX : SPX → EM G n
        zeroSPX x = 0ₖ n

        cohTrunc : (f : (Bool → X) → EM G n) → ∥ f ≡ zeroX ∥₁
        cohTrunc f = PathIdTrunc₀Iso .Iso.fun (cohX (∣ f ∣₂) (∣ zeroX ∣₂))
        
        thesis : (f : SPX → EM G n) → ∣ f ∣₂ ≡ ∣ zeroSPX ∣₂
        thesis f = PathIdTrunc₀Iso .Iso.inv fin where
            mapf : commf X (EM G n)
            mapf = composeCommf (fst SPX=SPX) f

            univmapStr = univSPX (EM G n) mapf

            univmap : SPX → EM G n
            univmap = fst (fst univmapStr)

            univmapCoh : (y : Bool → X) → univmap (injSPX y) ≡ mapf .commf.f y
            univmapCoh = snd (fst univmapStr)
            
            univmapUniv : (g : Σ[ h ∈ (SPX → EM G n) ] ((y : Bool → X) → h (injSPX y) ≡ mapf .commf.f y)) → univmap ≡ g .fst
            univmapUniv g = cong fst (snd univmapStr g)

            univmapEqF : univmap ≡ f
            univmapEqF = univmapUniv (f , λ y → refl)

            cohZero : ∥ ((y : Bool → X) → 0ₖ n ≡ mapf .commf.f y) ∥₁
            cohZero = PT.map (λ path y → cong (λ f → f y) (sym path)) (cohTrunc (mapf .commf.f))

            univmapMerelyZero : ∥ univmap ≡ zeroSPX ∥₁
            univmapMerelyZero = PT.map (λ pf → univmapUniv (zeroSPX , pf)) cohZero

            fin : ∥ f ≡ zeroSPX ∥₁
            fin = PT.map (λ path → (sym univmapEqF) ∙ path) univmapMerelyZero 



unitIsSpUnit : {X : Type} → isSP Unit X → X ≡ Unit
unitIsSpUnit {X} (inj , univ) = ua (isoToEquiv (iso f g sec ret)) where
    f : X → Unit
    f x = tt

    g : Unit → X
    g tt = inj .commf.f (λ x → tt)  

    sec : (u : Unit) → f (g u) ≡ u
    sec tt = refl

    univUnit : ∃![ h ∈ (X → X) ] ((x : Bool → Unit) → h (inj .commf.f x) ≡ inj .commf.f x)
    univUnit = univ X inj

    bpX : X
    bpX = g tt

    univmap : X → X
    univmap = fst (fst univUnit)

    univmapUniv : (gf : Σ[ h ∈ (X → X) ] ((y : Bool → Unit) → h (inj .commf.f y) ≡ inj .commf.f y)) → univmap ≡ gf .fst
    univmapUniv gf = cong fst (snd univUnit gf)

    univmapEqId : univmap ≡ (λ x → x)
    univmapEqId = univmapUniv ((λ x → x) , λ y → refl)

    isPropBool→Unit : isProp (Bool → Unit)
    isPropBool→Unit = isProp→ isPropUnit

    constSat : (y : Bool → Unit) → bpX ≡ inj .commf.f y
    constSat y = cong (inj .commf.f) (isPropBool→Unit (λ x → tt) y)

    univmapEqConst : univmap ≡ (λ x → bpX)
    univmapEqConst = univmapUniv ((λ x → bpX) , constSat)

    ret : (x : X) → bpX ≡ x
    ret x = cong (λ f → f x) (sym univmapEqConst ∙ univmapEqId)
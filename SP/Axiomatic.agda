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
private
    variable
        ℓ : Level

isSP : Type ℓ → Type ℓ → Type (ℓ-suc ℓ)
isSP {ℓ} X SPX = Σ[ f ∈ commf X SPX ] ((T : Type ℓ) → (g : commf X T) → ∃![ h ∈ (SPX → T) ] ((x : Bool → X) → h (f .commf.f x) ≡ g .commf.f x))

module _
    {X : Type}
    (bp : X)
    (SPX : Type)
    (SPX=SPX : isSP X SPX) where

    injSPX : (Bool → X) → SPX
    injSPX = fst SPX=SPX .commf.f

    univSPX : (T : Type) → (g : commf X T) → ∃![ h ∈ (SPX → T) ] ((x : Bool → X) → h (injSPX x) ≡ g .commf.f x)
    univSPX = snd SPX=SPX

    bpSPX : SPX
    bpSPX = injSPX (λ x → bp)
    
    module _
        (AC : {A : Type} {B : A → Type} → ((a : A) → ∥ B a ∥₁) → ∥ ((a : A) → B a) ∥₁)
        (LEM : (X : Type) → isProp X → (X ⊎ (X → ⊥))) where
    
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


uniqueSP : {X Y Z : Type} → isSP X Y → isSP X Z → Y ≡ Z
uniqueSP {X} {Y} {Z} (injY , univY) (injZ , univZ) = ua (isoToEquiv (iso f g sec ret)) where
    strF = univY Z injZ
    strG = univZ Y injY
    
    f : Y → Z
    f = strF .fst .fst

    g : Z → Y
    g = strG .fst .fst

    fCoh : (x : Bool → X) → f (injY .commf.f x) ≡ injZ .commf.f x
    fCoh = strF .fst .snd

    gCoh : (x : Bool → X) → g (injZ .commf.f x) ≡ injY .commf.f x
    gCoh = strG .fst .snd

    strIdY = univY Y injY
    strIdZ = univZ Z injZ

    idmapY : Y → Y
    idmapY = strIdY .fst .fst

    idmapZ : Z → Z
    idmapZ = strIdZ .fst .fst

    idmapYUniv : (hs : Σ[ h ∈ (Y → Y) ] ((y : Bool → X) → h (injY .commf.f y) ≡ injY .commf.f y)) → idmapY ≡ hs .fst
    idmapYUniv hs = cong fst (snd strIdY hs)

    idmapZUniv : (hs : Σ[ h ∈ (Z → Z) ] ((y : Bool → X) → h (injZ .commf.f y) ≡ injZ .commf.f y)) → idmapZ ≡ hs .fst
    idmapZUniv hs = cong fst (snd strIdZ hs)

    idmapYIsId : idmapY ≡ (λ x → x)
    idmapYIsId = idmapYUniv ((λ x → x) , (λ x → refl))

    idmapZIsId : idmapZ ≡ (λ x → x)
    idmapZIsId = idmapZUniv ((λ x → x) , (λ x → refl))

    g∘fCoh : idmapY ≡ (λ x → g (f x))
    g∘fCoh = idmapYUniv ((λ x → g (f x)) , (λ x → (cong g (fCoh x)) ∙ gCoh x))

    f∘gCoh : idmapZ ≡ (λ x → f (g x))
    f∘gCoh = idmapZUniv ((λ x → f (g x)) , (λ x → (cong f (gCoh x)) ∙ fCoh x))

    g∘fIsId : (λ x → g (f x)) ≡ (λ x → x)
    g∘fIsId = (sym g∘fCoh) ∙ idmapYIsId

    f∘gIsId : (λ x → f (g x)) ≡ (λ x → x)
    f∘gIsId = (sym f∘gCoh) ∙ idmapZIsId

    sec : (z : Z) → f (g z) ≡ z
    sec z = cong (λ h → h z) f∘gIsId

    ret : (y : Y) → g (f y) ≡ y
    ret y = cong (λ h → h y) g∘fIsId

module operations
    {X Y : Type}
    (bpX : X)
    (bpY : Y)
    (SPX : Type)
    (SPY : Type)
    (isSPX : isSP X SPX)
    (isSPY : isSP Y SPY) where

    functorSP : (X → Y) → SPX → SPY
    functorSP f = 
        snd isSPX SPY (precomposeCommf f (fst isSPY)) .fst .fst

{-
    sumSP : isSP (X ⊎ Y) ((X × Y) ⊎ (SPX ⊎ SPY))
    sumSP = {!!} where
        injSum : (X ⊎ Y) → (X ⊎ Y) → ((X × Y) ⊎ (SPX ⊎ SPY))
        injSum (inl x) (inr x') = inr (inl (fst isSPX (Cubical.Data.Bool.elim x x')))

        injSumCommf : commf (X ⊎ Y) ((X × Y) ⊎ (SPX ⊎ SPY))
        injSumCommf = record {
                f = {!!};
                comstr = {!!};
                coh = {!!}
            }
-}

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
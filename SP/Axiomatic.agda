module SP.Axiomatic where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.GroupPath
open import Cubical.Algebra.Group.Instances.Int
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Unit
open import Cubical.ZCohomology.GroupStructure
open import Cubical.ZCohomology.Groups.Connected

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.Truncation as T

open import Cubical.HITs.RPn.Base 
open import Cubical.HITs.S1
open import Cubical.HITs.S2
open import Cubical.HITs.Susp

open import Cubical.Homotopy.Connected

open import Cubical.Data.Bool hiding (Bool*)
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Sigma


record commf (X Y : Type₀) : Type₁ where
    field
        f : (Bool → X) → Y
        comstr : (B : 2-EltType₀) → (fst B → X) → Y
        coh : comstr Bool* ≡ f

composeCommf : {X Y Z : Type₀} → commf X Y → (Y → Z) → commf X Z
composeCommf (record {f = f; comstr = comstr; coh = coh}) g = record { 
        f = λ x → g (f x); 
        comstr = λ B x → g (comstr B x); 
        coh = cong (λ a x → g (a x)) coh 
    }

isSP : Type₀ → Type₀ → Type₁
isSP X SPX = Σ[ f ∈ commf X SPX ] ((T : Type₀) → (g : commf X T) → ∃![ h ∈ (SPX → T) ] ((x : Bool → X) → h (f .commf.f x) ≡ g .commf.f x))

postulate
    CP² : Type₀
    CP²=SPS² : isSP S² CP²

makef : {X : Type₀} → X → X → Bool → X
makef a b true = a
makef a b false = b

injCP² : (Bool → S²) → CP²
injCP² = fst CP²=SPS² .commf.f

univCP² : (T : Type₀) → (g : commf S² T) → ∃![ h ∈ (CP² → T) ] ((x : Bool → S²) → h (injCP² x) ≡ g .commf.f x)
univCP² = snd CP²=SPS²

baseCP² : CP²
baseCP² = injCP² (λ x → base)

isConnectedF : {X : Type₀} → {bp : X} → ((f : X → Bool) → (x : X) → ∥ f x ≡ f bp ∥₁) → (x : X) → ∥ bp ≡ x ∥₁
isConnectedF {X} {bp} feq x = ∣ {!!} ∣₁
 

isConnectedCP² : (x : CP²) → ∥ baseCP² ≡ x ∥₁
isConnectedCP² = isConnectedF (λ f x → 
    let map : commf S² Bool
        map = composeCommf (fst CP²=SPS²) f

        univmapStr = univCP² Bool map
        
        univmap : CP² → Bool
        univmap = fst (fst univmapStr)
        
        univmapCoh : (y : Bool → S²) → univmap (injCP² y) ≡ map .commf.f y
        univmapCoh = snd (fst univmapStr)
        
        univmapUniv : (g : Σ[ h ∈ (CP² → Bool) ] ((y : Bool → S²) → h (injCP² y) ≡ map .commf.f y)) → univmap ≡ g .fst
        univmapUniv g = cong fst (snd univmapStr g)

        univmapEqF : univmap ≡ f
        univmapEqF = univmapUniv (f , λ y → refl)

        mapValue : Bool
        mapValue = map .commf.f (λ x → base)

        Bool→S²connected : (x y : Bool → S²) → ∥ x ≡ y ∥₁
        Bool→S²connected x y = 
            let consp : isContr (hLevelTrunc 2 (Susp (Susp (Susp ⊥))))
                consp = isConnectedSubtr 2 1 (isConnectedSphere 3)
                
                susp³⊥≡S² : S² ≡ Susp (Susp (Susp ⊥))
                susp³⊥≡S² = 
                        S²
                    ≡⟨ S²≡SuspS¹ ⟩
                        Susp S¹
                    ≡⟨ cong Susp (S¹≡SuspBool) ⟩
                        Susp (Susp Bool)
                    ≡⟨ cong (λ x → Susp (Susp x)) (ua Bool≃Susp⊥) ⟩
                        Susp (Susp (Susp ⊥)) ∎
            
            in {!!}

        mapIsMerelyConstant : (y : Bool → S²) → ∥ mapValue ≡ map .commf.f y ∥₁
        mapIsMerelyConstant y = PT.rec isPropPropTrunc (λ path → ∣ cong (λ t → f (fst CP²=SPS² .commf.f t)) (sym path) ∣₁) (Bool→S²connected y (λ x → base))

        trivialMap : CP² → Bool
        trivialMap x = mapValue

        trivialCoh : ∥ ((y : Bool → S²) → trivialMap (injCP² y) ≡ map .commf.f y) ∥₁
        trivialCoh = {!!}

        univmapIsMerelyTrivial : ∥ univmap ≡ trivialMap ∥₁
        univmapIsMerelyTrivial = {!!}

        thesis : ∥ f x ≡ trivialMap x ∥₁ 
        thesis = PT.rec isPropPropTrunc (λ path → ∣ (funExtS⁻ (sym univmapEqF) x) ∙ (funExtS⁻ path x) ∣₁) univmapIsMerelyTrivial

        in thesis
    )

H⁰CP²≃ℤ : GroupIso (coHomGr 0 CP²) ℤGroup
H⁰CP²≃ℤ = H⁰-connected baseCP² isConnectedCP²


{-
data CommStrSP (X : Type₀) : Type₁ where
    cons : (Bool → X) → CommStrSP X
    comm_c : (Y : 2-EltType₀) → (fst Y → X) → CommStrSP X
    comm_e : comm_c Bool*  ≡ cons 

data CommSPSimp (X : Type₀) : Type₁ where
    comms_c : (Y : 2-EltType₀) → (fst Y → X) → CommSPSimp X

commEquiv : {X : Type₀} → CommStrSP X ≡ CommSPSimp X
commEquiv = isoToPath (iso f g eq1 eq2) where
    f : CommStrSP X → CommSPSimp X
    f (cons x) = comms_c Bool* x
    f (comm_c Y x) = comms_c Y x
    f (comm_e i x) = {!   !}

    g : CommSPSimp X → CommStrSP X
    g = {!!}

    eq1 : section f g
    eq1 = {!!}

    eq2 : retract f g
    eq2 = {!!}

commWorks : CommStrSP One ≡ One₁
commWorks = isoToPath (iso f g eq1 eq2) where
    f : CommStrSP One → One₁
    f (cons x) = {!   !}
    f (comm Y c x) = {!   !}
    f (comm i e x) = {!   !}

    g : One₁ → CommStrSP One
    g = {!!}

    eq1 : section f g
    eq1 = {!!}

    eq2 : retract f g
    eq2 = {!!}
-}
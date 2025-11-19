module SP.ComStr where

open import Cubical.Foundations.Prelude

open import SP.RPn -- RPn by Axel Ljungstrom & David Warn
--open import Cubical.HITs.RPn.Base
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (Bool*) renaming (elim to makepair)

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

precomposeCommf : {X Y Z : Type} → (X → Y) → commf Y Z → commf X Z
precomposeCommf f (record {f = g; comstr = comstr; coh = coh}) = record {
        f = λ x → g (λ b → f (x b));
        comstr = λ B x → comstr B (λ b → f (x b));
        coh = cong (λ a x → a (λ b → f (x b))) coh
    }

constantIsCommutative : {X Y : Type} → (y : Y) → (f : (Bool → X) → Y) → ((x : Bool → X) → f x ≡ y) → commf X Y
constantIsCommutative {X} {Y} y f const = record {
        f = f;
        comstr = λ B x → y;
        coh = sym (funExt const)
    }

commutativityStr : {X Y : Type} → (comstr : (B : 2-EltType₀) → (fst B → X) → Y) → (a b : X) →
    comstr Bool* (makepair b a) ≡ comstr Bool* (makepair a b)
commutativityStr {X} {Y} comstr a b = cong (comstr Bool*) (sym casesFalseFun) ∙ mainLemma where
    casesTrue : (CasesRP Bool* {A = λ _ → X} true a b true ≡ a) × (CasesRP Bool* {A = λ _ → X} true a b false ≡ b)
    casesTrue = CasesRPβ {ℓ-zero} Bool* {A = λ _ → X} true a b

    casesTrueFun : CasesRP Bool* {A = λ _ → X} true a b ≡ makepair a b
    casesTrueFun = funExt casesTrueBool where
        casesTrueBool : (t : Bool) → CasesRP Bool* {A = λ _ → X} true a b t ≡ makepair a b t
        casesTrueBool true = fst casesTrue
        casesTrueBool false = snd casesTrue
    
    casesFalse : (CasesRP Bool* {A = λ _ → X} false a b false ≡ a) × (CasesRP Bool* {A = λ _ → X} false a b true ≡ b)
    casesFalse = CasesRPβ {ℓ-zero} Bool* {A = λ _ → X} false a b

    casesFalseFun : CasesRP Bool* {A = λ _ → X} false a b ≡ makepair b a
    casesFalseFun = funExt casesFalseBool where
        casesFalseBool : (t : Bool) → CasesRP Bool* {A = λ _ → X} false a b t ≡ makepair b a t
        casesFalseBool false = fst casesFalse
        casesFalseBool true = snd casesFalse

    mainLemma :
        comstr Bool* (CasesRP Bool* false a b) ≡ comstr Bool* (makepair a b)
    mainLemma = JRP∞ (λ B t → comstr B (CasesRP B t a b) ≡ comstr Bool* (makepair a b)) 
        (cong (comstr Bool*) casesTrueFun) {Bool*} {false}

commfCommutative : {X Y : Type} → (f : commf X Y) → (a b : X) → 
    f .commf.f (makepair a b) ≡ f .commf.f (makepair b a)
commfCommutative {X} {Y} f a b = 
    cong (λ F → F (makepair a b)) (sym (f .commf.coh)) ∙ 
    sym (commutativityStr (f .commf.comstr) a b) ∙ 
    cong (λ F → F (makepair b a)) (f .commf.coh)
{-# OPTIONS --allow-unsolved-metas #-}
module defs where

open import Data.Nat
open import Data.List
open import Data.Sum
open import Data.Product
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

------------------------------------
-- Unification terms ---------------
------------------------------------
Var      = ℕ
Atom     = ℕ
Scope    = List Atom
data Term : Set where
  var  : Var → Term
  fapp : Term → Term → Term
  atom : Atom → Term
  bind : Atom → Term → Term
Closure  = Scope × Term
AClosure = Scope × Atom
VClosure = Scope × Var
record Eqn : Set where
  constructor _=α_
  field
    lhs : Closure
    rhs : Closure
record VEqn : Set where
  constructor _=α_
  field
    lhs : VClosure
    rhs : VClosure
data _∈_ : ∀ {A : Set} → A → List A → Set where
  base : ∀ {A} {a : A} {l}
         → a ∈ (a ∷ l)
  step : ∀ {A} {a a' : A} {l}
         → a ∈ l
         → a ∈ (a' ∷ l)

------------------------------------
-- Free and bound ------------------
------------------------------------
data _∉_ : Atom → Scope → Set where
  base : ∀ {a}
         → a ∉ []
  step : ∀ {ϕ a a'}
         → ¬ a ≡ a' → a ∉ ϕ
         → a ∉ (a' ∷ ϕ)
data dB : Scope → Atom → ℕ → Set where
  base : ∀ {a a' ϕ}
         → a ≡ a'
         → dB (a' ∷ ϕ) a (length ϕ)
  step : ∀ {a a' ℓ ϕ}
         → ¬ a ≡ a' → dB ϕ a ℓ
         → dB (a' ∷ ϕ) a ℓ
bound? : (ϕ : Scope) → (a : Atom) → (a ∉ ϕ) ⊎ Σ ℕ (λ ℓ → dB ϕ a ℓ)
bound? [] a = inj₁ base
bound? (a' ∷ ϕ) a with a ≟ a'
bound? (a' ∷ ϕ) a | yes p = inj₂ (length ϕ , base p)
bound? (a' ∷ ϕ) a | no ¬p with bound? ϕ a
bound? (a' ∷ ϕ) a | no ¬p | inj₁ f = inj₁ (step ¬p f)
bound? (a' ∷ ϕ) a | no ¬p | inj₂ (ℓ , b) = inj₂ (ℓ , step ¬p b)

------------------------------------
-- α-equivalence -------------------
------------------------------------
data _≈α_ : AClosure → AClosure → Set where
  free  : ∀ {a ϕ₁ ϕ₂} {same_len : (length ϕ₁) ≡ (length ϕ₂)}
          → a ∉ ϕ₁ → a ∉ ϕ₂
          → (ϕ₁ , a) ≈α (ϕ₂ , a)
  bound : ∀ {a₁ a₂ ϕ₁ ϕ₂ ℓ} {same_len : (length ϕ₁) ≡ (length ϕ₂)}
          → dB ϕ₁ a₁ ℓ → dB ϕ₂ a₂ ℓ
          → (ϕ₁ , a₁) ≈α (ϕ₂ , a₂)
data _⊢_=α_ : List VEqn → Closure → Closure → Set where
  var : ∀ {x₁ x₂ ϕ₁ ϕ₂ γ}
        → ((ϕ₁ , x₁) =α (ϕ₂ , x₂)) ∈ γ
        → γ ⊢ (ϕ₁ , var x₁) =α (ϕ₂ , var x₂)
  vext : ∀ {x₁ ϕ₁ x₂ ϕ₂ γ a}
          → γ ⊢ (ϕ₁ , var x₁) =α (ϕ₂ , var x₂)
          → γ ⊢ (ϕ₁ ++ (a ∷ []), var x₁) =α (ϕ₂ ++ (a ∷ []), var x₂)
  vrefl : ∀ {x ϕ γ}
          → γ ⊢ (ϕ , var x) =α (ϕ , var x)
  vsymm : ∀ {x₁ x₂ ϕ₁ ϕ₂ γ}
          → γ ⊢ (ϕ₂ , var x₂) =α (ϕ₁ , var x₁)
          → γ ⊢ (ϕ₁ , var x₁) =α (ϕ₂ , var x₂)
  vtran : ∀ {x₁ x₂ x' ϕ₁ ϕ₂ ϕ' γ}
          → γ ⊢ (ϕ₁ , var x₁) =α (ϕ' , var x')
          → γ ⊢ (ϕ' , var x') =α (ϕ₂ , var x₂)
          → γ ⊢ (ϕ₁ , var x₁) =α (ϕ₂ , var x₂)
  atom : ∀ {a₁ a₂ ϕ₁ ϕ₂ γ}
         → (ϕ₁ , a₁) ≈α (ϕ₂ , a₂)
         → γ ⊢ (ϕ₁ , atom a₁) =α (ϕ₂ , atom a₂)
  bind : ∀ {a₁ a₂ t₁ t₂ ϕ₁ ϕ₂ γ}
         → γ ⊢ (a₁ ∷ ϕ₁ , t₁) =α (a₂ ∷ ϕ₂ , t₂)
         → γ ⊢ (ϕ₁ , bind a₁ t₁) =α (ϕ₂ , bind a₂ t₂)
  fapp : ∀ {t₁ t₂ t₁' t₂' ϕ₁ ϕ₂ γ}
         → γ ⊢ (ϕ₁ , t₁) =α (ϕ₂ , t₁')
         → γ ⊢ (ϕ₁ , t₂) =α (ϕ₂ , t₂')
         → γ ⊢ (ϕ₁ , fapp t₁ t₂) =α (ϕ₂ , fapp t₁' t₂')

lemma₁ : ∀ {a a' l} → a ∉ l → ¬ a ≡ a' → a ∉ (l ++ a' ∷ [])
lemma₁ {l = []} base p2 = step p2 base
lemma₁ {l = x ∷ l} (step neq p1) p2 = step neq (lemma₁ p1 p2)

lemma₂ : ∀ {a a' l} → a ∉ l → a ≡ a' → dB (l ++ a' ∷ []) a 0
lemma₂ {l = []} p1 p2 = base p2
lemma₂ {l = x ∷ l} (step x₁ p1) p2 = step x₁ (lemma₂ p1 p2)

le : ∀ {A : Set} {a : A} {l : List A} → length (l ++ a ∷ []) ≡ suc (length l)
le {l = []} = refl
le {a = a} {l = x ∷ l} = cong suc (le {a = a}{l = l})

lemma₃ : ∀ {a a' l ℓ} → dB l a ℓ → dB (l ++ a' ∷ []) a (suc ℓ)
lemma₃ {l = x ∷ []} (base eq) = base eq
lemma₃ {a = a} {a' = a'} {l = x ∷ l@(_ ∷ _)} p@(base refl) = subst (λ ℓ → dB ((x ∷ l) ++ a' ∷ []) x ℓ) (le {a = a'} {l = l}) (base {a = a}{ϕ = l ++ a' ∷ []} refl)
lemma₃ {a' = a'} {l = x ∷ x₁ ∷ l} (step neq p) = step neq (lemma₃ {a' = a'} p)

ext : ∀ {t₁ t₂ ϕ₁ ϕ₂ γ a}
      → γ ⊢ (ϕ₁ , t₁) =α (ϕ₂ , t₂)
      → γ ⊢ (ϕ₁ ++ (a ∷ []) , t₁) =α (ϕ₂ ++ (a ∷ []) , t₂)
ext (var x) = vext (var x)
ext (vext p) = vext (ext p)
ext vrefl = vrefl
ext (vsymm p) = vsymm (ext p)
ext (vtran p₁ p₂) = vtran (ext p₁) (ext p₂)
ext {a = a'} (atom {a₁ = a} (free f₁ f₂)) with a ≟ a'
ext {a = a'} (atom {a} (free {ϕ₁ = ϕ₁} {ϕ₂ = ϕ₂} {same_len = same_len} f₁ f₂)) | yes eq = atom (bound {same_len = subst₂ (λ h₁ h₂ → h₁ ≡ h₂) (sym (le {a = a'} {l = ϕ₁})) (sym (le {a = a'} {l = ϕ₂})) (cong suc same_len)} (lemma₂ f₁ eq) (lemma₂ f₂ eq))
ext {a = a'} (atom {a} (free {ϕ₁ = ϕ₁} {ϕ₂ = ϕ₂} {same_len = same_len} f₁ f₂)) | no ¬p = atom (free {same_len = subst₂ (λ h₁ h₂ → h₁ ≡ h₂) (sym (le {a = a'} {l = ϕ₁})) (sym (le {a = a'} {l = ϕ₂})) (cong suc same_len)} (lemma₁ f₁ ¬p) (lemma₁ f₂ ¬p))
ext {a = a'} (atom (bound {ϕ₁ = ϕ₁} {ϕ₂ = ϕ₂} {same_len = same_len} b₁ b₂)) = atom (bound {same_len = subst₂ (λ h₁ h₂ → h₁ ≡ h₂) (sym (le {a = a'} {l = ϕ₁})) (sym (le {a = a'} {l = ϕ₂})) (cong suc same_len)} (lemma₃ b₁) (lemma₃ b₂))
ext (bind p) = bind (ext p)
ext (fapp p₁ p₂) = fapp (ext p₁) (ext p₂)

αtran : ∀ {ϕ₁ ϕ₂ t₁ t₂ ϕ' t' γ}
        → γ ⊢ (ϕ₁ , t₁) =α (ϕ' , t')
        → γ ⊢ (ϕ' , t') =α (ϕ₂ , t₂)
        → γ ⊢ (ϕ₁ , t₁) =α (ϕ₂ , t₂)
αtran (var x) (var x₁) = vtran (var x) (var x₁)
αtran (var x) (vext p2) = vtran (var x) (vext p2)
αtran (var x) vrefl = var x
αtran (var x) (vsymm p2) = vtran (var x) (vsymm p2)
αtran (var x) (vtran p2 p3) = vtran (αtran (var x) p2) p3
αtran p1@(vext _) p2 = {!!}
αtran vrefl (var x) = var x
αtran vrefl (vext p2) = vext p2
αtran vrefl vrefl = vrefl
αtran vrefl (vsymm p2) = vsymm p2
αtran vrefl (vtran p2 p3) = αtran p2 p3
αtran (vsymm p1) (var x) = vtran (vsymm p1) (var x)
αtran (vsymm p1) (vext p2) = vtran (vsymm p1) (vext p2)
αtran (vsymm p1) vrefl = vsymm p1
αtran (vsymm p1) (vsymm p2) = vsymm (αtran p2 p1)
αtran (vsymm p1) (vtran p2 p3) = vtran (αtran (vsymm p1) p2) p3
αtran (vtran p1 p3) (var x) = vtran (αtran p1 p3) (var x)
αtran (vtran p1 p3) (vext p2) = vtran (αtran p1 p3) (vext p2)
αtran (vtran p1 p3) vrefl = αtran p1 p3
αtran (vtran p1 p3) (vsymm p2) = vtran (αtran p1 p3) (vsymm p2)
αtran (vtran p1 p3) (vtran p2 p4) = vtran (αtran p1 p3) (αtran p2 p4)
αtran (atom (free x x₁)) (atom (free x₂ x₃)) = {!!}
αtran (atom (free x x₁)) (atom (bound x₂ x₃)) = {!!}
αtran (atom (bound x x₁)) (atom (free x₂ x₃)) = {!!}
αtran (atom (bound x x₁)) (atom (bound x₂ x₃)) = {!!}
αtran (bind p1) (bind p2) = bind (αtran p1 p2)
αtran (fapp p1 p3) (fapp p2 p4) = fapp (αtran p1 p2) (αtran p3 p4)

αsymm : ∀ {ϕ₁ ϕ₂ t₁ t₂ γ}
        → γ ⊢ (ϕ₁ , t₁) =α (ϕ₂ , t₂)
        → γ ⊢ (ϕ₂ , t₂) =α (ϕ₁ , t₁)
αsymm (var x) = vsymm (var x)
αsymm (vext p) = vext (αsymm p)
αsymm vrefl = vrefl
αsymm (vsymm p) = p
αsymm (vtran p p₁) = vtran (αsymm p₁) (αsymm p)
αsymm (atom (free {same_len = same_len} x x₁)) = atom (free {same_len = sym same_len} x₁ x)
αsymm (atom (bound {same_len = same_len} x x₁)) = atom (bound {same_len = sym same_len} x₁ x)
αsymm (bind p) = bind (αsymm p)
αsymm (fapp p p₁) = fapp (αsymm p) (αsymm p₁)

αrefl : ∀ {ϕ t γ}
        → γ ⊢ (ϕ , t) =α (ϕ , t)
αrefl {t = var x} = vrefl
αrefl {t = fapp t t₁} = fapp αrefl αrefl
αrefl {ϕ = ϕ} {t = atom x} with bound? ϕ x
αrefl {ϕ} {atom x} | inj₁ x₁ = atom (free {same_len = refl} x₁ x₁)
αrefl {ϕ} {atom x} | inj₂ (_ , b) = atom (bound {same_len = refl} b b)
αrefl {t = bind x t} = bind αrefl

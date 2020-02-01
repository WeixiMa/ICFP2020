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
  free  : ∀ {a ϕ₁ ϕ₂}
          → a ∉ ϕ₁ → a ∉ ϕ₂
          → (ϕ₁ , a) ≈α (ϕ₂ , a)
  bound : ∀ {a₁ a₂ ϕ₁ ϕ₂ ℓ}
          → dB ϕ₁ a₁ ℓ → dB ϕ₂ a₂ ℓ
          → (ϕ₁ , a₁) ≈α (ϕ₂ , a₂)
data _⊢_=α_ : List VEqn → Closure → Closure → Set where
  var : ∀ {x₁ x₂ ϕ₁ ϕ₂ γ}
        → ((ϕ₁ , x₁) =α (ϕ₂ , x₂)) ∈ γ
        → γ ⊢ (ϕ₁ , var x₁) =α (ϕ₂ , var x₂)
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
  ext  : ∀ {t₁ t₂ ϕ₁ ϕ₂ γ a}
         → γ ⊢ (ϕ₁ , t₁) =α (ϕ₂ , t₂)
         → γ ⊢ (a ∷ ϕ₁ , t₁) =α (a ∷ ϕ₂ , t₂)


αtran : ∀ {ϕ₁ ϕ₂ t₁ t₂ ϕ' t' γ}
        → γ ⊢ (ϕ₁ , t₁) =α (ϕ' , t')
        → γ ⊢ (ϕ' , t') =α (ϕ₂ , t₂)
        → γ ⊢ (ϕ₁ , t₁) =α (ϕ₂ , t₂)
αtran (var x) (var x₁) = vtran (var x) (var x₁)
αtran (var x) vrefl = var x
αtran (var x) (vsymm p2) = vtran (var x) (vsymm p2)
αtran (var x) (vtran p2 p3) = vtran (αtran (var x) p2) p3
αtran p1@(var x) (ext p2) = {!!}
αtran vrefl (var x) = var x
αtran vrefl vrefl = vrefl
αtran vrefl (vsymm p2) = vsymm p2
αtran vrefl (vtran p2 p3) = αtran p2 p3
αtran vrefl (ext p2) = ext p2
αtran (vsymm p1) (var x) = vtran (vsymm p1) (var x)
αtran (vsymm p1) vrefl = vsymm p1
αtran (vsymm p1) (vsymm p2) = vsymm (αtran p2 p1)
αtran (vsymm p1) (vtran p2 p3) = vtran (αtran (vsymm p1) p2) p3
αtran (vsymm p1) (ext p2) = {!!}
αtran (vtran p1 p2) (var x) = vtran (αtran p1 p2) (var x)
αtran (vtran p1 p2) vrefl = αtran p1 p2
αtran (vtran p1 p2) (vsymm p3) = vtran (αtran p1 p2) (vsymm p3)
αtran (vtran p1 p2) (vtran p3 p4) = vtran (αtran p1 p2) (αtran p3 p4)
αtran (vtran p1 p2) (ext p3) = {!!}
αtran (atom x) (atom x₁) = {!!}
αtran (atom x) (ext p2) = {!!}
αtran (bind p1) (bind p2) = bind (αtran p1 p2)
αtran (bind p1) (ext p2) = {!!}
αtran (fapp p1 p2) (fapp p3 p4) = fapp (αtran p1 p3) (αtran p2 p4)
αtran (fapp p1 p2) (ext p3) = {!!}
αtran (ext p1) (var x) = {!!}
αtran (ext p1) vrefl = ext p1
αtran (ext p1) (vsymm p2) = {!!}
αtran (ext p1) (vtran p2 p3) = {!!}
αtran (ext p1) (atom x) = {!!}
αtran (ext p1) (bind p2) = {!!}
αtran (ext p1) (fapp p2 p3) = {!!}
αtran (ext p1) (ext p2) = {!!}

αsymm : ∀ {ϕ₁ ϕ₂ t₁ t₂ γ}
        → γ ⊢ (ϕ₁ , t₁) =α (ϕ₂ , t₂)
        → γ ⊢ (ϕ₂ , t₂) =α (ϕ₁ , t₁)
αsymm (var x) = vsymm (var x)
αsymm vrefl = vrefl
αsymm (vsymm p) = p
αsymm (vtran p p₁) = vtran (αsymm p₁) (αsymm p)
αsymm (atom (free x x₁)) = atom (free x₁ x)
αsymm (atom (bound x x₁)) = atom (bound x₁ x)
αsymm (bind p) = bind (αsymm p)
αsymm (fapp p p₁) = fapp (αsymm p) (αsymm p₁)
αsymm (ext p) = ext (αsymm p)

αrefl : ∀ {ϕ t γ}
        → γ ⊢ (ϕ , t) =α (ϕ , t)
αrefl {t = var x} = vrefl
αrefl {t = fapp t t₁} = fapp αrefl αrefl
αrefl {ϕ} {t = atom x} with bound? ϕ x
αrefl {ϕ} {atom x} | inj₁ f = atom (free f f)
αrefl {ϕ} {atom x} | inj₂ (_ , b) = atom (bound b b)
αrefl {t = bind x t} = bind αrefl


module defs where

open import Data.Nat
open import Data.List
open import Data.Sum
open import Data.Product
open import Data.Empty
open import Relation.Nullary hiding (¬_)
open import Relation.Binary.PropositionalEquality
open import refutation

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
bound? (a' ∷ ϕ) a | no ¬p | inj₁ f = inj₁ (step (neg→neg ¬p) f)
bound? (a' ∷ ϕ) a | no ¬p | inj₂ (ℓ , b) = inj₂ (ℓ , step (neg→neg ¬p) b)

unique-free : ∀ {ϕ a} → (x : a ∉ ϕ) → (y : a ∉ ϕ) → x ≡ y
unique-free base base = refl
unique-free (step neq₁ p₁) (step neq₂ p₂) with unique-free p₁ p₂ | refutations-unique neq₁ neq₂
unique-free (step neq₁ p₁) (step .neq₁ .p₁) | refl | refl = refl

unique-bound : ∀ {ϕ a ℓ ℓ'} → (x : dB ϕ a ℓ) → (y : dB ϕ a ℓ')
               → Σ (ℓ ≡ ℓ') (λ eq → (subst (λ ℓ → dB ϕ a ℓ) eq x) ≡ y)
unique-bound (base refl) (base refl) = refl , refl
unique-bound (base eq) (step neq _) = refutation-elim (neq eq)
unique-bound (step neq _) (base eq) = refutation-elim (neq eq)
unique-bound (step neq₁ b₁) (step neq₂ b₂) with refutations-unique neq₁ neq₂ | unique-bound b₁ b₂
unique-bound (step neq₁ b₁) (step .neq₁ .b₁) | refl | refl , refl = refl , refl

free-bound-dec : ∀ {ϕ a ℓ} → dB ϕ a ℓ → a ∉ ϕ → ⊥
free-bound-dec {[]} () f
free-bound-dec {a ∷ ϕ} (base eq) (step neq _) = refutation-elim (neq eq)
free-bound-dec {a ∷ ϕ} (step neq b) (step neq f) = free-bound-dec b f
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

αtran : ∀ {ϕ₁ ϕ₂ t₁ t₂ ϕ' t' γ}
        → γ ⊢ (ϕ₁ , t₁) =α (ϕ' , t')
        → γ ⊢ (ϕ' , t') =α (ϕ₂ , t₂)
        → γ ⊢ (ϕ₁ , t₁) =α (ϕ₂ , t₂)
αtran (var x) (var x₁) = vtran (var x) (var x₁)
αtran (var x) vrefl = var x
αtran (var x) (vsymm p2) = vtran (var x) (vsymm p2)
αtran (var x) (vtran p2 p3) = vtran (αtran (var x) p2) p3
αtran vrefl (var x) = var x
αtran vrefl vrefl = vrefl
αtran vrefl (vsymm p2) = vsymm p2
αtran vrefl (vtran p2 p3) = αtran p2 p3
αtran (vsymm p1) (var x) = vtran (vsymm p1) (var x)
αtran (vsymm p1) vrefl = vsymm p1
αtran (vsymm p1) (vsymm p2) = vsymm (αtran p2 p1)
αtran (vsymm p1) (vtran p2 p3) = vtran (αtran (vsymm p1) p2) p3
αtran (vtran p1 p3) (var x) = vtran (αtran p1 p3) (var x)
αtran (vtran p1 p3) vrefl = αtran p1 p3
αtran (vtran p1 p3) (vsymm p2) = vtran (αtran p1 p3) (vsymm p2)
αtran (vtran p1 p3) (vtran p2 p4) = vtran (αtran p1 p3) (αtran p2 p4)
αtran (atom (free f₁ f₂)) (atom (free f₃ f₄)) with unique-free f₂ f₃
αtran (atom (free {same_len = same_len₁} f₁ f₂)) (atom (free {same_len = same_len₂} .f₂ f₄)) | refl = atom (free {same_len = trans same_len₁ same_len₂} f₁ f₄)
αtran (atom (free _ f)) (atom (bound b _)) = ⊥-elim (free-bound-dec b f)
αtran (atom (bound _ b)) (atom (free f _)) = ⊥-elim (free-bound-dec b f)
αtran (atom (bound b₁ b₂)) (atom (bound b₃ b₄)) with unique-bound b₂ b₃
αtran (atom (bound {same_len = same_len₁} b₁ b₂)) (atom (bound {same_len = same_len₂} .b₂ b₄)) | refl , refl = atom (bound {same_len = trans same_len₁ same_len₂} b₁ b₄)
αtran (bind p1) (bind p2) = bind (αtran p1 p2)
αtran (fapp p1 p3) (fapp p2 p4) = fapp (αtran p1 p2) (αtran p3 p4)

αsymm : ∀ {ϕ₁ ϕ₂ t₁ t₂ γ}
        → γ ⊢ (ϕ₁ , t₁) =α (ϕ₂ , t₂)
        → γ ⊢ (ϕ₂ , t₂) =α (ϕ₁ , t₁)
αsymm (var x) = vsymm (var x)
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

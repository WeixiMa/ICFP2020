open import Data.Nat
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Data.List
open import Data.Empty
open import Relation.Nullary  hiding (¬_)
open import Relation.Binary.PropositionalEquality
open import refutation
open import defs

module algoA
  (vext : ∀ {x₁ ϕ₁ x₂ ϕ₂ γ a}
          → γ ⊢ (ϕ₁ , var x₁) =α (ϕ₂ , var x₂)
          → γ ⊢ (ϕ₁ ++ (a ∷ []), var x₁) =α (ϕ₂ ++ (a ∷ []), var x₂))
  where


free_ext₁ : ∀ {a a' l} → a ∉ l → ¬ a ≡ a' → a ∉ (l ++ a' ∷ [])
free_ext₁ {l = []} base p2 = step p2 base
free_ext₁ {l = x ∷ l} (step neq p1) p2 = step neq (free_ext₁ p1 p2)

free_ext₂ : ∀ {a a' l} → a ∉ l → a ≡ a' → dB (l ++ a' ∷ []) a 0
free_ext₂ {l = []} p1 p2 = base p2
free_ext₂ {l = x ∷ l} (step x₁ p1) p2 = step x₁ (free_ext₂ p1 p2)

suc_length : ∀ {A : Set} {a : A} {l : List A} → length (l ++ a ∷ []) ≡ suc (length l)
suc_length {l = []} = refl
suc_length {a = a} {l = x ∷ l} = cong suc (suc_length {a = a} {l = l})

bound_ext : ∀ {a a' l ℓ} → dB l a ℓ → dB (l ++ a' ∷ []) a (suc ℓ)
bound_ext {l = x ∷ []} (base eq) = base eq
bound_ext {a = a} {a' = a'} {l = x ∷ l@(_ ∷ _)} p@(base refl) = subst (λ ℓ → dB ((x ∷ l) ++ a' ∷ []) x ℓ) (suc_length {a = a'} {l = l}) (base {a = a}{ϕ = l ++ a' ∷ []} refl)
bound_ext {a' = a'} {l = x ∷ x₁ ∷ l} (step neq p) = step neq (bound_ext {a' = a'} p)

ext : ∀ {t₁ t₂ ϕ₁ ϕ₂ γ a}
      → γ ⊢ (ϕ₁ , t₁) =α (ϕ₂ , t₂)
      → γ ⊢ (ϕ₁ ++ (a ∷ []) , t₁) =α (ϕ₂ ++ (a ∷ []) , t₂)
ext (var x) = vext (var x)
ext vrefl = vrefl
ext (vsymm p) = vsymm (ext p)
ext (vtran p₁ p₂) = vtran (ext p₁) (ext p₂)
ext {a = a'} (atom {a₁ = a} (free f₁ f₂)) with a ≟ a'
ext {a = a'} (atom {a} (free {ϕ₁ = ϕ₁} {ϕ₂ = ϕ₂} {same_len = same_len} f₁ f₂)) | yes eq = atom (bound {same_len = subst₂ (λ h₁ h₂ → h₁ ≡ h₂) (sym (suc_length {a = a'} {l = ϕ₁})) (sym (suc_length {a = a'} {l = ϕ₂})) (cong suc same_len)} (free_ext₂ f₁ eq) (free_ext₂ f₂ eq))
ext {a = a'} (atom {a} (free {ϕ₁ = ϕ₁} {ϕ₂ = ϕ₂} {same_len = same_len} f₁ f₂)) | no ¬p = atom (free {same_len = subst₂ (λ h₁ h₂ → h₁ ≡ h₂) (sym (suc_length {a = a'} {l = ϕ₁})) (sym (suc_length {a = a'} {l = ϕ₂})) (cong suc same_len)} (free_ext₁ f₁ (neg→neg ¬p)) (free_ext₁ f₂ (neg→neg ¬p)))
ext {a = a'} (atom (bound {ϕ₁ = ϕ₁} {ϕ₂ = ϕ₂} {same_len = same_len} b₁ b₂)) = atom (bound {same_len = subst₂ (λ h₁ h₂ → h₁ ≡ h₂) (sym (suc_length {a = a'} {l = ϕ₁})) (sym (suc_length {a = a'} {l = ϕ₂})) (cong suc same_len)} (bound_ext b₁) (bound_ext b₂))
ext (bind p) = bind (ext p)
ext (fapp p₁ p₂) = fapp (ext p₁) (ext p₂)

Sub = Term → Term
record Eqn? : Set where
  constructor _≈?_
  field
    lhs : Closure
    rhs : Closure

make-sub : Var → Term → Sub
make-sub x t (var x') with x ≟ x'
make-sub x t (var x') | yes p = t
make-sub x t (var x') | no ¬p = var x'
make-sub x t (fapp t₁ t₂) = fapp (make-sub x t t₁) (make-sub x t t₂)
make-sub x t (atom a) = atom a
make-sub x t (bind a t') = bind a (make-sub x t t')

app : (Term → Term) → Eqn? → Eqn?
app σ ((ϕ₁ , t₁) ≈? (ϕ₂ , t₂)) = ((ϕ₁ , σ t₁) ≈? (ϕ₂ , σ t₂))

data not-occurs : Var → Term → Set where
  var : ∀ {x x'}
        → ¬ x ≡ x'
        → not-occurs x (var x')
  atom : ∀ {x a}
         → not-occurs x (atom a)
  bind : ∀ {x a t}
        → not-occurs x t
        → not-occurs x (bind a t)
  fapp : ∀ {x t₁ t₂}
        → not-occurs x t₁
        → not-occurs x t₂
        → not-occurs x (fapp t₁ t₂)
data occurs : Var → Term → Set where
  var : ∀ {x x'}
        → x ≡ x'
        → occurs x (var x')
  bind : ∀ {x a t}
        → occurs x t
        → occurs x (bind a t)
  fapp₁ : ∀ {x t₁ t₂}
        → occurs x t₁
        → occurs x (fapp t₁ t₂)
  fapp₂ : ∀ {x t₁ t₂}
        → occurs x t₂
        → occurs x (fapp t₁ t₂)
occurs? : (x : Var) → (t : Term) →  (occurs x t) ⊎ (not-occurs x t)
occurs? x (var x') with x ≟ x'
occurs? x (var x') | yes p = inj₁ (var p)
occurs? x (var x') | no ¬p = inj₂ (var (neg→neg ¬p))
occurs? x (fapp t₁ t₂) with occurs? x t₁ | occurs? x t₂
occurs? x (fapp t₁ t₂) | inj₁ y₁ | inj₁ y₂  = inj₁ (fapp₁ y₁)
occurs? x (fapp t₁ t₂) | inj₁ y | inj₂ n = inj₁ (fapp₁ y)
occurs? x (fapp t₁ t₂) | inj₂ n | inj₁ y = inj₁ (fapp₂ y)
occurs? x (fapp t₁ t₂) | inj₂ n₁ | inj₂ n₂ = inj₂ (fapp n₁ n₂)
occurs? x (atom a) = inj₂ atom
occurs? x (bind a t) with occurs? x t
occurs? x (bind a t) | inj₁ y = inj₁ (bind y)
occurs? x (bind a t) | inj₂ n = inj₂ (bind n)

occur_sub_lemma : ∀ {x t' t} → not-occurs x t → (make-sub x t') t ≡ t
occur_sub_lemma {x} (var {x' = x'} neq) with x ≟ x'
occur_sub_lemma {x} (var {x' = x'} neq) | yes p = refutation-elim (neq p)
occur_sub_lemma {x} (var {x' = x'} neq) | no ¬p = refl
occur_sub_lemma atom = refl
occur_sub_lemma (bind {x} {a} {t} p) = subst (λ hole → bind a hole ≡ bind a t) (sym (occur_sub_lemma p)) refl
occur_sub_lemma (fapp {x} {t₁} {t₂} p₁ p₂) = subst₂ (λ h₁ h₂ → fapp h₁ h₂ ≡ fapp t₁ t₂) (sym (occur_sub_lemma p₁)) (sym (occur_sub_lemma p₂)) refl

map_lemma : ∀ {A B} {f : A → B} {as : List A} {a : A}
        → a ∈ as → (f a) ∈ (map f as)
map_lemma base = base
map_lemma (step i) = step (map_lemma i)

data SnocView {A : Set} : List A → Set where
  nil : SnocView []
  snoc : ∀ (xs : List A) → (x : A)
         → SnocView (xs ++ (x ∷ []))
view : ∀ {A} → (xs : List A) → SnocView xs
view [] = nil
view (x ∷ xs) with view xs
view (x ∷ .[]) | nil = snoc [] x
view (x ∷ .(xs ++ x' ∷ [])) | snoc xs x' = snoc (x ∷ xs) x'
         
-- Don't know what happend to Agda, but ℓ decreases in the recursive step and clearly this function terminates.
ext_lemma : ∀ {ℓ} {t₁} {t₂} {γ} {ϕ} {eq : ℓ ≡ (length ϕ)} → γ ⊢ ([] , t₁) =α ([] , t₂) → γ ⊢ (ϕ , t₁) =α (ϕ , t₂)
ext_lemma {zero} {ϕ = []} {refl} p = p
ext_lemma {zero} {ϕ = x ∷ ϕ} {()} p
ext_lemma {suc ℓ} {ϕ = []} {()} p
ext_lemma {suc .(foldr (λ _ → suc) 0 ϕ')} {ϕ = ϕ@(_ ∷ ϕ')} {refl} p with view ϕ'
ext_lemma {suc _} {γ = _} {a ∷ .[]} {refl} p | nil = ext p
ext_lemma {suc ℓ} {t₁} {t₂} {γ} {ϕ @(x' ∷ .(xs ++ x ∷ []))} {refl} p | snoc xs x = ext (ext_lemma {ℓ} {t₁} {t₂} {γ} {x' ∷ xs} {suc_length {a = x} {l = xs}} p)

sub_lemma : ∀ {σ : Term → Term} {x t t' γ}
          {sub₂ : ∀ {a t} → bind a (σ t) ≡ σ (bind a t)}
          {sub₃ : ∀ {t₁ t₂} → fapp (σ t₁) (σ t₂) ≡ σ (fapp t₁ t₂)}
        → γ ⊢ ([] , σ (var x)) =α ([] , σ t)
        → γ ⊢ ([] , σ ((make-sub x t) t')) =α ([] , σ t')
sub_lemma {σ} {x} {t} {t'} {γ} p with occurs? x t'
sub_lemma {σ} {x} {t} {var x'} {γ} p | inj₁ c with x ≟ x'
sub_lemma {σ} {x} {t} {var x'} {γ} p | inj₁ c | yes eq = αsymm (subst (λ hole → γ ⊢ ([] , σ hole) =α ([] , σ t)) (subst (λ hole → var hole ≡ var x') (sym eq) refl) p)
sub_lemma {σ} {x} {t} {var x'} {γ} p | inj₁ c | no _ = αrefl
sub_lemma {σ} {x} {t} {fapp t₁ t₂} {γ} {sub₂} {sub₃} p | inj₁ c with sub_lemma {σ} {x} {t} {t₁} {γ} {sub₂} {sub₃} p | sub_lemma {σ} {x} {t} {t₂} {γ} {sub₂} {sub₃}  p
... | r₁ | r₂ = subst₂ (λ h₁ h₂ → γ ⊢ ([] , h₁) =α ([] , h₂)) sub₃ sub₃ (fapp r₁ r₂)
sub_lemma {σ} {x} {t} {bind a t'} {γ} {sub₂} {sub₃} p | inj₁ c with (ext_lemma {ϕ = a ∷ []} {eq = refl} (sub_lemma {σ} {x} {t} {t'} {γ} {sub₂} {sub₃} p))
... | r = subst₂ (λ h₁ h₂ → γ ⊢ ([] , h₁) =α ([] , h₂)) sub₂ sub₂ (bind r)
sub_lemma {σ} {x} {t} {t'} {γ} p | inj₂ n = subst (λ hole → γ ⊢ ([] , σ hole) =α ([] , σ t')) (sym (occur_sub_lemma n)) αrefl

data _⇒A_ : List Eqn? → List Eqn? → Set where 
     a  : ∀ {ϕ x t e}
          → ¬ var x ≡ t
          → ((ϕ , t) ≈? (ϕ , var x) ∷ e) ⇒A ((ϕ , var x) ≈? (ϕ , t) ∷ e)
     b  : ∀ {ϕ x e}
          → ((ϕ , var x) ≈? (ϕ , var x) ∷ e) ⇒A e
     c1 : ∀ {ϕ₁ a₁ ϕ₂ a₂ e}
          → (ϕ₁ , a₁) ≈α (ϕ₂ , a₂)
          → ((ϕ₁ , atom a₁) ≈? (ϕ₂ , atom a₂) ∷ e) ⇒A e
     c2 : ∀ {ϕ₁ a₁ t₁ ϕ₂ a₂ t₂ e}
          → ((ϕ₁ , bind a₁ t₁) ≈? (ϕ₂ , bind a₂ t₂) ∷ e) ⇒A ((a₁ ∷ ϕ₁ , t₁) ≈? (a₂ ∷ ϕ₂ , t₂) ∷ e)
     c3 : ∀ {ϕ₁ t₁ t₂ ϕ₂ t₁' t₂' e}
          → ((ϕ₁ , fapp t₁ t₂) ≈? (ϕ₂ , fapp t₁' t₂') ∷ e) ⇒A ((ϕ₁ , t₁) ≈? (ϕ₂ , t₁') ∷ (ϕ₁ , t₂) ≈? (ϕ₂ , t₂') ∷ e)
     d1 : ∀ {ϕ₁ x a₁ ϕ₂ a₂ e}
          → (ϕ₁ , a₁) ≈α (ϕ₂ , a₂)
          → ((ϕ₁ , var x) ≈? (ϕ₂ , atom a₂) ∷ e) ⇒A (([] , var x) ≈? ([] , atom a₁) ∷ (map (app (make-sub x (atom a₁))) e))
     d2 : ∀ {ϕ₁ x x₁ a₁ ϕ₂ a₂ t₂ e}
          → not-occurs x t₂
          → ((ϕ₁ , var x) ≈? (ϕ₂ , bind a₂ t₂) ∷ e) ⇒A (([] , var x) ≈? ([] , bind a₁ (var x₁)) ∷ (((a₁ ∷ ϕ₁) , var x₁) ≈? ((a₂ ∷ ϕ₂) , t₂)) ∷ (map (app (make-sub x (bind a₁ (var x₁)))) e))
     d3 : ∀ {ϕ₁ x x₁ x₂ ϕ₂ t₁ t₂ e}
          → ((ϕ₁ , var x) ≈? (ϕ₂ , fapp t₁ t₂) ∷ e) ⇒A (([] , var x) ≈? ([] , fapp (var x₁) (var x₂)) ∷ ((ϕ₁ , var x₁) ≈? (ϕ₂ , t₁)) ∷ ((ϕ₁ , var x₂) ≈? (ϕ₂ , t₂)) ∷ (map (app (make-sub x (fapp (var x₁) (var x₂)))) e))

soundness : ∀ {σ : Term → Term} {γ e e'} 
              {sub₁ : ∀ {a} → atom a ≡ σ (atom a)}
              {sub₂ : ∀ {a t} → bind a (σ t) ≡ σ (bind a t)}
              {sub₃ : ∀ {t₁ t₂} → fapp (σ t₁) (σ t₂) ≡ σ (fapp t₁ t₂)}
            → e ⇒A e'
            → (∀ {ϕ₁ t₁ ϕ₂ t₂} → ((ϕ₁ , t₁) ≈? (ϕ₂ , t₂)) ∈ e' → γ ⊢ (ϕ₁ , σ t₁) =α (ϕ₂ , σ t₂))
            → (∀ {ϕ₁ t₁ ϕ₂ t₂} → ((ϕ₁ , t₁) ≈? (ϕ₂ , t₂)) ∈ e → γ ⊢ (ϕ₁ , σ t₁) =α (ϕ₂ , σ t₂))
soundness (a x) h base = αsymm (h base)
soundness (a x) h (step i) = h (step i)
soundness b h base = αrefl
soundness b h (step i) = h i
soundness {σ} {γ} {sub₁ = sub} (c1 {ϕ₁} {a₁} {ϕ₂} {a₂} eq) h base = subst₂ (λ t₁ t₂ → γ ⊢ (ϕ₁ , t₁) =α (ϕ₂ , t₂)) sub sub (atom eq)
soundness (c1 x) h (step i) = h i
soundness {σ} {γ} {sub₂ = sub} (c2 {ϕ₁} {a₁} {t₁} {ϕ₂} {a₂} {t₂}) h base = subst₂ (λ t₁ t₂ → γ ⊢ (ϕ₁ , t₁) =α (ϕ₂ , t₂)) sub sub (bind (h base))
soundness c2 h (step i) = h (step i)
soundness {σ} {γ} {sub₃ = sub} (c3 {ϕ₁} {t₁} {t₂} {ϕ₂} {t₁'} {t₂'}) h base = subst₂ (λ t₁ t₂ → γ ⊢ (ϕ₁ , t₁) =α (ϕ₂ , t₂)) sub sub (fapp (h base) (h (step base)))
soundness c3 h (step i) = h (step (step i))
soundness {σ} {γ} {sub₁ = sub} (d1 {ϕ₁} {x} {a₁} {ϕ₂} {a₂} eq) h base
  with h base | subst (λ t₂ → γ ⊢ (ϕ₁ , atom a₁) =α (ϕ₂ , t₂)) sub (atom eq)
... | eq₁ | eq₂ = αtran (ext_lemma {ℓ = (length ϕ₁)} {eq = refl} (subst (λ t₂ → γ ⊢ ([] , σ (var x)) =α ([] , t₂)) (sym sub) eq₁)) eq₂
soundness {σ} {γ} {sub₂ = sub₂} {sub₃ = sub₃} (d1 {x = x} eq) h {ϕ₁} {t₁} {ϕ₂} {t₂} (step i)
  = (αsymm (αtran (αsymm (αtran (h (step (map_lemma i))) (ext_lemma {ℓ = (length ϕ₂)} {eq = refl} (sub_lemma {σ = σ} {t' = t₂} {sub₂ = sub₂} {sub₃ = sub₃} (h base))))) (ext_lemma {ℓ = (length ϕ₁)} {eq = refl} (sub_lemma {σ = σ} {t' = t₁} {sub₂ = sub₂} {sub₃ = sub₃} (h base)))))
soundness {σ} {γ} {sub₂ = sub} (d2 {ϕ₁} {x} {x₁} {a₁} {ϕ₂} {a₂} {t₂} n) h base
  with h base | subst (λ t₂ → γ ⊢ (ϕ₁ , bind a₁ (σ (var x₁))) =α (ϕ₂ , t₂)) sub (bind (h (step base))) 
... | eq₁ | eq₂ = αtran (ext_lemma {ℓ = (length ϕ₁)} {eq = refl} (subst (λ t → γ ⊢ ([] , σ (var x)) =α ([] , t)) (sym sub) eq₁)) eq₂
soundness {σ} {γ} {sub₂ = sub₂} {sub₃ = sub₃} (d2 {x = x} x₁) h {ϕ₁} {t₁ = t₁} {ϕ₂} {t₂ = t₂} (step i)
  = (αsymm (αtran (αsymm (αtran (h (step (step (map_lemma i)))) (ext_lemma {ℓ = (length ϕ₂)} {eq = refl} (sub_lemma {σ = σ} {t' = t₂} {sub₂ = sub₂} {sub₃ = sub₃} (h base))))) (ext_lemma {ℓ = (length ϕ₁)} {eq = refl} (sub_lemma {σ = σ} {t' = t₁} {sub₂ = sub₂} {sub₃ = sub₃} (h base)))))
soundness {σ} {γ} {sub₃ = sub} (d3 {ϕ₁} {x} {x₁} {x₂} {ϕ₂} {t₁} {t₂}) h base 
  with h base | subst (λ t → γ ⊢ (ϕ₁ , fapp (σ (var x₁)) (σ (var x₂))) =α (ϕ₂ , t)) sub (fapp (h (step base)) (h (step (step base))))
... | eq₁ | eq₂  = αtran (ext_lemma {ℓ = (length ϕ₁)} {eq = refl} (subst (λ t → γ ⊢ ([] , σ (var x)) =α ([] , t)) (sym sub) eq₁)) eq₂
soundness {σ} {γ} {sub₂ = sub₂} {sub₃ = sub₃} (d3 {x = x} {e = e}) h {ϕ₁} {t₁} {ϕ₂} {t₂} (step i)
  = (αsymm (αtran (αsymm (αtran (h (step (step (step (map_lemma i))))) (ext_lemma {ℓ = (length ϕ₂)} {eq = refl} (sub_lemma {σ = σ} {t' = t₂} {sub₂ = sub₂} {sub₃ = sub₃} (h base))))) (ext_lemma {ℓ = (length ϕ₁)} {eq = refl} (sub_lemma {σ = σ} {t' = t₁} {sub₂ = sub₂} {sub₃ = sub₃} (h base)))))


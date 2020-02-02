module wellfounded where

open import Data.Nat
open import Relation.Binary

data Acc {ℓ} {A : Set ℓ} (_<_ : Rel A ℓ) (x : A) : Set ℓ where
  acc : (∀ y → y < x → Acc _<_ y) → Acc _<_ x

mutual
  ℕ-allgood' : (n y : ℕ) → y <′ n → Acc _<′_ y
  ℕ-allgood' zero y ()
  ℕ-allgood' (suc n) .n ≤′-refl = ℕ-allgood n
  ℕ-allgood' (suc n) y (≤′-step y<'n) = ℕ-allgood' n y y<'n

  ℕ-allgood : (n : ℕ) → Acc _<′_ n
  ℕ-allgood n = acc (ℕ-allgood' n)


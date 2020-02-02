open import Data.List

data SnocView {A : Set} : List A → Set where
  nil : SnocView []
  snoc : ∀ (xs : List A) → (x : A)
         → SnocView (xs ++ (x ∷ []))
view : ∀ {A} → (xs : List A) → SnocView xs
view [] = nil
view (x ∷ xs) with view xs
view (x ∷ .[]) | nil = snoc [] x
view (x ∷ .(xs ++ x' ∷ [])) | snoc xs x' = snoc (x ∷ xs) x'
         

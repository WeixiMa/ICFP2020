module refutation where

open import Data.Empty
open import Relation.Binary.PropositionalEquality

-- It turns out there's a way to get uniqueness of refutations without
-- any postulates in Agda. The trick is to declare an irrelevant field
-- of type ⊥ in a record. η-expansion of the record's values causes
-- them to be compared as if they were ⊤, because irrelevant fields
-- are irrelevant to judgmental equality as well. At the same time, it
-- is possible to eliminate irrelevant fields as empty patterns in a
-- relevant context, so they work fine as ⊥ replacements.
--
-- Let p q : Πx:A.Refutation.
-- They are judgmentally equal, because
-- p = λ a : A . p a     η for Π
--   = λ a : A . ref _   η for Refutation, _ for irrelevant position
-- and q expands the same way.
-- These are α-equivalent, so refl proves their equality.
--
-- Note that we could also make the proof fields in the data structure
-- irrelevant, but that is a much bigger use of irrelevance. This is
-- essentially a hack to work around the absence of η for ⊥, and can
-- work in many type theories.

record Refutation {α} : Set α where
  constructor ref
  field
    .bot : ⊥

refutation-elim : ∀ {α β} {B : Set β} -> Refutation {α} → B
refutation-elim (ref ())

ref≡ : ∀ {α} (r1 r2 : Refutation {α}) → r1 ≡ r2
ref≡ r1 r2 = refl

infix 3 ¬_

¬_ : ∀ {α} → Set α → Set α
¬_ {α} P = P → Refutation {α}

neg→neg : ∀ {α} {A : Set α} → (A → ⊥) → ¬ A
neg→neg ¬A = λ a → ref (¬A a)


refutations-unique : ∀ {α} {A : Set α} → (f g : ¬ A) → f ≡ g
refutations-unique f g = refl

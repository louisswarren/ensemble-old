open import Agda.Builtin.Equality

open import Decidable
open import List renaming (_∈_ to _[∈]_; _∉_ to _[∉]_)

-- An ensemble is like a decidable finite set, but we do not define a
-- comprehension constructor.

data Ensemble {A : Set} (_≟_ : Decidable≡ A) : Set where
  ∅   : Ensemble _≟_
  _∷_ : A            → Ensemble _≟_ → Ensemble _≟_
  _-_ : Ensemble _≟_ → A            → Ensemble _≟_
  _∪_ : Ensemble _≟_ → Ensemble _≟_ → Ensemble _≟_

data _∈_∖_ {A : Set} {_≟_ : Decidable≡ A} (α : A) : Ensemble _≟_ → List A → Set where
  head : ∀{β αs xs} → α ≡ β → α [∉] xs → α ∈ (β ∷ αs) ∖ xs
  tail : ∀{β αs xs} → α ∈ αs ∖ xs      → α ∈ (β ∷ αs) ∖ xs







_∈_ : {A : Set} {_≟_ : Decidable≡ A} → (α : A) → Ensemble _≟_ → Set
α ∈ αs = α ∈ αs ∖ []

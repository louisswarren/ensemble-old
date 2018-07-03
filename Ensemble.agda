open import Agda.Builtin.Equality

open import Decidable
open import List renaming ( _∈_ to _[∈]_ ;
                            _∉_ to _[∉]_ ;
                            All to All[] ;
                            Any to Any[] )

-- An ensemble is like a decidable finite set, but we do not define a
-- comprehension constructor.

data Ensemble {A : Set} (_≟_ : Decidable≡ A) : Set where
  ∅   : Ensemble _≟_
  _∷_ : A            → Ensemble _≟_ → Ensemble _≟_
  _-_ : Ensemble _≟_ → A            → Ensemble _≟_
  _∪_ : Ensemble _≟_ → Ensemble _≟_ → Ensemble _≟_


data All_⟨_∖_⟩ {A : Set} {_≟_ : Decidable≡ A} (P : A → Set) : Ensemble _≟_ → List A → Set where
  ∅      : ∀{αs xs}    → All P ⟨ αs ∖ xs ⟩
  _∷_    : ∀{αs xs α}  → P α      → All P ⟨ αs ∖ xs ⟩ → All P ⟨ (α ∷ αs) ∖ xs ⟩
  _-∷_   : ∀{αs xs α}  → α [∈] xs → All P ⟨ αs ∖ xs ⟩ → All P ⟨ (α ∷ αs) ∖ xs ⟩
  delete : ∀{αs xs x}  → All P ⟨ αs ∖ (x ∷ xs) ⟩ → All P ⟨ (αs - x) ∖ xs ⟩
  _∪_    : ∀{αs βs xs} → All P ⟨ αs ∖ xs ⟩ → All P ⟨ βs ∖ xs ⟩ → All P ⟨ (αs ∪ βs) ∖ xs ⟩

All : {A : Set} {_≟_ : Decidable≡ A} → (P : A → Set) → Ensemble _≟_ → Set
All P αs = All P ⟨ αs ∖ [] ⟩


data Any_⟨_∖_⟩ {A : Set} {_≟_ : Decidable≡ A} (P : A → Set) : Ensemble _≟_ → List A → Set where

Any : {A : Set} {_≟_ : Decidable≡ A} → (P : A → Set) → Ensemble _≟_ → Set
Any P αs = Any P ⟨ αs ∖ [] ⟩


_∈_ : {A : Set} {_≟_ : Decidable≡ A} → (α : A) → Ensemble _≟_ → Set
α ∈ αs = Any (α ≡_) αs

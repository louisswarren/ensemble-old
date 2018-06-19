open import Decidable
open import List

-- An ensemble is like a decidable finite set, but we do not define a
-- comprehension constructor.

data Ensemble {A : Set} (_≟_ : Decidable≡ A) : Set where
  ∅   : Ensemble _≟_
  _∷_ : A            → Ensemble _≟_ → Ensemble _≟_
  _-_ : Ensemble _≟_ → A            → Ensemble _≟_
  _∪_ : Ensemble _≟_ → Ensemble _≟_ → Ensemble _≟_

data _∈_∖_ {A : Set} {_≟_ : Decidable≡ A} (x : A) : Ensemble _≟_ → List A → Set where

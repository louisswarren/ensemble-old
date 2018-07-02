module List where

open import Agda.Builtin.List public

open import Agda.Builtin.Equality

open import Decidable

infixr 5 _++_

_++_ : {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

record Membership {A : Set} : Set where
  constructor membership
  field
    _≟_ : Decidable≡ A

  data _∈_ (x : A) : List A → Set where
    head : ∀{y ys} → x ≡ y  → x ∈ (y ∷ ys)
    tail : ∀{y ys} → x ∈ ys → x ∈ (y ∷ ys)

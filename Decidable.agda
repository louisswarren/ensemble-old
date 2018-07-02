module Decidable where

open import Agda.Builtin.Equality public

data ⊥ : Set where

¬_ : (A : Set) → Set
¬ A = A → ⊥

_≢_ : {A : Set} → A → A → Set
x ≢ y = ¬(x ≡ y)

data Dec (A : Set) : Set where
  yes :   A → Dec A
  no  : ¬ A → Dec A

Decidable : {A : Set} → (A → Set) → Set
Decidable P = ∀ x → Dec (P x)

Decidable≡ : Set → Set
Decidable≡ A = (x y : A) → Dec (x ≡ y)

isYes : {A : Set} → {f : A → Set} → Decidable f → A → Set
isYes {_} {f} P x = f x

isNo : {A : Set} → {f : A → Set} → Decidable f → A → Set
isNo {_} {f} P x = ¬(f x)

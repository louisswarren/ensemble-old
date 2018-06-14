module Decidable where

open import Agda.Builtin.Equality

data ⊥ : Set where

¬_ : (A : Set) → Set
¬ A = A → ⊥


data Dec (A : Set) : Set where
  yes :   A → Dec A
  no  : ¬ A → Dec A


data isYes {A : Set} : Dec A → Set where
  since : (x : A) → isYes (yes x)

yesIsYes : {A : Set}{a : A}{x : Dec A} → x ≡ (yes a) → isYes x
yesIsYes {_} {a} refl = since a


data isNo {A : Set} : Dec A → Set where
  since : (x : ¬ A) → isNo (no x)

noIsNo : {A : Set}{a : ¬ A}{x : Dec A} → x ≡ (no a) → isNo x
noIsNo {_} {a} refl = since a


Decidable : {A : Set} → (A → Set) → Set
Decidable P = ∀ x → Dec (P x)

BiDecidable : {A B : Set} → (A → B → Set) → Set
BiDecidable P = ∀ x y → Dec (P x y)

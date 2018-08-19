module Functools where

open import Agda.Builtin.Equality

_∘_ : ∀{k n m}{A : Set k}{B : A → Set n}{C : (x : A) → B x → Set m}
      → (f : {x : A} → (y : B x) → C x y)
      → (g : (x : A) → B x)
      → ((x : A) → C x (g x))
(f ∘ g) x = f (g x)


data Inspect {A : Set}(x : A) : Set where
  _with≡_ : (y : A) → x ≡ y → Inspect x

inspect : {A : Set} → (x : A) → Inspect x
inspect x = x with≡ refl

data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

⊎-elim : {C : Set} → {A B : Set} → A ⊎ B → (A → C) → (B → C) → C
⊎-elim (inl a) A→C B→C = A→C a
⊎-elim (inr b) A→C B→C = B→C b


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

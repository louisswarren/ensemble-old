module Find where

open import Decidable
open import Functools
open import List

data Find {A : Set} {f : A → Set} (P : Decidable f) : List A → Set where
  missing : ∀{xs}       → All (isNo P) xs        → Find P xs
  found   : ∀{y} → ∀ xs → isYes P y       → ∀ ys → Find P (xs ++ y ∷ ys)

find : {A : Set} {f : A → Set} → (P : Decidable f) → (xs : List A) → Find P xs
find P [] = missing []
find P (x ∷ xs) with inspect (P x)
...             | yes fx with≡ eq = found [] fx xs
...             | no ¬fx with≡ eq with find P xs
...                               | missing ∀x¬fx   = missing (¬fx ∷ ∀x¬fx)
...                               | found xs' fy ys = found (x ∷ xs') fy ys

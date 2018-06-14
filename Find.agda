module Find where

open import All
open import Decidable
open import Functools
open import List

data Find {A : Set}{f : A → Set}(P : Decidable f) : List A → Set where
  missing : ∀{xs}     → All (isNo ∘ P) xs → Find P xs
  found   : ∀ xs y ys → isYes (P y)       → Find P (xs ++ y ∷ ys)

find : {A : Set}{f : A → Set} → (P : Decidable f) → (xs : List A) → Find P xs
find P [] = missing []
find P (x ∷ xs) with inspect (P x)
find P (x ∷ xs) | yes a with≡ eq = found [] x xs (yesIsYes eq)
find P (x ∷ xs) | no ¬a with≡ eq with find P xs
...                              | missing pf        = missing (noIsNo eq ∷ pf)
...                              | found pre y ys pf = found (x ∷ pre) y ys pf

open import List
open import Decidable
open import Ensemble
open import Agda.Builtin.Nat renaming (Nat to ℕ) hiding (_-_)
open import Agda.Builtin.Equality

droop : ∀{n m} → suc n ≡ suc m → n ≡ m
droop refl = refl

natdec : Decidable≡ ℕ
natdec zero    zero     = yes refl
natdec zero    (suc m)  = no (λ ())
natdec (suc n) zero     = no (λ ())
natdec (suc n) (suc m)  with natdec n m
...                     | yes refl = yes refl
...                     | no x = no λ seq → x (droop seq)


omo : Ensemble natdec
omo = (1 ∷ ∅) - 1

a : Empty omo
a = 1 ~ ([ refl ] -∷ ∅)

au : Dec (Empty omo)
au = empty? omo

r : au ≡ (yes a)
r = refl

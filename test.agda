open import List
open import Decidable
open import Agda.Builtin.Nat renaming (Nat to ℕ)
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


_∈_ : ℕ → List ℕ → Set
_∈_ = Membership._∈_ (membership natdec)

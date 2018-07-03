module List where

open import Agda.Builtin.List public

open import Agda.Builtin.Equality

open import Decidable

infixr 5 _++_

_++_ : {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)


data All {A : Set} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : ∀{x xs} → P x → All P xs → All P (x ∷ xs)

data Any {A : Set} (P : A → Set) : List A → Set where
  any : ∀{y} → ∀ xs → P y → ∀ ys → Any P (xs ++ y ∷ ys)


-- The above defines membership. We define non-membership positively.

_∈_ : {A : Set} → (x : A) → List A → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : {A : Set} → (x : A) → List A → Set
x ∉ xs = All (x ≢_) xs

-- Alternative ways of constructing _∈_ and _∉_
∈head : {A : Set} {x : A} → ∀{y ys} → x ≡ y  → x ∈ (y ∷ ys)
∈head x≡y = any [] x≡y _

∈tail : {A : Set} {x : A} → ∀{y ys} → x ∈ ys → x ∈ (y ∷ ys)
∈tail (any xs eq ys) = any (_ ∷ xs) eq ys

∉empty : {A : Set} {x : A} → x ∉ []
∉empty = []

∉notat : {A : Set} {x : A} → ∀{y ys} → x ≢ y → x ∉ ys → x ∉ (y ∷ ys)
∉notat x≢y x∉ys = x≢y ∷ x∉ys


-- Check that _∉_ is equivalent to ¬ ∘ _∈_

thm:∉→¬∈ : {A : Set} → (x : A) → (xs : List A) → x ∉ xs → ¬(x ∈ xs)
thm:∉→¬∈ x xs x∉xs x∈xs = {!   !}

thm:¬∈→∉ : {A : Set} → (x : A) → (xs : List A) → ¬(x ∈ xs) → x ∉ xs
thm:¬∈→∉ x [] ¬x∈xs = []
thm:¬∈→∉ x (y ∷ xs) ¬x∈xs = (λ x≡y → ¬x∈xs (any [] x≡y xs))
                            ∷ thm:¬∈→∉ x xs λ anyxs → ¬x∈xs (∈tail anyxs)

-- Useful theorems
all++ : {A : Set} {xs ys : List A} {P : A → Set}
        → All P xs → All P ys → All P (xs ++ ys)
all++ []       ys = ys
all++ (x ∷ xs) ys = x ∷ all++ xs ys

all++l : {A : Set} {xs ys : List A} {P : A → Set} → All P (xs ++ ys) → All P xs
all++l {_} {[]}    _             = []
all++l {_} {_ ∷ _} (pfx ∷ pfrst) = pfx ∷ all++l pfrst

all++r : {A : Set} {xs ys : List A} {P : A → Set} → All P (xs ++ ys) → All P ys
all++r {_} {_}      {[]}     pf            = []
all++r {_} {[]}     {y ∷ ys} pf            = pf
all++r {_} {x ∷ xs} {y ∷ ys} (pfx ∷ pfrst) = all++r pfrst

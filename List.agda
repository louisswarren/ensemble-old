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
  [_] : ∀{xs} → ∀{x} → P x      → Any P (x ∷ xs)
  _∷_ : ∀{xs} → ∀ x  → Any P xs → Any P (x ∷ xs)

-- The above defines membership. We define non-membership positively.

_∈_ : {A : Set} → (x : A) → List A → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : {A : Set} → (x : A) → List A → Set
x ∉ xs = All (x ≢_) xs

-- Alternative ways of constructing _∈_ and _∉_
∈head : {A : Set} {x : A} → ∀{y ys} → x ≡ y  → x ∈ (y ∷ ys)
∈head x≡y = [ x≡y ]

∈tail : {A : Set} {x : A} → ∀{y ys} → x ∈ ys → x ∈ (y ∷ ys)
∈tail a = _ ∷ a

∉empty : {A : Set} {x : A} → x ∉ []
∉empty = []

∉notat : {A : Set} {x : A} → ∀{y ys} → x ≢ y → x ∉ ys → x ∉ (y ∷ ys)
∉notat x≢y x∉ys = x≢y ∷ x∉ys


-- Check that _∉_ is equivalent to ¬ ∘ _∈_

∉→¬∈ : {A : Set} → {x : A} → {xs : List A} → x ∉ xs → ¬(x ∈ xs)
∉→¬∈ {_} {x} {xs}     (x≢x ∷ x∉xs) [ refl ]   = x≢x refl
∉→¬∈ {_} {x} {_ ∷ xs} (x≢y ∷ x∉xs) (y ∷ x∈xs) = ∉→¬∈ x∉xs x∈xs

¬∈→∉ : {A : Set} → {x : A} → {xs : List A} → ¬(x ∈ xs) → x ∉ xs
¬∈→∉ {_} {x} {[]}     ¬x∈xs = []
¬∈→∉ {_} {x} {y ∷ xs} ¬x∈xs = (λ x≡y → ¬x∈xs [ x≡y ])
                              ∷ ¬∈→∉ (λ anyxs → ¬x∈xs (y ∷ anyxs))

-- Decidability of _∈_ follows from decidability of _≡_

decide∈ : {A : Set} → Decidable≡ A → (x : A) → (xs : List A) → Dec (x ∈ xs)
decide∈ _≟_ x [] = no (λ ())
decide∈ _≟_ x (y ∷ xs) with x ≟ y
...                    | yes x≡y = yes [ x≡y ]
...                    | no  x≢y with decide∈ _≟_ x xs
...                              | yes x∈xs = yes (y ∷ x∈xs)
...                              | no ¬x∈xs = no (∉→¬∈ (x≢y ∷ ¬∈→∉ ¬x∈xs))

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

module All where

open import List

data All {A : Set} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : ∀{x xs} → P x → All P xs → All P (x ∷ xs)

data Any {A : Set} (P : A → Set) : List A → Set where
  any : ∀{y} → ∀ xs → P y → ∀ ys → Any P (xs ++ y ∷ ys)

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

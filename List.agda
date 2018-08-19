module List where

open import Agda.Builtin.List public
open import Agda.Builtin.Equality
open import Decidable
open import Functools

infixr 5 _++_

_++_ : {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)


data All {A : Set} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : ∀{x xs} → P x → All P xs → All P (x ∷ xs)

headAll : ∀{A x xs} {P : A → Set} → All P (x ∷ xs) → P x
headAll (Px ∷ _) = Px

tailAll : ∀{A x xs} {P : A → Set} → All P (x ∷ xs) → All P xs
tailAll (_ ∷ ∀xsP) = ∀xsP

all : {A : Set} {P : A → Set} → (P? : Decidable P) → (xs : List A) → Dec (All P xs)
all P? [] = yes []
all P? (x ∷ xs) with P? x
...             | no ¬Px = no λ φ → ¬Px (headAll φ)
...             | yes Px with all P? xs
...                      | yes ∀xsP = yes (Px ∷ ∀xsP)
...                      | no ¬∀xsP = no λ φ → ¬∀xsP (tailAll φ)


data Any {A : Set} (P : A → Set) : List A → Set where
  [_] : ∀{xs} → ∀{x} → P x      → Any P (x ∷ xs)
  _∷_ : ∀{xs} → ∀ x  → Any P xs → Any P (x ∷ xs)

hereAny : ∀{A x xs} {P : Pred A} → Any P (x ∷ xs) → ¬(Any P xs) → P x
hereAny [ Px ]     ¬∃xsP = Px
hereAny (_ ∷ ∃xsP) ¬∃xsP = ⊥-elim (¬∃xsP ∃xsP)

laterAny : ∀{A x xs} {P : Pred A} → Any P (x ∷ xs) → ¬(P x) → (Any P xs)
laterAny [ Px ]     ¬Px = ⊥-elim (¬Px Px)
laterAny (_ ∷ ∃xsP) ¬Px = ∃xsP

any : {A : Set} {P : A → Set} → (P? : Decidable P) → (xs : List A) → Dec (Any P xs)
any P? [] = no (λ ())
any P? (x ∷ xs) with P? x
...             | yes Px = yes [ Px ]
...             | no ¬Px with any P? xs
...                      | yes ∃xsP = yes (x ∷ ∃xsP)
...                      | no ¬∃xsP = no λ φ → ¬Px (hereAny φ ¬∃xsP)


-- The above defines membership.

_∈_ : {A : Set} → (x : A) → List A → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : {A : Set} → (x : A) → List A → Set
x ∉ xs = ¬(x ∈ xs)

decide∈ : {A : Set} → Decidable≡ A → (x : A) → (xs : List A) → Dec (x ∈ xs)
decide∈ _≟_ x xs = any (x ≟_) xs


-- Alternative ways of constructing _∈_ and _∉_
∈head : {A : Set} {x : A} → ∀{y ys} → x ≡ y  → x ∈ (y ∷ ys)
∈head x≡y = [ x≡y ]

∈tail : {A : Set} {x : A} → ∀{y ys} → x ∈ ys → x ∈ (y ∷ ys)
∈tail a = _ ∷ a

∉empty : {A : Set} {x : A} → x ∉ []
∉empty ()

∉notat : {A : Set} {x : A} → ∀{y ys} → x ≢ y → x ∉ ys → x ∉ (y ∷ ys)
∉notat x≢y x∉ys [ x≡y ]    = x≢y x≡y
∉notat x≢y x∉ys (x ∷ x∈ys) = x∉ys x∈ys

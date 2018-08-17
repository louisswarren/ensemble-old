module Vec where

open import Agda.Builtin.Nat renaming (Nat to ℕ)

open import Decidable

data Vec (A : Set) : ℕ → Set where
  []  : Vec A zero
  _∷_ : ∀{n} → A → Vec A n → Vec A (suc n)

data All {A} (P : A → Set) : {n : ℕ} → Vec A n → Set where
  []  : All P []
  _∷_ : ∀{x n} {xs : Vec A n} → P x → All P xs → All P (x ∷ xs)

all : ∀{A n} {P : A → Set} → (P? : Decidable P) → (xs : Vec A n) → Dec (All P xs)
all P? [] = yes []
all P? (x ∷ xs) with P? x
...             | no ¬Px = no φ
                           where φ : _
                                 φ (Px ∷ _) = ¬Px Px
...             | yes Px with all P? xs
...                      | yes ∀xsP = yes (Px ∷ ∀xsP)
...                      | no ¬∀xsP = no φ
                                      where φ : _
                                            φ (_ ∷ z) = ¬∀xsP z

data Any {A} (P : A → Set) : {n : ℕ} → Vec A n → Set where
  [_] : ∀{n} {xs : Vec A n} → ∀{x} → P x      → Any P (x ∷ xs)
  _∷_ : ∀{n} {xs : Vec A n} → ∀ x  → Any P xs → Any P (x ∷ xs)

any : ∀{A n} {P : A → Set} → (P? : Decidable P) → (xs : Vec A n) → Dec (Any P xs)
any P? [] = no (λ ())
any P? (x ∷ xs) with P? x
...             | yes Px = yes [ Px ]
...             | no ¬Px with any P? xs
...                      | yes ∃xsP = yes (x ∷ ∃xsP)
...                      | no ¬∃xsP = no φ where φ : _
                                                 φ [ Px ]  = ¬Px Px
                                                 φ (x ∷ a) = ¬∃xsP a

-- The above defines membership. We define non-membership positively.

_∈_ : ∀{A n} → (x : A) → Vec A n → Set
x ∈ xs = Any (x ≡_) xs


decide∈ : ∀{A n} → Decidable≡ A → (x : A) → (xs : Vec A n) → Dec (x ∈ xs)
decide∈ _≟_ x xs = any (x ≟_) xs

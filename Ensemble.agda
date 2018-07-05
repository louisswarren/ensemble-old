open import Agda.Builtin.Equality

open import Decidable
open import List
  renaming (
    _∈_      to _[∈]_        ;
    _∉_      to _[∉]_        ;
    All      to All[]        ;
    Any      to Any[]        ;
    thm:∉→¬∈ to thm:[∉]→¬[∈] ;
    thm:¬∈→∉ to thm:¬[∈]→[∉] )

open import Functools


-- An ensemble is like a decidable finite set, but we do not define a
-- comprehension constructor.

data Ensemble {A : Set} (_≟_ : Decidable≡ A) : Set where
  ∅   : Ensemble _≟_
  _∷_ : A            → Ensemble _≟_ → Ensemble _≟_
  _-_ : Ensemble _≟_ → A            → Ensemble _≟_
  _∪_ : Ensemble _≟_ → Ensemble _≟_ → Ensemble _≟_


data All_⟨_∖_⟩ {A : Set} {_≟_ : Decidable≡ A} (P : A → Set) : Ensemble _≟_ → List A → Set where
  ∅    : ∀{xs}       → All P ⟨ ∅ ∖ xs ⟩
  _∷_  : ∀{αs xs α}  → P α      → All P ⟨ αs ∖ xs ⟩ → All P ⟨ α ∷ αs ∖ xs ⟩
  _-∷_ : ∀{αs xs α}  → α [∈] xs → All P ⟨ αs ∖ xs ⟩ → All P ⟨ α ∷ αs ∖ xs ⟩
  _~_  : ∀{αs xs}    → ∀ x → All P ⟨ αs ∖ x ∷ xs ⟩ → All P ⟨ αs - x ∖ xs ⟩
  _∪_  : ∀{αs βs xs} → All P ⟨ αs ∖ xs ⟩ → All P ⟨ βs ∖ xs ⟩ → All P ⟨ αs ∪ βs ∖ xs ⟩

All : {A : Set} {_≟_ : Decidable≡ A} → (P : A → Set) → Ensemble _≟_ → Set
All P αs = All P ⟨ αs ∖ [] ⟩


data Any_⟨_∖_⟩ {A : Set} {_≟_ : Decidable≡ A} (P : A → Set) : Ensemble _≟_ → List A → Set where
  [_,_] : ∀{αs xs α} → P α  → α [∉] xs              → Any P ⟨ α ∷ αs ∖ xs ⟩
  _∷_   : ∀{αs xs}   → ∀ α  → Any P ⟨ αs ∖ xs ⟩     → Any P ⟨ α ∷ αs ∖ xs ⟩
  _~_   : ∀{αs xs}   → ∀ x  → Any P ⟨ αs ∖ x ∷ xs ⟩ → Any P ⟨ αs - x ∖ xs ⟩
  _∣∪_  : ∀{βs xs}   → ∀ αs → Any P ⟨ βs ∖ xs ⟩     → Any P ⟨ αs ∪ βs ∖ xs ⟩
  _∪∣_  : ∀{αs xs}   → Any P ⟨ αs ∖ xs ⟩     → ∀ βs → Any P ⟨ αs ∪ βs ∖ xs ⟩

Any : {A : Set} {_≟_ : Decidable≡ A} → (P : A → Set) → Ensemble _≟_ → Set
Any P αs = Any P ⟨ αs ∖ [] ⟩


_∈_ : {A : Set} {_≟_ : Decidable≡ A} → (α : A) → Ensemble _≟_ → Set
α ∈ αs = Any (α ≡_) αs

_∉_ : {A : Set} {_≟_ : Decidable≡ A} → (α : A) → Ensemble _≟_ → Set
α ∉ αs = All (α ≢_) αs


-- Prove that ∀α ¬Pα is equivalent to ¬∃α Pα

thm:all¬→¬any : {A : Set} → {_≟_ : Decidable≡ A}
                → (P : A → Set) → (αs : Ensemble _≟_) → (xs : List A)
                → All (¬_ ∘ P) ⟨ αs ∖ xs ⟩ → ¬(Any P ⟨ αs ∖ xs ⟩)
thm:all¬→¬any P ∅         xs all¬            ()
thm:all¬→¬any P (α ∷ αs)  xs (¬Pα ∷ all¬)    [ Pα , α∉xs ] = ¬Pα Pα
thm:all¬→¬any P (α ∷ αs)  xs (α∈xs -∷ all¬)  [ Pα , α∉xs ] = thm:[∉]→¬[∈] α xs α∉xs α∈xs
thm:all¬→¬any P (α ∷ αs)  xs (x ∷ all¬)      (.α ∷ any)    = thm:all¬→¬any P αs xs all¬ any
thm:all¬→¬any P (α ∷ αs)  xs (x -∷ all¬)     (.α ∷ any)    = thm:all¬→¬any P αs xs all¬ any
thm:all¬→¬any P (αs - α)  xs (.α ~ all¬)     (.α ~ any)    = thm:all¬→¬any P αs (α ∷ xs) all¬ any
thm:all¬→¬any P (αs ∪ βs) xs (allα¬ ∪ allβ¬) (.αs ∣∪ any)  = thm:all¬→¬any P βs xs allβ¬ any
thm:all¬→¬any P (αs ∪ βs) xs (allα¬ ∪ allβ¬) (any ∪∣ .βs)  = thm:all¬→¬any P αs xs allα¬ any

thm:¬any→all¬ : {A : Set} → {_≟_ : Decidable≡ A}
                → (P : A → Set) → (αs : Ensemble _≟_) → (xs : List A)
                → ¬(Any P ⟨ αs ∖ xs ⟩) → All (¬_ ∘ P) ⟨ αs ∖ xs ⟩
thm:¬any→all¬ P ∅ xs ¬any = ∅
thm:¬any→all¬ {_} {_≟_} P (α ∷ αs) xs ¬any with decide∈ _≟_ α xs
...           | yes α∈xs = α∈xs -∷ thm:¬any→all¬ P αs xs λ any → ¬any (α ∷ any)
...           | no ¬α∈xs = (λ Pα → ¬any [ Pα , thm:¬[∈]→[∉] α xs ¬α∈xs ])
                           ∷ thm:¬any→all¬ P αs xs λ any → ¬any (α ∷ any)
thm:¬any→all¬ P (αs - α)  xs ¬any = α ~ thm:¬any→all¬ P αs (α ∷ xs) λ any → ¬any (α ~ any)
thm:¬any→all¬ P (αs ∪ βs) xs ¬any = thm:¬any→all¬ P αs xs (λ z → ¬any (z ∪∣ βs))
                                    ∪ thm:¬any→all¬ P βs xs λ z → ¬any (αs ∣∪ z)


---- Check that _∉_ is equivalent to ¬ ∘ _∈_
thm:∉→¬∈ : {A : Set} {_≟_ : Decidable≡ A} → (x : A) → (xs : Ensemble _≟_) → x ∉ xs → ¬(x ∈ xs)
thm:∉→¬∈ x xs x∉xs = thm:all¬→¬any (_≡_ x) xs [] x∉xs

thm:¬∈→∉ : {A : Set} {_≟_ : Decidable≡ A} → (x : A) → (xs : Ensemble _≟_) → ¬(x ∈ xs) → x ∉ xs
thm:¬∈→∉ x xs ¬x∈xs = thm:¬any→all¬ (_≡_ x) xs [] ¬x∈xs

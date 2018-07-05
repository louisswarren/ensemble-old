open import Agda.Builtin.Equality

open import Decidable
open import List
  renaming (
    _∈_        to _[∈]_        ;
    _∉_        to _[∉]_        ;
    All        to All[]        ;
    Any        to Any[]        ;
    ∉→¬∈       to [∉]→¬[∈]     ;
    ¬∈→∉       to ¬[∈]→[∉]     ;
    Decidable∈ to Decidable[∈] ;
    decide∈    to decide[∈]    )

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

all¬→¬any : {A : Set} → {_≟_ : Decidable≡ A}
                → (P : A → Set) → (αs : Ensemble _≟_) → (xs : List A)
                → All (¬_ ∘ P) ⟨ αs ∖ xs ⟩ → ¬(Any P ⟨ αs ∖ xs ⟩)
all¬→¬any P ∅         xs all¬            ()
all¬→¬any P (α ∷ αs)  xs (¬Pα ∷ all¬)    [ Pα , α∉xs ] = ¬Pα Pα
all¬→¬any P (α ∷ αs)  xs (α∈xs -∷ all¬)  [ Pα , α∉xs ] = [∉]→¬[∈] α xs α∉xs α∈xs
all¬→¬any P (α ∷ αs)  xs (x ∷ all¬)      (.α ∷ any)    = all¬→¬any P αs xs all¬ any
all¬→¬any P (α ∷ αs)  xs (x -∷ all¬)     (.α ∷ any)    = all¬→¬any P αs xs all¬ any
all¬→¬any P (αs - α)  xs (.α ~ all¬)     (.α ~ any)    = all¬→¬any P αs (α ∷ xs) all¬ any
all¬→¬any P (αs ∪ βs) xs (allα¬ ∪ allβ¬) (.αs ∣∪ any)  = all¬→¬any P βs xs allβ¬ any
all¬→¬any P (αs ∪ βs) xs (allα¬ ∪ allβ¬) (any ∪∣ .βs)  = all¬→¬any P αs xs allα¬ any

¬any→all¬ : {A : Set} → {_≟_ : Decidable≡ A}
                → (P : A → Set) → (αs : Ensemble _≟_) → (xs : List A)
                → ¬(Any P ⟨ αs ∖ xs ⟩) → All (¬_ ∘ P) ⟨ αs ∖ xs ⟩
¬any→all¬ P ∅ xs ¬any = ∅
¬any→all¬ {_} {_≟_} P (α ∷ αs) xs ¬any with decide[∈] _≟_ α xs
...           | yes α∈xs = α∈xs -∷ ¬any→all¬ P αs xs λ any → ¬any (α ∷ any)
...           | no ¬α∈xs = (λ Pα → ¬any [ Pα , ¬[∈]→[∉] α xs ¬α∈xs ])
                           ∷ ¬any→all¬ P αs xs λ any → ¬any (α ∷ any)
¬any→all¬ P (αs - α)  xs ¬any = α ~ ¬any→all¬ P αs (α ∷ xs) λ any → ¬any (α ~ any)
¬any→all¬ P (αs ∪ βs) xs ¬any = ¬any→all¬ P αs xs (λ z → ¬any (z ∪∣ βs))
                                    ∪ ¬any→all¬ P βs xs λ z → ¬any (αs ∣∪ z)


---- Check that _∉_ is equivalent to ¬ ∘ _∈_
∉→¬∈ : {A : Set} {_≟_ : Decidable≡ A} → (x : A) → (xs : Ensemble _≟_) → x ∉ xs → ¬(x ∈ xs)
∉→¬∈ x xs x∉xs = all¬→¬any (_≡_ x) xs [] x∉xs

¬∈→∉ : {A : Set} {_≟_ : Decidable≡ A} → (x : A) → (xs : Ensemble _≟_) → ¬(x ∈ xs) → x ∉ xs
¬∈→∉ x xs ¬x∈xs = ¬any→all¬ (_≡_ x) xs [] ¬x∈xs


-- Decidability of _∈_ follows from decidability of _≡_

Decidable∈ : {A : Set} → (Decidable≡ A) → Set
Decidable∈ {A} _≟_ = (α : A) → (αs : Ensemble _≟_) → Dec (α ∈ αs)

private lemma:¬∈∪ : ∀{A} {_≟_ : Decidable≡ A} {α : A} {αs βs : Ensemble _≟_}
                    → ¬(α ∈ αs) → ¬(α ∈ βs) → ¬(α ∈ (αs ∪ βs))
lemma:¬∈∪ ¬α∈αs ¬α∈βs (αs ∣∪ α∈∪) = ¬α∈βs α∈∪
lemma:¬∈∪ ¬α∈αs ¬α∈βs (α∈∪ ∪∣ βs) = ¬α∈αs α∈∪

decide∈ : {A : Set} → (_≟_ : Decidable≡ A) → Decidable∈ _≟_
decide∈ _≟_ α ∅ = no (λ ())
decide∈ _≟_ α (β ∷ αs) = {!   !}
decide∈ _≟_ α (αs - x) with α ≟ x
decide∈ _≟_ α (αs - x) | yes α≡x = no {!   !}
decide∈ _≟_ α (αs - x) | no  α≢x = no {!   !}
decide∈ _≟_ α (αs ∪ βs) with decide∈ _≟_ α αs
decide∈ _≟_ α (αs ∪ βs) | yes α∈αs = yes (α∈αs ∪∣ βs)
decide∈ _≟_ α (αs ∪ βs) | no ¬α∈αs with decide∈ _≟_ α βs
decide∈ _≟_ α (αs ∪ βs) | no ¬α∈αs | yes α∈βs = yes (αs ∣∪ α∈βs)
decide∈ _≟_ α (αs ∪ βs) | no ¬α∈αs | no ¬α∈βs = no (lemma:¬∈∪ ¬α∈αs ¬α∈βs)

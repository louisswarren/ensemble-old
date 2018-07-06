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

_∈_∖_ : {A : Set} {_≟_ : Decidable≡ A} → A → Ensemble _≟_ → List A → Set
α ∈ αs ∖ xs = Any (α ≡_) ⟨ αs ∖ xs ⟩

_∈_ : {A : Set} {_≟_ : Decidable≡ A} → A → Ensemble _≟_ → Set
α ∈ αs = α ∈ αs ∖ []

_∉_∖_ : {A : Set} {_≟_ : Decidable≡ A} → A → Ensemble _≟_ → List A → Set
α ∉ αs ∖ xs = All α ≢_ ⟨ αs ∖ xs ⟩

_∉_ : {A : Set} {_≟_ : Decidable≡ A} → A → Ensemble _≟_ → Set
α ∉ αs = α ∉ αs ∖ []


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


-- All and Any are decidable
-- Decidability of _∈_ follows from decidability of _≡_.

-- These proofs need a total cleanup, mostly just generated with agda's auto

private lemma:all∪α : {A : Set} {_≟_ : Decidable≡ A} {f : A → Set}
                    → (P : Decidable f) → (αs βs : Ensemble _≟_) → (xs : List A)
                    → ¬(All f ⟨ αs ∖ xs ⟩) → ¬(All f ⟨ αs ∪ βs ∖ xs ⟩)
lemma:all∪α P αs βs xs ¬allαs (allαs ∪ allβs) = ¬allαs allαs

private lemma:all∪β : {A : Set} {_≟_ : Decidable≡ A} {f : A → Set}
                    → (P : Decidable f) → (αs βs : Ensemble _≟_) → (xs : List A)
                    → ¬(All f ⟨ βs ∖ xs ⟩) → ¬(All f ⟨ αs ∪ βs ∖ xs ⟩)
lemma:all∪β P αs βs xs ¬allβs (allαs ∪ allβs) = ¬allβs allβs


decidableAll : {A : Set} {_≟_ : Decidable≡ A} {f : A → Set}
               → (P : Decidable f) → (αs : Ensemble _≟_) → (xs : List A)
               → Dec (All f ⟨ αs ∖ xs ⟩)
decidableAll P ∅         xs = yes ∅
decidableAll P (α ∷ αs)  xs with P α
decidableAll P (α ∷ αs) xs | yes x with decidableAll P αs xs
decidableAll P (α ∷ αs) xs | yes x | yes x₁ = yes (x ∷ x₁)
decidableAll {_} {_≟_} {f} P (α ∷ αs) xs | yes x | no x₁ = no ¬all
                                             where
                                             ¬all : (All f ⟨ α ∷ αs ∖ xs ⟩) → ⊥
                                             ¬all (x₂ ∷ all) = x₁ all
                                             ¬all (x₂ -∷ all) = x₁ all
decidableAll {_} {_≟_} {f} P (α ∷ αs) xs | no ¬fα with decide[∈] _≟_ α xs
decidableAll {_} {_≟_} {f} P (α ∷ αs) xs | no ¬fα | yes x with decidableAll P αs xs
decidableAll {_} {_≟_} {f} P (α ∷ αs) xs | no ¬fα | yes x | yes x₁ = yes (x -∷ x₁)
decidableAll {_} {_≟_} {f} P (α ∷ αs) xs | no ¬fα | yes x | no x₁ = no ¬all
                                                                    where
                                                                    ¬all : (x₂ : All f ⟨ α ∷ αs ∖ xs ⟩) → ⊥
                                                                    ¬all (x₂ ∷ all) = ¬fα x₂
                                                                    ¬all (x₂ -∷ all) = x₁ all
decidableAll {_} {_≟_} {f} P (α ∷ αs) xs | no ¬fα | no x = no ¬all
                                    where
                                    ¬all : ¬(All f ⟨ α ∷ αs ∖ xs ⟩)
                                    ¬all (x₁ ∷ p) = ¬fα x₁
                                    ¬all (x₁ -∷ p) = x x₁
decidableAll P (αs - α)  xs with decidableAll P αs (α ∷ xs)
decidableAll P (αs - α) xs | yes x = yes (α ~ x)
decidableAll {_} {_} {f} P (αs - α) xs | no x = no ¬all
                                    where
                                    ¬all : (All f ⟨ αs - α ∖ xs ⟩) → ⊥
                                    ¬all (x₁ ~ all) = x all
decidableAll P (αs ∪ βs) xs with decidableAll P αs xs
decidableAll P (αs ∪ βs) xs | yes allαs with decidableAll P βs xs
decidableAll P (αs ∪ βs) xs | yes allαs | yes allβs = yes (allαs ∪ allβs)
decidableAll P (αs ∪ βs) xs | yes allαs | no ¬allβs = no (lemma:all∪β P αs βs xs ¬allβs)
decidableAll P (αs ∪ βs) xs | no ¬allαs = no (lemma:all∪α P αs βs xs ¬allαs)

Decidable∈ : {A : Set} → (Decidable≡ A) → Set
Decidable∈ {A} _≟_ = (α : A) → (αs : Ensemble _≟_) → Dec (α ∈ αs)



decidableAny : {A : Set} {_≟_ : Decidable≡ A} {f : A → Set}
               → (P : Decidable f) → (αs : Ensemble _≟_) → (xs : List A)
               → Dec (Any f ⟨ αs ∖ xs ⟩)
decidableAny P ∅ xs = no (λ ())
decidableAny P (x ∷ αs) xs with P x
decidableAny {_} {_≟_} P (x ∷ αs) xs | yes x₁ with decide[∈] _≟_ x xs
decidableAny {_} {_≟_} P (x ∷ αs) xs | yes x₁ | yes x₂ with decidableAny P αs xs
decidableAny {_} {_≟_} P (x ∷ αs) xs | yes x₁ | yes x₂ | yes x₃ = yes (x ∷ x₃)
decidableAny {_} {_≟_} {f} P (x ∷ αs) xs | yes x₁ | yes x₂ | no x₃ = no ¬any
                                                                     where
                                                                     ¬any : (Any f ⟨ x ∷ αs ∖ xs ⟩) → ⊥
                                                                     ¬any [ x₅ , x₄ ] = [∉]→¬[∈] x xs x₄ x₂
                                                                     ¬any (α ∷ any) = x₃ any
decidableAny {_} {_≟_} P (x ∷ αs) xs | yes x₁ | no x₂ = yes [ x₁ , ¬[∈]→[∉] x xs x₂ ]
decidableAny P (x ∷ αs) xs | no x₁ with decidableAny P αs xs
decidableAny P (x ∷ αs) xs | no x₁ | yes x₂ = yes (x ∷ x₂)
decidableAny {_} {_} {f} P (x ∷ αs) xs | no x₁ | no x₂ = no ¬any
                                                         where
                                                         ¬any : (x₃ : Any f ⟨ x ∷ αs ∖ xs ⟩) → ⊥
                                                         ¬any [ x , x₃ ] = x₁ x
                                                         ¬any (α ∷ any) = x₂ any
decidableAny P (αs - x) xs with decidableAny P αs (x ∷ xs)
decidableAny P (αs - x) xs | yes x₁ = yes (x ~ x₁)
decidableAny {_} {_} {f} P (αs - x) xs | no x₁ = no ¬any
                                     where
                                     ¬any : (x₂ : Any f ⟨ αs - x ∖ xs ⟩) → ⊥
                                     ¬any (x ~ any) = x₁ any
decidableAny P (αs ∪ βs) xs with decidableAny P αs xs
decidableAny P (αs ∪ βs) xs | yes x = yes (x ∪∣ βs)
decidableAny P (αs ∪ βs) xs | no x with decidableAny P βs xs
decidableAny P (αs ∪ βs) xs | no x | yes x₁ = yes (αs ∣∪ x₁)
decidableAny {_} {_} {f} P (αs ∪ βs) xs | no x | no x₁ = no ¬any
                                             where
                                             ¬any : (Any f ⟨ αs ∪ βs ∖ xs ⟩) → ⊥
                                             ¬any (αs ∣∪ any) = x₁ any
                                             ¬any (any ∪∣ βs) = x any

decide∈ : {A : Set} → (_≟_ : Decidable≡ A) → (α : A) → (αs : Ensemble _≟_) → Dec (α ∈ αs)
decide∈ _≟_ α αs with decidableAny (α ≟_) αs []
decide∈ _≟_ α αs | yes x = yes x
decide∈ _≟_ α αs | no x = no x


_⊂_ : {A : Set} {_≟_ : Decidable≡ A} → (αs βs : Ensemble _≟_) → Set
αs ⊂ βs = ∀ x → x ∈ αs → x ∈ βs

isEmpty : {A : Set} {_≟_ : Decidable≡ A} → (αs : Ensemble _≟_) → Set
isEmpty αs = αs ⊂ ∅

uninhabited : {A : Set} {_≟_ : Decidable≡ A} → (αs : Ensemble _≟_) → Set
uninhabited αs = All (λ _ → ⊥) αs

--decidableUninhabited : {A : Set} → {_≟_ : Decidable≡ A}
--                       → (αs : Ensemble _≟_) → Dec (uninhabited αs)
--decidableUninhabited ∅ = yes ∅
--decidableUninhabited (α ∷ αs) = no φ
--                                where
--                                φ : ¬(All (λ _ → ⊥) (α ∷ αs))
--                                φ (x ∷ p) = x
--                                φ (() -∷ p)
--decidableUninhabited (αs - x) = {! decidableUninhabited  !}
--decidableUninhabited (αs ∪ βs) = {!   !}

open import Agda.Builtin.Equality

open import Decidable
open import List
  renaming (
    _∈_        to _[∈]_        ;
    _∉_        to _[∉]_        ;
    All        to All[]        ;
    Any        to Any[]        ;
    any        to any[]        ;
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
all¬→¬any P (α ∷ αs)  xs (α∈xs -∷ all¬)  [ Pα , α∉xs ] = α∉xs α∈xs
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
...           | no  α∉xs = (λ Pα → ¬any [ Pα , α∉xs ])
                           ∷ ¬any→all¬ P αs xs λ any → ¬any (α ∷ any)
¬any→all¬ P (αs - α)  xs ¬any = α ~ ¬any→all¬ P αs (α ∷ xs) λ any → ¬any (α ~ any)
¬any→all¬ P (αs ∪ βs) xs ¬any = ¬any→all¬ P αs xs (λ z → ¬any (z ∪∣ βs))
                                    ∪ ¬any→all¬ P βs xs λ z → ¬any (αs ∣∪ z)


-- Some useful lemmae for "lifting" all and any
¬all∷∣ : {A : Set} {_≟_ : Decidable≡ A}
         → {P : A → Set} → {α : A} → {αs : Ensemble _≟_} → {xs : List A}
         → ¬(P α) → ¬(α [∈] xs) →  ¬(All P ⟨ α ∷ αs ∖ xs ⟩)
¬all∷∣ {_} {_} {P} {α} {αs} {xs} ¬Pα α∉xs (x ∷ all)  = ¬Pα x
¬all∷∣ {_} {_} {P} {α} {αs} {xs} ¬Pα α∉xs (x -∷ all) = α∉xs x

¬all∣∷ : {A : Set} {_≟_ : Decidable≡ A}
         → {P : A → Set} → {α : A} → {αs : Ensemble _≟_} → {xs : List A}
         → ¬(All P ⟨ αs ∖ xs ⟩) →  ¬(All P ⟨ α ∷ αs ∖ xs ⟩)
¬all∣∷ {_} {_} {P} {α} {αs} {xs} ¬all (x ∷ all)  = ¬all all
¬all∣∷ {_} {_} {P} {α} {αs} {xs} ¬all (x -∷ all) = ¬all all

¬all- : {A : Set} {_≟_ : Decidable≡ A}
         → {P : A → Set} → {α : A} → {αs : Ensemble _≟_} → {xs : List A}
         → ¬(All P ⟨ αs ∖ α ∷ xs ⟩) → ¬(All P ⟨ αs - α ∖ xs ⟩)
¬all- {_} {_} {P} {.x} {αs} {xs} ¬all (x ~ all) = ¬all all

¬all∪∣ : {A : Set} {_≟_ : Decidable≡ A}
         → {P : A → Set} → {αs βs : Ensemble _≟_} → {xs : List A}
         → ¬(All P ⟨ αs ∖ xs ⟩) → ¬(All P ⟨ αs ∪ βs ∖ xs ⟩)
¬all∪∣ {_} {_} {P} {αs} {βs} {xs} ¬all (allα ∪ allβ) = ¬all allα

¬all∣∪ : {A : Set} {_≟_ : Decidable≡ A}
         → {P : A → Set} → {αs βs : Ensemble _≟_} → {xs : List A}
         → ¬(All P ⟨ βs ∖ xs ⟩) → ¬(All P ⟨ αs ∪ βs ∖ xs ⟩)
¬all∣∪ {_} {_} {P} {αs} {βs} {xs} ¬all (allα ∪ allβ) = ¬all allβ


¬any¬∷ : {A : Set} {_≟_ : Decidable≡ A}
        → {P : A → Set} → {α : A} → {αs : Ensemble _≟_} → {xs : List A}
        → ¬(P α) → ¬(Any P ⟨ αs ∖ xs ⟩) → ¬(Any P ⟨ α ∷ αs ∖ xs ⟩)
¬any¬∷ {_} {_} {P} {α} {αs} {xs} ¬Pα ¬any [ Pα , _ ] = ¬Pα Pα
¬any¬∷ {_} {_} {P} {α} {αs} {xs} ¬Pα ¬any (α ∷ any)  = ¬any any

¬any∉∷ : {A : Set} {_≟_ : Decidable≡ A}
        → {P : A → Set} → {α : A} → {αs : Ensemble _≟_} → {xs : List A}
        → (α [∈] xs) → ¬(Any P ⟨ αs ∖ xs ⟩) → ¬(Any P ⟨ α ∷ αs ∖ xs ⟩)
¬any∉∷ {_} {_} {P} {α} {αs} {xs} α∈xs ¬any [ Pα , α∉xs ] = α∉xs α∈xs
¬any∉∷ {_} {_} {P} {α} {αs} {xs} α∈xs ¬any (α ∷ any)     = ¬any any

¬any- : {A : Set} {_≟_ : Decidable≡ A}
         → {P : A → Set} → {α : A} → {αs : Ensemble _≟_} → {xs : List A}
         → ¬(Any P ⟨ αs ∖ α ∷ xs ⟩) → ¬(Any P ⟨ αs - α ∖ xs ⟩)
¬any- {_} {_} {P} {.x} {αs} {xs} ¬any (x ~ any) = ¬any any

¬any∪ : {A : Set} {_≟_ : Decidable≡ A}
         → {P : A → Set} → {αs βs : Ensemble _≟_} → {xs : List A}
         → ¬(Any P ⟨ αs ∖ xs ⟩) → ¬(Any P ⟨ βs ∖ xs ⟩)
         → ¬(Any P ⟨ αs ∪ βs ∖ xs ⟩)
¬any∪ {_} {_} {P} {αs₁} {βs} {xs} ¬anyαs ¬anyβs (αs₁ ∣∪ any) = ¬anyβs any
¬any∪ {_} {_} {P} {αs} {βs₁} {xs} ¬anyαs ¬anyβs (any ∪∣ βs₁) = ¬anyαs any

---- Check that _∉_ is equivalent to ¬ ∘ _∈_
∉→¬∈ : {A : Set} {_≟_ : Decidable≡ A} → (x : A) → (xs : Ensemble _≟_) → x ∉ xs → ¬(x ∈ xs)
∉→¬∈ x xs x∉xs = all¬→¬any (_≡_ x) xs [] x∉xs

¬∈→∉ : {A : Set} {_≟_ : Decidable≡ A} → (x : A) → (xs : Ensemble _≟_) → ¬(x ∈ xs) → x ∉ xs
¬∈→∉ x xs ¬x∈xs = ¬any→all¬ (_≡_ x) xs [] ¬x∈xs


-- All and Any are decidable over decidable predicates.
-- Decidability of _∈_ follows from decidability of _≡_.


all?_⟨_∖_⟩ : {A : Set} {_≟_ : Decidable≡ A} {P : A → Set}
               → (P? : Decidable P) → (αs : Ensemble _≟_) → (xs : List A)
               → Dec (All P ⟨ αs ∖ xs ⟩)
all? P? ⟨ ∅ ∖ xs ⟩ = yes ∅
all? P? ⟨ α ∷ αs ∖ xs ⟩ with all? P? ⟨ αs ∖ xs ⟩
...                                 | no ¬all = no (¬all∣∷ ¬all)
all?_⟨_∖_⟩ {_} {_≟_} P? (α ∷ αs) xs | yes all with decide[∈] _≟_ α xs
...                                           | yes α∈xs = yes (α∈xs -∷ all)
...                                           | no  α∉xs with P? α
...                                                      | yes Pα = yes (Pα ∷ all)
...                                                      | no ¬Pα = no (¬all∷∣ ¬Pα α∉xs)
all? P? ⟨ αs - α  ∖ xs ⟩ with all? P? ⟨ αs ∖ α ∷ xs ⟩
...                      | yes all = yes (α ~ all)
...                      | no ¬all = no (¬all- ¬all)
all? P? ⟨ αs ∪ βs ∖ xs ⟩ with all? P? ⟨ αs ∖ xs ⟩
...                      | no ¬allαs = no (¬all∪∣ ¬allαs)
...                      | yes allαs with all? P? ⟨ βs ∖ xs ⟩
...                                  | yes allβs = yes (allαs ∪ allβs)
...                                  | no ¬allβs = no (¬all∣∪ ¬allβs)


any?_⟨_∖_⟩ : {A : Set} {_≟_ : Decidable≡ A} {P : A → Set}
               → (P? : Decidable P) → (αs : Ensemble _≟_) → (xs : List A)
               → Dec (Any P ⟨ αs ∖ xs ⟩)
any? P? ⟨ ∅ ∖ xs ⟩ = no (λ ())
any? P? ⟨ α ∷ αs  ∖ xs ⟩ with any? P? ⟨ αs ∖ xs ⟩
...                                 | yes any = yes (α ∷ any)
any?_⟨_∖_⟩ {_} {_≟_} P? (α ∷ αs) xs | no ¬any with decide[∈] _≟_ α xs
...                                           | yes α∈xs = no (¬any∉∷ α∈xs ¬any)
...                                           | no  α∉xs with P? α
...                                                      | yes Pα = yes [ Pα , α∉xs ]
...                                                      | no ¬Pα = no (¬any¬∷ ¬Pα ¬any)
any? P? ⟨ αs - α  ∖ xs ⟩ with any? P? ⟨ αs ∖ α ∷ xs ⟩
...                      | yes any = yes (α ~ any)
...                      | no ¬any = no (¬any- ¬any)
any? P? ⟨ αs ∪ βs ∖ xs ⟩ with any? P? ⟨ αs ∖ xs ⟩
...                      | yes anyαs = yes (anyαs ∪∣ βs)
...                      | no ¬anyαs with any? P? ⟨ βs ∖ xs ⟩
...                                  | yes anyβs = yes (αs ∣∪ anyβs)
...                                  | no ¬anyβs = no (¬any∪ ¬anyαs ¬anyβs)


decide∈ : {A : Set} → (_≟_ : Decidable≡ A) → (α : A) → (αs : Ensemble _≟_) → Dec (α ∈ αs)
decide∈ _≟_ α αs with any? α ≟_ ⟨ αs ∖ [] ⟩
decide∈ _≟_ α αs | yes any = yes any
decide∈ _≟_ α αs | no ¬any = no ¬any



_⊂_ : {A : Set} {_≟_ : Decidable≡ A} → (αs βs : Ensemble _≟_) → Set
αs ⊂ βs = All (_∈ βs) αs

_⊂?_ : {A : Set} {_≟_ : Decidable≡ A} → (αs βs : Ensemble _≟_) → Dec (αs ⊂ βs)
_⊂?_ {A} {_≟_} αs βs = all? (λ x → any? _≟_ x ⟨ βs ∖ [] ⟩) ⟨ αs ∖ [] ⟩

Empty : {A : Set} {_≟_ : Decidable≡ A} → (αs : Ensemble _≟_) → Set
Empty αs = αs ⊂ ∅

empty? : {A : Set} {_≟_ : Decidable≡ A} → (αs : Ensemble _≟_) → Dec (Empty αs)
empty? αs = all? (λ x → no (λ ())) ⟨ αs ∖ [] ⟩

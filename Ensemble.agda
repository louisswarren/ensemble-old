open import Agda.Builtin.Equality

open import Decidable
open import List
  renaming (
    _∈_        to _[∈]_        ;
    _∉_        to _[∉]_        ;
    All        to All[]        ;
    headAll    to headAll[]    ;
    tailAll    to tailAll[]    ;
    hereAny    to hereAny[]    ;
    laterAny   to laterAny[]   ;
    Any        to Any[]        ;
    any        to any[]        ;
    decide∈    to decide[∈]    )

open import Functools


-- An ensemble is like a decidable finite set, but we do not define a
-- comprehension constructor.

data Ensemble {A : Set} (eq : Decidable≡ A) : Set where
  ∅   : Ensemble eq
  _∷_ : A           → Ensemble eq → Ensemble eq
  _-_ : Ensemble eq → A           → Ensemble eq
  _∪_ : Ensemble eq → Ensemble eq → Ensemble eq


data All_⟨_∖_⟩ {A : Set} {eq : Decidable≡ A} (P : Pred A) : Ensemble eq → List A → Set where
  ∅    : ∀{xs}       → All P ⟨ ∅ ∖ xs ⟩
  _∷_  : ∀{αs xs α}  → P α      → All P ⟨ αs ∖ xs ⟩ → All P ⟨ α ∷ αs ∖ xs ⟩
  _-∷_ : ∀{αs xs α}  → α [∈] xs → All P ⟨ αs ∖ xs ⟩ → All P ⟨ α ∷ αs ∖ xs ⟩
  _~_  : ∀{αs xs}    → ∀ x → All P ⟨ αs ∖ x ∷ xs ⟩ → All P ⟨ αs - x ∖ xs ⟩
  _∪_  : ∀{αs βs xs} → All P ⟨ αs ∖ xs ⟩ → All P ⟨ βs ∖ xs ⟩ → All P ⟨ αs ∪ βs ∖ xs ⟩

All : {A : Set} {_≟_ : Decidable≡ A} → (P : A → Set) → Ensemble _≟_ → Set
All P αs = All P ⟨ αs ∖ [] ⟩

headAll : ∀{A α xs} {eq : Decidable≡ A} {αs : Ensemble eq} {P : Pred A}
          → All P ⟨ α ∷ αs ∖ xs ⟩ → α [∉] xs → P α
headAll (Pα ∷ al)    α∉xs = Pα
headAll (α∈xs -∷ al) α∉xs = ⊥-elim (α∉xs α∈xs)

tailAll : ∀{A α xs} {eq : Decidable≡ A} {αs : Ensemble eq} {P : Pred A}
          → All P ⟨ α ∷ αs ∖ xs ⟩ → All P ⟨ αs ∖ xs ⟩
tailAll (_  ∷ ∀αs∖xsP) = ∀αs∖xsP
tailAll (_ -∷ ∀αs∖xsP) = ∀αs∖xsP

plusAll : ∀{A α xs} {eq : Decidable≡ A} {αs : Ensemble eq} {P : Pred A}
          → All P ⟨ αs - α ∖ xs ⟩ → All P ⟨ αs ∖ α ∷ xs ⟩
plusAll (_ ~ ∀αs∖α∷xs) = ∀αs∖α∷xs

leftAll : ∀{A xs} {eq : Decidable≡ A} {αs βs : Ensemble eq} {P : Pred A}
          → All P ⟨ αs ∪ βs ∖ xs ⟩ → All P ⟨ αs ∖ xs ⟩
leftAll (∀αs∖xsP ∪ _) = ∀αs∖xsP

rightAll : ∀{A xs} {eq : Decidable≡ A} {αs βs : Ensemble eq} {P : Pred A}
          → All P ⟨ αs ∪ βs ∖ xs ⟩ → All P ⟨ βs ∖ xs ⟩
rightAll (_ ∪ ∀βs∖xsP) = ∀βs∖xsP


data Any_⟨_∖_⟩ {A : Set} {eq : Decidable≡ A} (P : Pred A) : Ensemble eq → List A → Set where
  [_,_] : ∀{αs xs α} → P α  → α [∉] xs              → Any P ⟨ α ∷ αs ∖ xs ⟩
  _∷_   : ∀{αs xs}   → ∀ α  → Any P ⟨ αs ∖ xs ⟩     → Any P ⟨ α ∷ αs ∖ xs ⟩
  _~_   : ∀{αs xs}   → ∀ x  → Any P ⟨ αs ∖ x ∷ xs ⟩ → Any P ⟨ αs - x ∖ xs ⟩
  _∣∪_  : ∀{βs xs}   → ∀ αs → Any P ⟨ βs ∖ xs ⟩     → Any P ⟨ αs ∪ βs ∖ xs ⟩
  _∪∣_  : ∀{αs xs}   → Any P ⟨ αs ∖ xs ⟩     → ∀ βs → Any P ⟨ αs ∪ βs ∖ xs ⟩

Any : {A : Set} {eq : Decidable≡ A} → (P : Pred A) → Ensemble eq → Set
Any P αs = Any P ⟨ αs ∖ [] ⟩

hereAny : ∀{A α xs} {eq : Decidable≡ A} {αs : Ensemble eq} {P : Pred A}
          → Any P ⟨ α ∷ αs ∖ xs ⟩ → ¬ Any P ⟨ αs ∖ xs ⟩ → P α
hereAny [ Pα , _ ]    ¬∃αs∖xsP = Pα
hereAny (_ ∷ ∃αs∖xsP) ¬∃αs∖xsP = ⊥-elim (¬∃αs∖xsP ∃αs∖xsP)

laterAny : ∀{A α xs} {eq : Decidable≡ A} {αs : Ensemble eq} {P : Pred A}
          → Any P ⟨ α ∷ αs ∖ xs ⟩ → ¬(P α) → Any P ⟨ αs ∖ xs ⟩
laterAny [ Pα , _ ]    ¬Pα = ⊥-elim (¬Pα Pα)
laterAny (_ ∷ ∃αs∖xsP) ¬Pα = ∃αs∖xsP

thereAny : ∀{A α xs} {eq : Decidable≡ A} {αs : Ensemble eq} {P : Pred A}
          → Any P ⟨ α ∷ αs ∖ xs ⟩ → α [∈] xs → Any P ⟨ αs ∖ xs ⟩
thereAny [ _ , α[∉]xs ] α[∈]xs = ⊥-elim (α[∉]xs α[∈]xs)
thereAny (_ ∷ ∃αs∖xs)   α[∈]xs = ∃αs∖xs

plusAny : ∀{A α xs} {eq : Decidable≡ A} {αs : Ensemble eq} {P : Pred A}
          → Any P ⟨ αs - α ∖ xs ⟩ → Any P ⟨ αs ∖ α ∷ xs ⟩
plusAny (_ ~ ∃αs∖α∷xs) = ∃αs∖α∷xs

leftAny : ∀{A xs} {eq : Decidable≡ A} {αs βs : Ensemble eq} {P : Pred A}
          → Any P ⟨ αs ∪ βs ∖ xs ⟩ → ¬ Any P ⟨ βs ∖ xs ⟩ → Any P ⟨ αs ∖ xs ⟩
leftAny (αs      ∣∪  ∃βs∖xsP) ¬∃βs∖xsP = ⊥-elim (¬∃βs∖xsP ∃βs∖xsP)
leftAny (∃αs∖xsP  ∪∣ βs)      ¬∃βs∖xsP = ∃αs∖xsP

rightAny : ∀{A xs} {eq : Decidable≡ A} {αs βs : Ensemble eq} {P : Pred A}
          → Any P ⟨ αs ∪ βs ∖ xs ⟩ → ¬ Any P ⟨ αs ∖ xs ⟩ → Any P ⟨ βs ∖ xs ⟩
rightAny (αs      ∣∪  ∃βs∖xsP) ¬∃αs∖xsP = ∃βs∖xsP
rightAny (∃αs∖xsP  ∪∣ βs)      ¬∃αs∖xsP = ⊥-elim (¬∃αs∖xsP ∃αs∖xsP)


_∈_∖_ : {A : Set} {_≟_ : Decidable≡ A} → A → Ensemble _≟_ → List A → Set
α ∈ αs ∖ xs = Any (α ≡_) ⟨ αs ∖ xs ⟩

_∈_ : {A : Set} {_≟_ : Decidable≡ A} → A → Ensemble _≟_ → Set
α ∈ αs = α ∈ αs ∖ []

_∉_∖_ : {A : Set} {_≟_ : Decidable≡ A} → A → Ensemble _≟_ → List A → Set
α ∉ αs ∖ xs = ¬(α ∈ αs ∖ xs)

_∉_ : {A : Set} {_≟_ : Decidable≡ A} → A → Ensemble _≟_ → Set
α ∉ αs = ¬(α ∈ αs)


---- Prove that ∀α ¬Pα is equivalent to ¬∃α Pα
--
--all¬→¬any : {A : Set} → {_≟_ : Decidable≡ A}
--                → (P : A → Set) → (αs : Ensemble _≟_) → (xs : List A)
--                → All (¬_ ∘ P) ⟨ αs ∖ xs ⟩ → ¬(Any P ⟨ αs ∖ xs ⟩)
--all¬→¬any P ∅         xs all¬            ()
--all¬→¬any P (α ∷ αs)  xs (¬Pα ∷ all¬)    [ Pα , α∉xs ] = ¬Pα Pα
--all¬→¬any P (α ∷ αs)  xs (α∈xs -∷ all¬)  [ Pα , α∉xs ] = α∉xs α∈xs
--all¬→¬any P (α ∷ αs)  xs (x ∷ all¬)      (.α ∷ any)    = all¬→¬any P αs xs all¬ any
--all¬→¬any P (α ∷ αs)  xs (x -∷ all¬)     (.α ∷ any)    = all¬→¬any P αs xs all¬ any
--all¬→¬any P (αs - α)  xs (.α ~ all¬)     (.α ~ any)    = all¬→¬any P αs (α ∷ xs) all¬ any
--all¬→¬any P (αs ∪ βs) xs (allα¬ ∪ allβ¬) (.αs ∣∪ any)  = all¬→¬any P βs xs allβ¬ any
--all¬→¬any P (αs ∪ βs) xs (allα¬ ∪ allβ¬) (any ∪∣ .βs)  = all¬→¬any P αs xs allα¬ any
--
--¬any→all¬ : {A : Set} → {_≟_ : Decidable≡ A}
--                → (P : A → Set) → (αs : Ensemble _≟_) → (xs : List A)
--                → ¬(Any P ⟨ αs ∖ xs ⟩) → All (¬_ ∘ P) ⟨ αs ∖ xs ⟩
--¬any→all¬ P ∅ xs ¬any = ∅
--¬any→all¬ {_} {_≟_} P (α ∷ αs) xs ¬any with decide[∈] _≟_ α xs
--...           | yes α∈xs = α∈xs -∷ ¬any→all¬ P αs xs λ any → ¬any (α ∷ any)
--...           | no  α∉xs = (λ Pα → ¬any [ Pα , α∉xs ])
--                           ∷ ¬any→all¬ P αs xs λ any → ¬any (α ∷ any)
--¬any→all¬ P (αs - α)  xs ¬any = α ~ ¬any→all¬ P αs (α ∷ xs) λ any → ¬any (α ~ any)
--¬any→all¬ P (αs ∪ βs) xs ¬any = ¬any→all¬ P αs xs (λ z → ¬any (z ∪∣ βs))
--                                    ∪ ¬any→all¬ P βs xs λ z → ¬any (αs ∣∪ z)
--
--
------ Check that _∉_ is equivalent to ¬ ∘ _∈_
--∉→¬∈ : {A : Set} {_≟_ : Decidable≡ A} → (x : A) → (xs : Ensemble _≟_) → x ∉ xs → ¬(x ∈ xs)
--∉→¬∈ x xs x∉xs = all¬→¬any (_≡_ x) xs [] x∉xs
--
--¬∈→∉ : {A : Set} {_≟_ : Decidable≡ A} → (x : A) → (xs : Ensemble _≟_) → ¬(x ∈ xs) → x ∉ xs
--¬∈→∉ x xs ¬x∈xs = ¬any→all¬ (_≡_ x) xs [] ¬x∈xs
--
--
---- All and Any are decidable over decidable predicates.
---- Decidability of _∈_ follows from decidability of _≡_.
--
--
all_⟨_∖_⟩ : {A : Set} {_≟_ : Decidable≡ A} {P : Pred A}
              → (P? : Decidable P) → (αs : Ensemble _≟_) → (xs : List A)
              → Dec (All P ⟨ αs ∖ xs ⟩)
all P? ⟨ ∅ ∖ xs ⟩ = yes ∅
all P? ⟨ α ∷ αs ∖ xs ⟩ with all P? ⟨ αs ∖ xs ⟩
...                                | no ¬all = no λ φ → ¬all (tailAll φ)
all_⟨_∖_⟩ {_} {_≟_} P? (α ∷ αs) xs | yes all with decide[∈] _≟_ α xs
...                                          | yes α∈xs = yes (α∈xs -∷ all)
...                                          | no  α∉xs with P? α
...                                                     | yes Pα = yes (Pα ∷ all)
...                                                     | no ¬Pα = no λ φ → ¬Pα (headAll φ α∉xs)
all P? ⟨ αs - α  ∖ xs ⟩ with all P? ⟨ αs ∖ α ∷ xs ⟩
...                     | yes all = yes (α ~ all)
...                     | no ¬all = no λ φ → ¬all (plusAll φ)
all P? ⟨ αs ∪ βs ∖ xs ⟩ with all P? ⟨ αs ∖ xs ⟩
...                     | no ¬allαs = no λ φ → ¬allαs (leftAll φ)
...                     | yes allαs with all P? ⟨ βs ∖ xs ⟩
...                                 | yes allβs = yes (allαs ∪ allβs)
...                                 | no ¬allβs = no λ φ → ¬allβs (rightAll φ)


any_⟨_∖_⟩ : {A : Set} {_≟_ : Decidable≡ A} {P : Pred A}
              → (P? : Decidable P) → (αs : Ensemble _≟_) → (xs : List A)
              → Dec (Any P ⟨ αs ∖ xs ⟩)
any P? ⟨ ∅ ∖ xs ⟩ = no (λ ())
any P? ⟨ α ∷ αs  ∖ xs ⟩ with any P? ⟨ αs ∖ xs ⟩
...                                | yes any = yes (α ∷ any)
any_⟨_∖_⟩ {_} {_≟_} P? (α ∷ αs) xs | no ¬any with decide[∈] _≟_ α xs
...                                          | yes α∈xs = no λ φ → ¬any (thereAny φ α∈xs)
...                                          | no  α∉xs with P? α
...                                                     | yes Pα = yes [ Pα , α∉xs ]
...                                                     | no ¬Pα = no λ φ → ¬Pα (hereAny φ ¬any)
any P? ⟨ αs - α  ∖ xs ⟩ with any P? ⟨ αs ∖ α ∷ xs ⟩
...                     | yes any = yes (α ~ any)
...                     | no ¬any = no λ φ → ¬any (plusAny φ)
any P? ⟨ αs ∪ βs ∖ xs ⟩ with any P? ⟨ αs ∖ xs ⟩
...                     | yes anyαs = yes (anyαs ∪∣ βs)
...                     | no ¬anyαs with any P? ⟨ βs ∖ xs ⟩
...                                 | yes anyβs = yes (αs ∣∪ anyβs)
...                                 | no ¬anyβs = no λ φ → ¬anyβs (rightAny φ ¬anyαs)


decide∈ : {A : Set} → (_≟_ : Decidable≡ A) → (α : A) → (αs : Ensemble _≟_) → Dec (α ∈ αs)
decide∈ _≟_ α αs with any α ≟_ ⟨ αs ∖ [] ⟩
decide∈ _≟_ α αs | yes any = yes any
decide∈ _≟_ α αs | no ¬any = no ¬any



_⊂_ : {A : Set} {_≟_ : Decidable≡ A} → (αs βs : Ensemble _≟_) → Set
αs ⊂ βs = All (_∈ βs) αs

_⊂?_ : {A : Set} {_≟_ : Decidable≡ A} → (αs βs : Ensemble _≟_) → Dec (αs ⊂ βs)
_⊂?_ {A} {_≟_} αs βs = all (λ x → any _≟_ x ⟨ βs ∖ [] ⟩) ⟨ αs ∖ [] ⟩

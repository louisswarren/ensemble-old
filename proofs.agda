open import Agda.Builtin.Equality

open import Decidable
open import List
  hiding (All ; all ; Any ; any)
  renaming (
    _∈_        to _[∈]_        ;
    _∉_        to _[∉]_        ;
    decide∈    to decide[∈]    )

open import Ensemble

All′ : {A : Set} {_≟_ : Decidable≡ A} → (P : Pred A) → (αs : Ensemble _≟_) → Set
All′ P αs = ∀ x → x ∈ αs → P x

All→All′ : {A : Set} {_≟_ : Decidable≡ A} → (P : Pred A) → (αs : Ensemble _≟_) → All P αs → All′ P αs
All→All′ P ∅ ∀αsP x ()
All→All′ P (x₁ ∷ αs) ∀αsP x x∈αs = {!   !}
All→All′ P (αs - x₁) ∀αsP x x∈αs = {!   !}
All→All′ P (αs ∪ αs₁) ∀αsP x x∈αs = {!   !}

All′→All : {A : Set} {_≟_ : Decidable≡ A} → (P : Pred A) → (αs : Ensemble _≟_) → All′ P αs → All P αs
All′→All P ∅ all′ = ∅
All′→All P (x ∷ αs) all′ = all′ x [ refl , (λ ()) ] ∷ All′→All P αs (λ x z → all′ x (_ ∷ z))
All′→All P (αs - x) all′ = {!   !}
All′→All P (αs ∪ αs₁) all′ = All′→All P αs (λ x z → all′ x (z ∪∣ αs₁)) ∪ All′→All P αs₁ (λ x z → all′ x (αs ∣∪ z))


⊂weaken : {A : Set} {_≟_ : Decidable≡ A} → (Γ : Ensemble _≟_) → (α : A) → Γ ⊂ (α ∷ Γ)
⊂weaken ∅ α = ∅
⊂weaken (x ∷ Γ) α = {!   !}
⊂weaken (Γ - x) α = {!   !}
⊂weaken (Γ ∪ Γ₁) α = {!   !}

⊂refl : {A : Set} {_≟_ : Decidable≡ A} → (Γ : Ensemble _≟_) → Γ ⊂ Γ
⊂refl ∅ = ∅
⊂refl (x ∷ Γ) = [ refl , (λ ()) ] ∷ {!   !}
⊂refl (Γ - x) = {!   !}
⊂refl (Γ₁ ∪ Γ₂) with ⊂refl Γ₁ | ⊂refl Γ₂
... | x₁ | x₂ = {!   !} ∪ {!   !}

triv : {A : Set} {_≟_ : Decidable≡ A} → (Γ : Ensemble _≟_) → (α : A) → (Γ - α) ⊂ Γ
triv ∅ α = α ~ ∅
triv (x ∷ Γ) α = α ~ {!   !}
triv (Γ - x) α = {!   !}
triv (Γ ∪ Γ₁) α = {!   !}

open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma

open import Decidable

data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

_×_ : Set → Set → Set
A × B = Σ A λ _ → B

infix 4 _∈_ _∉_

_∈_ : {A : Set} → A → Pred A → Set
α ∈ αs = αs α

_∉_ : {A : Set} → A → Pred A → Set
α ∉ αs = ¬(α ∈ αs)

infixr 5 _∷_ _∪_
infixl 5 _-_

∅ : {A : Set} → Pred A
∅ _ = ⊥

_∷_ : {A : Set} → A → Pred A → Pred A
(α ∷ αs) x = (α ≡ x) ⊎ (x ∈ αs)

_-_ : {A : Set} → Pred A → A → Pred A
(αs - α) x = (α ≢ x) × (x ∈ αs)

_∪_ : {A : Set} → Pred A → Pred A → Pred A
(αs ∪ βs) x = (x ∈ αs) ⊎ (x ∈ βs)

All : {A : Set} → Pred A → Pred A → Set
All P αs = ∀ x → x ∈ αs → P x

Any : {A : Set} → Pred A → Pred A → Set
Any P αs = Σ _ λ x → P x × (x ∈ αs)

_⊂_ : {A : Set} → Pred A → Pred A → Set
αs ⊂ βs = ∀ x → x ∈ αs → x ∈ βs


import Ensemble
import List

fromEnsemble : {A : Set} {eq : Decidable≡ A} → Ensemble.Ensemble eq → Pred A
fromEnsemble Ensemble.∅ = ∅
fromEnsemble (x Ensemble.∷ αs) = x ∷ fromEnsemble αs
fromEnsemble (αs Ensemble.- x) = fromEnsemble αs - x
fromEnsemble (αs Ensemble.∪ βs) = fromEnsemble αs ∪ fromEnsemble βs

loopin : {A : Set} {eq : Decidable≡ A} → (α : A) → (αs : Ensemble.Ensemble eq) → α ∈ fromEnsemble αs → α Ensemble.∈ αs
loopin α Ensemble.∅ ()
loopin α (.α Ensemble.∷ αs) (inl refl) = Ensemble.[ refl , (λ ()) ]
loopin α (x Ensemble.∷ αs) (inr x₁) = x Ensemble.∷ loopin α αs x₁
loopin α (αs Ensemble.- x) (fst₁ , snd₁) = x Ensemble.~ {!   !}
  where
    lem : Ensemble.Any _≡_ α ⟨ αs ∖ List.List.[] ⟩
    lem = loopin α αs snd₁
    lem2 : Ensemble.Any _≡_ α ⟨ αs ∖ x List.∷ List.List.[] ⟩
    lem2 with lem
    lem2 | Ensemble.[ x , x₁ ] = {!   !}
    lem2 | α Ensemble.∷ c = {!   !}
    lem2 | x Ensemble.~ c = {!   !}
    lem2 | αs Ensemble.∣∪ c = {!   !}
    lem2 | c Ensemble.∪∣ βs = {!   !}
loopin α (αs Ensemble.∪ αs₁) (inl x) = loopin α αs x Ensemble.∪∣ αs₁
loopin α (αs Ensemble.∪ αs₁) (inr x) = αs Ensemble.∣∪ loopin α αs₁ x

loop : {A : Set} {eq : Decidable≡ A} → (αs βs : Ensemble.Ensemble eq) → fromEnsemble αs ⊂ fromEnsemble βs → αs Ensemble.⊂ βs
loop Ensemble.∅ βs s = Ensemble.∅
loop (x Ensemble.∷ αs) βs s with s x (inl refl)
... | c = loopin x βs c Ensemble.∷ {!   !}
loop (αs Ensemble.- x) βs s = {!   !}
loop (αs Ensemble.∪ αs₁) βs s = loop αs βs (λ x z → s x (inl z)) Ensemble.∪ loop αs₁ βs (λ x z → s x (inr z))

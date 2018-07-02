open import All
open import Decidable
open import List

allnot∉ : {A : Set} → (x : A) → (xs : List A) → All (x ≢_) xs → x ∉ xs
allnot∉ x [] [] = empty
allnot∉ x (y ∷ xs) (x≢y ∷ allpf) = notat x≢y (allnot∉ x xs allpf)

∉allnot : {A : Set} → (x : A) → (xs : List A) → x ∉ xs → All (x ≢_) xs
∉allnot x [] empty = []
∉allnot x (y ∷ xs) (notat x≢y x∉xs) = x≢y ∷ ∉allnot x xs x∉xs

any∈ : {A : Set} → (x : A) → (xs : List A) → Any (x ≡_) xs → x ∈ xs
any∈ x _ (any [] x₁ ys)          = head x₁
any∈ x _ (any (x₂ ∷ xs) refl ys) = tail (any∈ x (xs ++ x ∷ ys) (any xs refl ys))

∈any : {A : Set} → (x : A) → (xs : List A) → x ∈ xs → Any (x ≡_) xs
∈any x (y ∷ ys) (head x₁)   = any [] x₁ ys
∈any x (y ∷ ys) (tail x∈xs) with ∈any x ys x∈xs
∈any x (y ∷ _ ) (tail x∈xs) | any xs x₁ ys = any (y ∷ xs) x₁ ys

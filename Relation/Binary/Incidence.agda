
open import Level
open import Data.Product
open import Data.Sum
open import Relation.Nullary
open import Function using (_$_ ; _∘_)

module Relation.Binary.Incidence where


record OutsideStructure  ℓ₁ ℓ₂ ℓ₃ ℓ₄
  (A : Set ℓ₁)
  (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂ ⊔ suc ℓ₃ ⊔ suc ℓ₄) where
  
  field
    _∉_ : A → B → Set ℓ₃
    _∈_ : A → B → Set ℓ₃

    ¬∉→∈ : ∀ a b → ¬ (a ∉ b) → a ∈ b
  

{-
_⟨∩⟩_  _⟨∪⟩_  : ∀ {ℓ₁ ℓ₂}{A : Set ℓ₁} → ( P Q : SetOf ℓ₁ ℓ₂ A) → SetOf ℓ₁ ℓ₂ A
(setOf p) ⟨∩⟩ (setOf q) =  setOf (λ a → p a × q a)
(setOf p) ⟨∪⟩ (setOf q) =  setOf (λ a → p a ⊎ q a)

_⟨⊆⟩_  _⟨≡⟩_ :  ∀ {ℓ₁ ℓ₂}{A : Set ℓ₁} → ( P Q : SetOf ℓ₁ ℓ₂ A) → Set (ℓ₁ ⊔  ℓ₂)
(setOf p) ⟨⊆⟩ (setOf q) = ∀ a → p a → q a

R ⟨≡⟩ S  = R ⟨⊆⟩ S × S ⟨⊆⟩ R
-}

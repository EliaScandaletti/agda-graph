open import Graph.Core
module Graph.Common.Definitions {L : Set} {E-of : Graph {L} → L → L → Set} where
  open import Function using (flip)
  open import Relation.Binary using (_⇒_)
  open import Data.Product using (_×_)

  open import Graph.Core.Definitions

  E-syntax = E-of
   
  syntax E-syntax g x y = x ↦ y ∈E[ g ]

  infix 2 _≡ᵍ_ _⊆ᵍ_

  _⊆ᴱ_ : Graph {L} → Graph {L} → Set
  g₁ ⊆ᴱ g₂ = (E-of g₁) ⇒ (E-of g₂)

  _⊆ᵍ_ : Graph {L} → Graph {L} → Set
  g₁ ⊆ᵍ g₂ = (g₁ ⊆ⱽ g₂) × (g₁ ⊆ᴱ g₂)

  _⊇ᵍ_ : Graph → Graph → Set
  _⊇ᵍ_ = flip _⊆ᵍ_

  _≡ᵍ_ : Graph → Graph → Set
  g₁ ≡ᵍ g₂ = (g₁ ⊆ᵍ g₂) × (g₂ ⊆ᵍ g₁)
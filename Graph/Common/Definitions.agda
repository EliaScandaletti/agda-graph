open import Graph.Core
module Graph.Common.Definitions {L : Set} {_↦_∈E[_] : L → L → Graph {L} → Set} where
  open import Function using (flip)
  open import Relation.Binary using (_⇒_)
  open import Data.Product using (_×_)

  open import Graph.Core.Definitions

  infix 2 _≡ᵍ_ _⊆ᵍ_

  _⊆ᴱ_ : Graph {L} → Graph {L} → Set
  g₁ ⊆ᴱ g₂ = (_↦_∈E[ g₁ ]) ⇒ (_↦_∈E[ g₂ ])

  _⊆ᵍ_ : Graph {L} → Graph {L} → Set
  g₁ ⊆ᵍ g₂ = (g₁ ⊆ⱽ g₂) × (g₁ ⊆ᴱ g₂)

  _⊇ᵍ_ : Graph → Graph → Set
  _⊇ᵍ_ = flip _⊆ᵍ_

  _≡ᵍ_ : Graph → Graph → Set
  g₁ ≡ᵍ g₂ = (g₁ ⊆ᵍ g₂) × (g₂ ⊆ᵍ g₁)

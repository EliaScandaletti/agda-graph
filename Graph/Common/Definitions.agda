module Graph.Common.Definitions {L Graph : Set} 
    (_⊆ⱽ_ : Graph → Graph → Set)
    (_↦_∈E[_] : L → L → Graph → Set) where
  open import Relation.Unary using (_⊆_)
  open import Relation.Binary using (_⇒_)
  open import Data.Product using (_×_)

  _⊆ᴱ_ : Graph → Graph → Set
  g₁ ⊆ᴱ g₂ = (_↦_∈E[ g₁ ]) ⇒ (_↦_∈E[ g₂ ])

  infix 2 _≡ᵍ_ _⊆ᵍ_

  _⊆ᵍ_ : Graph → Graph → Set
  g₁ ⊆ᵍ g₂ = (g₁ ⊆ⱽ g₂) × (g₁ ⊆ᴱ g₂)

  _≡ᵍ_ : Graph → Graph → Set
  g₁ ≡ᵍ g₂ = (g₁ ⊆ᵍ g₂) × (g₂ ⊆ᵍ g₁)

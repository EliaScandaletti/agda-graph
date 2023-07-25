open import Graph.Core
open import Relation.Nullary using (Dec)
open import Relation.Binary using (DecidableEquality; _⇒_)

module Graph.Common.Decidability
    {L : Set} {_≟ᴸ_ : DecidableEquality L}
    {_↦_∈E[_] : L → L → Graph {L} → Set}
    {E-of? : (g : Graph) → (x y : L) → Dec (x ↦ y ∈E[ g ])}
    {_⊆ᴱ?_ : (g₁ g₂ : Graph {L}) → Dec (_↦_∈E[ g₁ ] ⇒ _↦_∈E[ g₂ ])} where
  open import Relation.Nullary using (_×-dec_)

  open import Graph.Core.Decidability {L} {_≟ᴸ_}
  open import Graph.Common.Definitions {L} {_↦_∈E[_]}

  _⊆ᵍ?_ : (g₁ g₂ : Graph) → Dec (g₁ ⊆ᵍ g₂)
  g₁ ⊆ᵍ? g₂ = (g₁ ⊆ⱽ? g₂) ×-dec (g₁ ⊆ᴱ? g₂)

  _≟_ : (g₁ g₂ : Graph) → Dec (g₁ ≡ᵍ g₂)
  g₁ ≟ g₂ = (g₁ ⊆ᵍ? g₂) ×-dec (g₂ ⊆ᵍ? g₁)
 

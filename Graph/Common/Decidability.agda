open import Relation.Nullary using (Dec)
open import Relation.Unary using (_⊆_)
open import Relation.Binary using (DecidableEquality; _⇒_)
module Graph.Common.Decidability
    {L Graph : Set} (_≟ᴸ_ : DecidableEquality L)
    {_∈V[_] : L → Graph → Set}
    {_↦_∈E[_] : L → L → Graph → Set}
    (_⊆ⱽ?_ : (g₁ g₂ : Graph) → Dec ((_∈V[ g₁ ]) ⊆ (_∈V[ g₂ ])))
    (_⊆ᴱ?_ : (g₁ g₂ : Graph) → Dec (_↦_∈E[ g₁ ] ⇒ _↦_∈E[ g₂ ])) where
  open import Relation.Nullary using (_×-dec_)

  open import Graph.Common.Definitions (λ (g₁ g₂ : Graph) → (_∈V[ g₁ ]) ⊆ (_∈V[ g₂ ])) _↦_∈E[_]

  _⊆ᵍ?_ : (g₁ g₂ : Graph) → Dec (g₁ ⊆ᵍ g₂)
  g₁ ⊆ᵍ? g₂ = (g₁ ⊆ⱽ? g₂) ×-dec (g₁ ⊆ᴱ? g₂)

  _≟_ : (g₁ g₂ : Graph) → Dec (g₁ ≡ᵍ g₂)
  g₁ ≟ g₂ = (g₁ ⊆ᵍ? g₂) ×-dec (g₂ ⊆ᵍ? g₁)

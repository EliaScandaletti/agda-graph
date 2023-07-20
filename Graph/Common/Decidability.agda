open import Graph.Core
open import Relation.Nullary using (Dec)
open import Relation.Binary using (DecidableEquality; _⇒_)

module Graph.Common.Decidability
    {L : Set} {_≟ᴸ_ : DecidableEquality L}
    {E-of : Graph {L} → L → L → Set}
    {E-of? : (g : Graph) → (x y : L) → Dec (E-of g x y)}
    {_⊆ᴱ?_ : (g₁ g₂ : Graph {L}) → Dec ((E-of g₁) ⇒ (E-of g₂))} where
  open import Relation.Nullary using (_×-dec_)

  open import Graph.Core.Decidability {L} {_≟ᴸ_}
  open import Graph.Common.Definitions {L} {E-of}

  _⊆ᵍ?_ : (g₁ g₂ : Graph) → Dec (g₁ ⊆ᵍ g₂)
  g₁ ⊆ᵍ? g₂ = (g₁ ⊆ⱽ? g₂) ×-dec (g₁ ⊆ᴱ? g₂)

  _≟_ : (g₁ g₂ : Graph) → Dec (g₁ ≡ᵍ g₂)
  g₁ ≟ g₂ = (g₁ ⊆ᵍ? g₂) ×-dec (g₂ ⊆ᵍ? g₁)
 
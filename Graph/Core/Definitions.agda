module Graph.Core.Definitions {L : Set} where
  open import Level renaming (0ℓ to 0𝓁)
  open import Relation.Unary using (Pred; ∅; ｛_｝; _∪_; _⊆_)

  open import Graph.Core {L}

  V-of : Graph → Pred L 0𝓁
  V-of ε = ∅
  V-of (v x) = ｛ x ｝
  V-of (g₁ + g₂) = (V-of g₁) ∪ (V-of g₂)
  V-of (g₁ * g₂) = (V-of g₁) ∪ (V-of g₂)
  
  syntax V-of g x = x ∈V[ g ]
  
  _⊆ⱽ_ : Graph → Graph → Set
  g₁ ⊆ⱽ g₂ = (V-of g₁) ⊆ (V-of g₂)

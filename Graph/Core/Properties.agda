module Graph.Core.Properties {L : Set} where
  open import Graph.Core {L}
  open import Graph.Core.Definitions

  lemma-⊆ⱽ-refl : {g : Graph} → g ⊆ⱽ g
  lemma-⊆ⱽ-refl = λ z → z

  lemma-⊆ⱽ-trans : {g₁ g₂ g₃ : Graph} → g₁ ⊆ⱽ g₂ → g₂ ⊆ⱽ g₃ → g₁ ⊆ⱽ g₃
  lemma-⊆ⱽ-trans g₁⊆ⱽg₂ g₂⊆ⱽg₃ = λ x∈V₁ → g₂⊆ⱽg₃ (g₁⊆ⱽg₂ x∈V₁)

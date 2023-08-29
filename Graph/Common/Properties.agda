module Graph.Common.Properties {L Graph : Set}
      (_⊆ⱽ_ : Graph → Graph → Set)
      (lemma-⊆ⱽ-refl : {g : Graph} → g ⊆ⱽ g)
      (lemma-⊆ⱽ-trans : {g₁ g₂ g₃ : Graph} → g₁ ⊆ⱽ g₂ → g₂ ⊆ⱽ g₃ → g₁ ⊆ⱽ g₃)
      (_↦_∈E[_] : L → L → Graph → Set) where
  open import Function using (id; _∘_)
  open import Relation.Binary using (IsEquivalence)
  open import Data.Product using (_,_)

  open import Graph.Common.Definitions _⊆ⱽ_ _↦_∈E[_]

  lemma-≡ᵍ-refl : {g : Graph} → g ≡ᵍ g
  lemma-≡ᵍ-refl = (lemma-⊆ⱽ-refl , id) , (lemma-⊆ⱽ-refl , id)

  lemma-≡ᵍ-sym : {g₁ g₂ : Graph} → g₁ ≡ᵍ g₂ → g₂ ≡ᵍ g₁
  lemma-≡ᵍ-sym ((V₁⊆V₂ , E₁⊆E₂) , (V₂⊆V₁ , E₂⊆E₁)) = (V₂⊆V₁ , E₂⊆E₁) , V₁⊆V₂ , E₁⊆E₂
  
  lemma-≡ᵍ-trans : {g₁ g₂ g₃ : Graph} → g₁ ≡ᵍ g₂ → g₂ ≡ᵍ g₃ → g₁ ≡ᵍ g₃
  lemma-≡ᵍ-trans ((V₁⊆V₂ , E₁⊆E₂) , (V₂⊆V₁ , E₂⊆E₁)) ((V₂⊆V₃ , E₂⊆E₃) , (V₃⊆V₂ , E₃⊆E₂)) =
                 (lemma-⊆ⱽ-trans V₁⊆V₂ V₂⊆V₃ , (E₂⊆E₃ ∘ E₁⊆E₂)) , (lemma-⊆ⱽ-trans V₃⊆V₂ V₂⊆V₁ , (E₂⊆E₁ ∘ E₃⊆E₂))

  ≡ᵍ-is-equivalence : IsEquivalence _≡ᵍ_
  ≡ᵍ-is-equivalence = record { refl = lemma-≡ᵍ-refl ; sym = lemma-≡ᵍ-sym ; trans = lemma-≡ᵍ-trans }

  lemma-⊆ᵍ-refl : {g : Graph} → g ⊆ᵍ g
  lemma-⊆ᵍ-refl = lemma-⊆ⱽ-refl , id

  lemma-⊆ᵍ-trans : {g₁ g₂ g₃ : Graph} → g₁ ⊆ᵍ g₂ → g₂ ⊆ᵍ g₃ → g₁ ⊆ᵍ g₃
  lemma-⊆ᵍ-trans (V₁⊆V₂ , E₁⊆E₂) (V₂⊆V₃ , E₂⊆E₃) = lemma-⊆ⱽ-trans V₁⊆V₂ V₂⊆V₃ , (E₂⊆E₃ ∘ E₁⊆E₂)

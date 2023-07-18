module Graph.Core {L : Set} where
  open import Level renaming (0ℓ to 0𝓁)
  open import Function using (flip)
  open import Relation.Unary using (Pred; ∅; ｛_｝; _∪_; _⊆_) 
  open import Relation.Binary using (Rel; _⇒_)

  open import Data.Empty using (⊥)
  open import Data.Sum using (_⊎_)
  open import Data.Product using (_×_)
  
  data Graph : Set where
    ε   : Graph
    v_  : L → Graph
    _+_ : Graph → Graph → Graph
    _*_ : Graph → Graph → Graph
  
  infixl 6  _+_
  infixl 7  _*_
  
  V-of : Graph → Pred L 0𝓁
  V-of ε = ∅
  V-of (v x) = ｛ x ｝
  V-of (g₁ + g₂) = (V-of g₁) ∪ (V-of g₂)
  V-of (g₁ * g₂) = (V-of g₁) ∪ (V-of g₂)
  
  syntax V-of g x = x ∈V[ g ]

  E-of : Graph → Rel L 0𝓁
  E-of ε         _ _ = ⊥
  E-of (v x)     _ _ = ⊥
  E-of (g₁ + g₂) x y = (E-of g₁) x y ⊎ (E-of g₂) x y
  E-of (g₁ * g₂) x y = ((E-of g₁) x y ⊎ (E-of g₂) x y) ⊎ (((x ∈V[ g₁ ]) × (y ∈V[ g₂ ])) ⊎ ((x ∈V[ g₂ ]) × y ∈V[ g₁ ]))
  
  syntax E-of g x y = x ↦ y ∈E[ g ]

  infix 2 _≡ᵍ_ _⊆ᵍ_

  _⊆ᵍ_ : Graph → Graph → Set
  g₁ ⊆ᵍ g₂ = ((V-of g₁) ⊆ (V-of g₂)) × ((E-of g₁) ⇒ (E-of g₂))

  _⊇ᵍ_ : Graph → Graph → Set
  _⊇ᵍ_ = flip _⊆ᵍ_

  _≡ᵍ_ : Graph → Graph → Set
  g₁ ≡ᵍ g₂ = (g₁ ⊆ᵍ g₂) × (g₂ ⊆ᵍ g₁)

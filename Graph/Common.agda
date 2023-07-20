module Graph.Common {L : Set} where
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

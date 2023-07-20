module Graph.Undirected.Core {L : Set} where
  open import Level renaming (0ℓ to 0𝓁)
  open import Relation.Binary using (Rel)
  open import Data.Empty using (⊥)
  open import Data.Sum using (_⊎_)
  open import Data.Product using (_×_)
  
  open import Graph.Core {L} public
  open import Graph.Core.Definitions {L} public

  E-of : Graph → Rel L 0𝓁
  E-of ε         _ _ = ⊥
  E-of (v x)     _ _ = ⊥
  E-of (g₁ + g₂) x y = (E-of g₁) x y ⊎ (E-of g₂) x y
  E-of (g₁ * g₂) x y = ((E-of g₁) x y ⊎ (E-of g₂) x y) ⊎ (((x ∈V[ g₁ ]) × (y ∈V[ g₂ ])) ⊎ ((x ∈V[ g₂ ]) × y ∈V[ g₁ ]))
  
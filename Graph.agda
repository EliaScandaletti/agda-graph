module Graph where

  open import Level renaming (0ℓ to 0𝓁)
  open import Agda.Builtin.Equality

  open import Relation.Nullary using (Dec; yes; no; _⊎-dec_; _×-dec_)
  open import Relation.Unary using (Pred; ∅; ｛_｝; _∪_; _≐_) 
  open import Relation.Binary using (Rel; _⇔_; DecidableEquality)

  open import Data.Empty using (⊥; ⊥-elim)
  open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
  open import Data.Product using (_×_; _,_; proj₁; proj₂)
  open import Data.Bool using (true; false)

  open import Graph.Core public
  open import Graph.Properties public
  open import Graph.Decidability public


  module Example where
    open import Data.Nat using (ℕ)
    g = (v 1 * v 2 * v 3) * (v 0 + v 4) + (v 0 * v 3 * v 5)
    {- 
            +-------+
            |       |
            1       3          0               0---3
             \      |                           \ /
     g =  (   \     |    *             ) +       5
               \    |
                2---+      4
     
          +-------+
          |       |
          1---0---3--+        0---3
          |\  |   |  |         \ /
     g =  | \ |   |  |  +       5
          |  \|   |  |
          4---2---+  |
          |          |
          +----------+
     
          +-------+
          |       |
          1---0---3--+
          |\  |\ /|  |
     g =  | \ | 5 |  |
          |  \|   |  |
          4---2---+  |
          |          |
          +----------+
    -}

    _ : 1 ↦ 0 ∈E[ g ]
    _ = inj₁ (inj₂ (inj₁ (inj₁ (inj₁ refl) , inj₁ refl)))

    g₁ = v 0 * v 1
    g₂ = v 1 * v 0
    _ : g₁ ≡ᵍ g₂
    _ = ((λ { (inj₁ x) → inj₂ x
            ; (inj₂ y) → inj₁ y})
       , (λ { (inj₁ x) → inj₁ x
            ; (inj₂ (inj₁ x)) → inj₂ (inj₂ x)
            ; (inj₂ (inj₂ y)) → inj₂ (inj₁ y)}))
      , ((λ { (inj₁ x) → inj₂ x
            ; (inj₂ y) → inj₁ y})
       , (λ { (inj₁ x) → inj₁ x
            ; (inj₂ (inj₁ x)) → inj₂ (inj₂ x)
            ; (inj₂ (inj₂ y)) → inj₂ (inj₁ y)}))

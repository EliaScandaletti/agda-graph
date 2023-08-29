open import Relation.Binary using (DecidableEquality)
module Graph.Core.Algo.Properties {L : Set} (_≟ᴸ_ : DecidableEquality L) where
  open import Agda.Builtin.Equality using (refl)
  open import Data.Sum using (inj₁; inj₂)
  open import Data.List.Membership.DecPropositional _≟ᴸ_
  open import Data.List.Relation.Unary.Any using (here)
  open import Data.List.Relation.Unary.Unique.Propositional using (Unique)

  open import Algo.List.Properties _≟ᴸ_
  open import Graph.Core
  open import Graph.Core.Definitions
  open import Graph.Core.Algo.Definitions _≟ᴸ_

  vertices-unique : (g : Graph) → Unique (vertices g)
  vertices-unique g = unique-deduplicate _

  ∈V⇒∈v : {x : L} → (g : Graph) → x ∈V[ g ] → x ∈ (vertices g)
  ∈V⇒∈v (v x) v-V = here refl
  ∈V⇒∈v (g₁ + g₂) (+-Vˡ x∈V) = ∈-deduplicate _ (∈ˡ⇒∈++ (vertices g₁) (vertices g₂) (∈V⇒∈v g₁ x∈V))
  ∈V⇒∈v (g₁ + g₂) (+-Vʳ x∈V) = ∈-deduplicate _ (∈ʳ⇒∈++ (vertices g₁) (vertices g₂) (∈V⇒∈v g₂ x∈V))
  ∈V⇒∈v (g₁ * g₂) (*-Vˡ x∈V) = ∈-deduplicate _ (∈ˡ⇒∈++ (vertices g₁) (vertices g₂) (∈V⇒∈v g₁ x∈V))
  ∈V⇒∈v (g₁ * g₂) (*-Vʳ x∈V) = ∈-deduplicate _ (∈ʳ⇒∈++ (vertices g₁) (vertices g₂) (∈V⇒∈v g₂ x∈V))

  ∈v⇒∈V : {x : L} → (g : Graph) → x ∈ (vertices g) → x ∈V[ g ]
  ∈v⇒∈V (v x) (here refl) = v-V
  ∈v⇒∈V (g₁ + g₂) x∈v with ∈++⇒∈ˡ⊎∈ʳ (vertices g₁) (vertices g₂) (deduplicate-∈ _ x∈v)
  ... | inj₁ x∈v₁ = +-Vˡ (∈v⇒∈V g₁ x∈v₁)
  ... | inj₂ x∈v₂ = +-Vʳ (∈v⇒∈V g₂ x∈v₂)
  ∈v⇒∈V (g₁ * g₂) x∈v with ∈++⇒∈ˡ⊎∈ʳ (vertices g₁) (vertices g₂) (deduplicate-∈ _ x∈v)
  ... | inj₁ x∈v₁ = *-Vˡ (∈v⇒∈V g₁ x∈v₁)
  ... | inj₂ x∈v₂ = *-Vʳ (∈v⇒∈V g₂ x∈v₂)

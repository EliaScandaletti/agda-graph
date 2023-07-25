open import Relation.Binary using (DecidableEquality)

module Graph.Core.Decidability {L : Set} {_≟ᴸ_ : DecidableEquality L} where
  open import Agda.Builtin.Equality using (refl; _≡_)
  open import Function using (id)
  open import Relation.Nullary using (Dec; yes; no)
  open import Data.Empty using (⊥)

  open import Graph.Core
  open import Graph.Core.Definitions
  
  V-of? : (g : Graph) → (x : L) → Dec (x ∈V[ g ])
  V-of? ε         x = no λ ()
  V-of? (v x₁)    x with x₁ ≟ᴸ x
  ... | yes refl = yes v-V
  ... | no  x₁≠x = no (λ { v-V → x₁≠x refl})
  V-of? (g₁ + g₂) x with V-of? g₁ x | V-of? g₂ x
  ... | no  x∉V₁ | no  x∉V₂ = no λ { (+-Vˡ x∈V₁) → x∉V₁ x∈V₁ ; (+-Vʳ x∈V₂) → x∉V₂ x∈V₂}
  ... | no  x∉V₁ | yes x∈V₂ = yes (+-Vʳ x∈V₂)
  ... | yes x∈V₁ | _ = yes (+-Vˡ x∈V₁)
  V-of? (g₁ * g₂) x with V-of? g₁ x | V-of? g₂ x
  ... | no  x∉V₁ | no  x∉V₂ = no λ { (*-Vˡ x∈V₁) → x∉V₁ x∈V₁ ; (*-Vʳ x∈V₂) → x∉V₂ x∈V₂}
  ... | no  x∉V₁ | yes x∈V₂ = yes (*-Vʳ x∈V₂)
  ... | yes x∈V₁ | _ = yes (*-Vˡ x∈V₁)
    
  _⊆ⱽ?_ : (g₁ g₂ : Graph) → Dec (g₁ ⊆ⱽ g₂)
  ε ⊆ⱽ? _ = yes λ ()
  (v x) ⊆ⱽ? ε = no helper where
    helper : (v x) ⊆ⱽ ε → ⊥
    helper x∈∅ with x∈∅ v-V
    ... | ()
  (v x₁) ⊆ⱽ? (v x₂) with x₂ ≟ᴸ x₁
  ... | no  x₂≠x₁ = no (λ x → x₂≠x₁ (helper (x v-V))) where
    helper : x₁ ∈V[ (v x₂) ] → x₂ ≡ x₁
    helper v-V = refl
  ... | yes refl = yes (id)
  (v x) ⊆ⱽ? (g₂ + g₃) with (v x) ⊆ⱽ? g₂ | (v x) ⊆ⱽ? g₃
  ... | no  x∉V₂ | no  x∉V₃ = no helper where
    helper :  ({x₂ : L} → x₂ ∈V[ v x ] → x₂ ∈V[ g₂ + g₃ ]) → ⊥
    helper p with p v-V
    ... | +-Vˡ x∈V₂ = x∉V₂ λ {v-V → x∈V₂}
    ... | +-Vʳ x∈V₃ = x∉V₃ λ {v-V → x∈V₃}
  ... | no  x∉V₂ | yes x∈V₃ = yes λ z → +-Vʳ (x∈V₃ z)
  ... | yes x∈V₂ | Q = yes λ z → +-Vˡ (x∈V₂ z)
  (v x) ⊆ⱽ? (g₂ * g₃) with (v x) ⊆ⱽ? g₂ | (v x) ⊆ⱽ? g₃
  ... | no  x∉V₂ | no  x∉V₃ = no helper where
    helper : ({x₂ : L} → x₂ ∈V[ v x ] → x₂ ∈V[ g₂ * g₃ ]) → ⊥
    helper p with p v-V
    ... | *-Vˡ x∈V₂ = x∉V₂ λ {v-V → x∈V₂}
    ... | *-Vʳ x∈V₃ = x∉V₃ λ {v-V → x∈V₃}
  ... | no  x∉V₂ | yes x∈V₃ = yes λ z → *-Vʳ (x∈V₃ z)
  ... | yes x∈V₂ | Q = yes λ z → *-Vˡ (x∈V₂ z)
  (g₁ + g₂) ⊆ⱽ? g₃ with g₁ ⊆ⱽ? g₃ | g₂ ⊆ⱽ? g₃
  ... | no  V₁⊈V₃ | _ = no helper where
    helper : ({x : L} → x ∈V[ g₁ + g₂ ] → x ∈V[ g₃ ]) → ⊥
    helper p = V₁⊈V₃ λ z → p (+-Vˡ z)
  ... | yes _     | no  V₂⊈V₃ = no helper where
    helper : ({x : L} → x ∈V[ g₁ + g₂ ] → x ∈V[ g₃ ]) → ⊥
    helper p = V₂⊈V₃ λ z → p (+-Vʳ z)
  ... | yes V₁⊆V₃ | yes V₂⊆V₃ = yes (λ { (+-Vˡ x) → V₁⊆V₃ x ; (+-Vʳ x) → V₂⊆V₃ x})
  (g₁ * g₂) ⊆ⱽ? g₃ with g₁ ⊆ⱽ? g₃ | g₂ ⊆ⱽ? g₃
  ... | no  V₁⊈V₃ | _ = no helper where
    helper : ({x : L} → x ∈V[ g₁ * g₂ ] → x ∈V[ g₃ ]) → ⊥
    helper p = V₁⊈V₃ λ z → p (*-Vˡ z)
  ... | yes _     | no  V₂⊈V₃ = no helper where
    helper : ({x : L} → x ∈V[ g₁ * g₂ ] → x ∈V[ g₃ ]) → ⊥
    helper p = V₂⊈V₃ λ z → p (*-Vʳ z)
  ... | yes V₁⊆V₃ | yes V₂⊆V₃ = yes (λ { (*-Vˡ x) → V₁⊆V₃ x ; (*-Vʳ x) → V₂⊆V₃ x})
  

module Graph.Core.Definitions {L : Set} where
  open import Relation.Unary using (_⊆_)

  open import Graph.Core

  data _∈V[_] (x : L) : Graph → Set where
    v-V : x ∈V[ (v x) ]
    +-Vˡ : {g₁ g₂ : Graph} → x ∈V[ g₁ ] → x ∈V[ (g₁ + g₂)]
    +-Vʳ : {g₁ g₂ : Graph} → x ∈V[ g₂ ] → x ∈V[ (g₁ + g₂)]
    *-Vˡ : {g₁ g₂ : Graph} → x ∈V[ g₁ ] → x ∈V[ (g₁ * g₂)]
    *-Vʳ : {g₁ g₂ : Graph} → x ∈V[ g₂ ] → x ∈V[ (g₁ * g₂)]

  _⊆ⱽ_ : Graph → Graph → Set
  g₁ ⊆ⱽ g₂ = (_∈V[ g₁ ]) ⊆ (_∈V[ g₂ ])

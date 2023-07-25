module Graph.Undirected.Core {L : Set} where
  open import Graph.Core {L} public
  open import Graph.Core.Definitions {L} public

  data _↦_∈E[_] (x y : L) : Graph → Set where
    +-Eˡ : {g₁ g₂ : Graph} → x ↦ y ∈E[ g₁ ] → x ↦ y ∈E[ (g₁ + g₂)]
    +-Eʳ : {g₁ g₂ : Graph} → x ↦ y ∈E[ g₂ ] → x ↦ y ∈E[ (g₁ + g₂)]
    *-Eˡ : {g₁ g₂ : Graph} → x ↦ y ∈E[ g₁ ] → x ↦ y ∈E[ (g₁ * g₂)]
    *-Eʳ : {g₁ g₂ : Graph} → x ↦ y ∈E[ g₂ ] → x ↦ y ∈E[ (g₁ * g₂)]
    *-Eˣ₁ : {g₁ g₂ : Graph} → x ∈V[ g₁ ] → y ∈V[ g₂ ] → x ↦ y ∈E[ (g₁ * g₂)]
    *-Eˣ₂ : {g₁ g₂ : Graph} → y ∈V[ g₁ ] → x ∈V[ g₂ ] → x ↦ y ∈E[ (g₁ * g₂)]

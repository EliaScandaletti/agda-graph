module Graph.Common.Weighted {L Graph : Set} {_↦_∈E[_] : L → L → Graph → Set} where
  open import Data.Nat using (ℕ)

  record WGraph : Set where
    field
      core   : Graph
      weight : {x y : L} → x ↦ y ∈E[ core ] → ℕ

open import Graph.Core
module Graph.Common.Weighted {L : Set} {_↦_∈E[_] : L → L → Graph {L} → Set} where
  open import Data.Nat using (ℕ)

  record WGraph : Set where
    field
      core   : Graph {L}
      weight : {x y : L} → x ↦ y ∈E[ core ] → ℕ

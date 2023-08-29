open import Relation.Binary using (DecidableEquality)
module Graph.Core.Algo.Definitions {L : Set} (_≟ᴸ_ : DecidableEquality L) where
  open import Data.List using (List; []; [_]; _++_; deduplicate)
  open import Graph.Core

  vertices : Graph → List L
  vertices g = deduplicate _≟ᴸ_ (go g) where
    go : Graph → List L
    go ε = []
    go (v x) = [ x ]
    go (g₁ + g₂) = vertices g₁ ++ vertices g₂
    go (g₁ * g₂) = vertices g₁ ++ vertices g₂

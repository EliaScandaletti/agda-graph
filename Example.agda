module Example where
  open import Agda.Builtin.Equality using (refl)
  open import Data.Maybe using (Maybe; maybe′)
  open import Data.Product using (_×_; _,_)
  open import Data.Nat using (ℕ)
  open import Data.Nat.Properties using (+-0-isMonoid; ≤-isDecTotalOrder) renaming (_≟_ to _≟ᴺ_)
  open import Data.List.Membership.Propositional using (_∈_)
  open import Data.List.Relation.Unary.Any using (here; there)

  open import Graph.Core
  open import Graph.Core.Decidability _≟ᴺ_
  open import Graph.Core.Algo.Definitions _≟ᴺ_
  open import Graph.Core.Algo.Properties _≟ᴺ_
  open import Graph.Undirected
  open import Graph.Undirected.Decidability _≟ᴺ_
  open import Graph.Undirected.Properties
  open import Graph.Common.Algo.Definitions vertices E-of?
  open import Graph.Common.Algo.Properties {_≟ᴸ_ = _≟ᴺ_} vertices ∈V⇒∈v ∈v⇒∈V E-of? lemma-soundness
  open import Graph.Common.Algo.Path V-of? E-of? lemma-soundness
  open Weighted +-0-isMonoid ≤-isDecTotalOrder
  open import Graph.Common.Algo.FloydWarshall _≟ᴺ_ vertices V-of? E-of? lemma-soundness +-0-isMonoid ≤-isDecTotalOrder


  g = (v 1 * v 2 * v 3) * (v 0 + v 4) + (v 0 * v 3 * v 5)
  {-
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

  w : {x y : ℕ} → .(x ↦ y ∈E[ g ]) → ℕ
  w {0} {1} _ = 1
  w {1} {0} _ = 1
  w {0} {2} _ = 2
  w {2} {0} _ = 2
  w {0} {3} _ = 10
  w {3} {0} _ = 10
  w {0} {5} _ = 3
  w {5} {0} _ = 3
  w {1} {2} _ = 3
  w {2} {1} _ = 3
  w {1} {3} _ = 7
  w {3} {1} _ = 7
  w {1} {4} _ = 9
  w {4} {1} _ = 9
  w {2} {3} _ = 8
  w {3} {2} _ = 8
  w {2} {4} _ = 8
  w {4} {2} _ = 8
  w {3} {4} _ = 9999
  w {4} {3} _ = 9999
  w {3} {5} _ = 2
  w {5} {3} _ = 2
  w {x} {y} _ = _ -- not reachable


  x : Maybe (Path g 3 4)
  x = floyd-warshall w 3 4
  
  y = maybe′ (weight w) 0 x

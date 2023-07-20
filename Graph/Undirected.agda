module Graph.Undirected where
  open import Agda.Builtin.Equality using (refl)

  open import Data.Sum using (inj₁; inj₂)
  open import Data.Product using (_,_)

  open import Graph.Undirected.Core public
  open import Graph.Undirected.Properties public
  open import Graph.Undirected.Decidability public

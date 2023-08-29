open import Relation.Nullary using (Dec)
open import Data.Product using (_×_)
open import Data.List using (List)
module Graph.Common.Algo.Definitions {L Graph : Set}
    (vertices : Graph → List L)
    {_↦_∈E[_] : L → L → Graph → Set}
    (E-of? : (g : Graph) → (x y : L) → Dec (x ↦ y ∈E[ g ])) where
  open import Agda.Builtin.Equality using (refl)
  open import Relation.Nullary using (no; yes)
  open import Data.Product using (_,_)
  open import Data.List using ([]; [_]; map; filter; cartesianProduct)

  edges : Graph → List (L × L)
  edges g = filter (λ { (x , y) → E-of? g x y}) (cartesianProduct (vertices g) (vertices g))

  adjacency-list : Graph → List (L × List L)
  adjacency-list g = map (λ x → x , (filter (E-of? g x) (vertices g))) (vertices g)

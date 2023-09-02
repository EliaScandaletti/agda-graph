open import Relation.Nullary using (Dec)
module Graph.Common.Algo.Path
  {L Graph : Set}
  {_∈V[_] : L → Graph → Set}
  (V-of? : (g : Graph) → (x : L) → Dec (x ∈V[ g ]))
  {_↦_∈E[_] : L → L → Graph → Set}
  (E-of? : (g : Graph) → (x y : L) → Dec (x ↦ y ∈E[ g ]))
  where
  open import Relation.Nullary.Decidable using (True)

  data Path (g : Graph) : L → L → Set where
    _# : (v : L) → {True (V-of? g v)} → Path g v v
    _↦_# : (s d : L) → {True (E-of? g s d)} → Path g s d
    _↦_ : (s : L) → {x d : L} → Path g x d → {True (E-of? g s x)} → Path g s d

  _++_ : {g : Graph} {s x d : L} → Path g s x  → Path g x d → Path g s d
  (_ #) ++ p = p
  (_↦_# s x {sx∈E}) ++ p = (s ↦ p) {sx∈E}
  (_↦_ s q {sx∈E}) ++ p = (s ↦ (q ++ p)) {sx∈E}

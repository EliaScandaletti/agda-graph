open import Relation.Nullary using (Dec)
open import Relation.Binary using () renaming (Decidable to Dec₂)
open import Data.List using (List)
module Graph.Common.Algo.FloydWarshall
  {L Graph : Set}
  (vertices : Graph → List L)
  {_∈V[_] : L → Graph → Set} (V-of? : (g : Graph) → (x : L) → Dec (x ∈V[ g ]))
  {_↦_∈E[_] : L → L → Graph → Set} (E-of? : (g : Graph) → (x y : L) → Dec (x ↦ y ∈E[ g ]))
  {W : Set}
  (_+_ : W → W → W)
  {_≤_ : W → W → Set} (_≤?_ : Dec₂ _≤_)
  (zero : W)
  where
  open import Relation.Nullary.Decidable using (yes; no; True; toWitness; fromWitness)
  open import Data.Unit using (tt)
  open import Data.Bool using (Bool; true; false)
  open import Data.Maybe using (Maybe; just; nothing)
  open import Data.Nat using (ℕ)
  open import Data.List using ([]; _∷_)

  open import Graph.Common.Algo.Definitions vertices
  open import Graph.Common.Algo.Path V-of? E-of?
  
  module _ {g : Graph} (w : {x y : L} → x ↦ y ∈E[ g ] → W) where
    weight : {s d : L} → Path g s d → W
    weight (v #) = zero
    weight ((s ↦ d #) {q}) = w (toWitness q)
    weight ((s ↦ p) {q}) = (w (toWitness q)) + (weight p)
  
    _≼_ : {s d : L} → Path g s d → Path g s d → Set
    _≼_ p q = (weight p) ≤ (weight q)
    
    _≼?_ : {s d : L} → (p q : Path g s d) → Dec (p ≼ q)
    _≼?_ p q = (weight p) ≤? weight q
  
    floyd-warshall : (s d : L) → {True (V-of? g s)} → {True (V-of? g d)} → Maybe (Path g s d)
    floyd-warshall s d = go s d (vertices g) where
      
      min-maybe : {s d : L} → Maybe (Path g s d) → Maybe (Path g s d) → Maybe (Path g s d)
      min-maybe (just p) (just q) with p ≼? q
      ... | no  _ = just q
      ... | yes _ = just p
      min-maybe (just x) nothing = just x
      min-maybe nothing y = y

      _++-maybe_ : {s x d : L} → Maybe (Path g s x) → Maybe (Path g x d) → Maybe (Path g s d)
      just p  ++-maybe just q  = just (p ++ q)
      just _  ++-maybe nothing = nothing
      nothing ++-maybe _       = nothing
      
      go : (s d : L) → List L → Maybe (Path g s d)
      go s d [] with E-of? g s d
      ... | no  _ = nothing
      ... | yes sd∈E = just ((s ↦ d #) {fromWitness sd∈E})
      go s d (x ∷ l) = min-maybe (go s d l) (go s x l ++-maybe go x d l)

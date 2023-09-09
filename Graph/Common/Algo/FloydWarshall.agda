open import Algebra.Structures using (IsMonoid)
open import Relation.Nullary using (Dec)
open import Relation.Binary using (DecidableEquality; IsDecTotalOrder) renaming (Decidable to Dec₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product using (_×_)
open import Data.List using (List)
module Graph.Common.Algo.FloydWarshall
  {L Graph : Set}
  (_≟ᴸ_ : DecidableEquality L)
  (vertices : Graph → List L)
  {_∈V[_] : L → Graph → Set} (V-of? : (g : Graph) → (x : L) → Dec (x ∈V[ g ]))
  {_↦_∈E[_] : L → L → Graph → Set} (E-of? : (g : Graph) → (x y : L) → Dec (x ↦ y ∈E[ g ]))
  (lemma-soundness : {x y : L} → (g : Graph) → x ↦ y ∈E[ g ] → x ∈V[ g ] × y ∈V[ g ])
  {W : Set}
  {_+_ : W → W → W} {ε : W} (W-isMonoid : IsMonoid _≡_ _+_ ε)
  {_≤_ : W → W → Set} (W-isDecTotalOrder : IsDecTotalOrder _≡_ _≤_)
  where
  open import Relation.Nullary.Decidable using (yes; no; fromWitness)
  open import Relation.Binary.PropositionalEquality using (refl)
  open import Data.Unit using (tt)
  open import Data.Bool using (Bool; true; false)
  open import Data.Maybe using (Maybe; just; nothing)
  open import Data.Nat using (ℕ)
  open import Data.List using ([]; _∷_)

  open import Graph.Common.Algo.Definitions vertices
  open import Graph.Common.Algo.Path V-of? E-of? lemma-soundness

  module _ {g : Graph} where
    _++-maybe_ : {s x d : L} → Maybe (Path g s x) → Maybe (Path g x d) → Maybe (Path g s d)
    just p  ++-maybe just q  = just (p ++ q)
    just _  ++-maybe nothing = nothing
    nothing ++-maybe _       = nothing
    
    module _ (w : {x y : L} → .(x ↦ y ∈E[ g ]) → W) where
      open Weighted W-isMonoid W-isDecTotalOrder w
      
      min-maybe : {s d : L} → Maybe (Path g s d) → Maybe (Path g s d) → Maybe (Path g s d)
      min-maybe (just p) (just q) with p ≼? q
      ... | no  _ = just q
      ... | yes _ = just p
      min-maybe (just x) nothing = just x
      min-maybe nothing y = y
      
      go : List L → (s d : L) → Maybe (Path g s d)
      go l s d with s ≟ᴸ d
      go l s .s | yes refl with V-of? g s
      ... | no _ = nothing
      ... | yes Vs = just ((s #) {fromWitness Vs})
      go [] s d | no _ with E-of? g s d
      ... | no  _ = nothing
      ... | yes sd∈E = just ((s ↦ d #) {fromWitness sd∈E})
      go (x ∷ l) s d | no _ = min-maybe (go l s d) (go l s x ++-maybe go l x d)
        
      floyd-warshall : (s d : L) → Maybe (Path g s d)
      floyd-warshall = go (vertices g)

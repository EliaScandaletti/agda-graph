open import Graph.Core
open import Graph.Core.Definitions using(_∈V[_])
open import Relation.Nullary using (Dec)
open import Relation.Binary using (DecidableEquality; _⇒_)
open import Data.Product using (_×_)
module Graph.Common.Algo.Definitions
    {L : Set} {_≟ᴸ_ : DecidableEquality L}
    {_↦_∈E[_] : L → L → Graph {L} → Set}
    {E-of? : (g : Graph) → (x y : L) → Dec (x ↦ y ∈E[ g ])}
    {lemma-soundness : {x y : L} → (g : Graph) → x ↦ y ∈E[ g ] → x ∈V[ g ] × y ∈V[ g ]} where
  open import Agda.Builtin.Equality using (_≡_; refl)
  open import Function using (_∘_)
  open import Relation.Nullary using (¬_; no; yes)
  open import Relation.Binary using () renaming (Decidable to Dec₂)
  open import Relation.Binary.PropositionalEquality using (sym)
  open import Data.Empty using (⊥; ⊥-elim)
  open import Data.Sum using ([_,_]′)
  open import Data.Product using (Σ; _,_; proj₁; proj₂)
  open import Data.Product.Properties using (,-injective)
  open import Data.List using (List; []; [_]; _∷_; map; deduplicate; filter; cartesianProduct)
  open import Data.List.Relation.Unary.All using (All)
  open import Data.List.Relation.Unary.Any using (any?)
  open import Data.List.Relation.Unary.AllPairs using (AllPairs)

  open import Graph.Core.Definitions using (v-V; +-Vˡ; +-Vʳ; *-Vˡ; *-Vʳ)
  open import Graph.Common.Algo.List
  open import Graph.Common.Algo.List.Properties
  open import Graph.Common.Algo.List.Properties.Cartesian
  
  ×-≟ : {A B : Set} → DecidableEquality A → DecidableEquality B →  DecidableEquality (A × B)
  ×-≟ _≟ᴬ_ _≟ᴮ_ (x₁ , y₁) (x₂ , y₂) with x₁ ≟ᴬ x₂ | y₁ ≟ᴮ y₂
  ... | no x₁≠x₂ | _        = no λ { refl → x₁≠x₂ refl}
  ... | yes _    | no y₁≠y₂ = no λ { refl → y₁≠y₂ refl}
  ... | yes refl | yes refl = yes refl

  _≟ᴱ_ : DecidableEquality (L × L)
  _≟ᴱ_ = ×-≟ _≟ᴸ_ _≟ᴸ_

  _++ᴸ_ = _++ᵘ_ {L} {_≟ᴸ_}

  vertices : Graph → List L
  vertices ε = []
  vertices (v x) = [ x ]
  vertices (g₁ + g₂) = vertices g₁ ++ᴸ vertices g₂
  vertices (g₁ * g₂) = vertices g₁ ++ᴸ vertices g₂

  edges : Graph → List (L × L)
  edges g = deduplicate _≟ᴱ_ (filter (λ { (x , y) → E-of? g x y}) (cartesianProduct (vertices g) (vertices g)))

  adjacency-list : Graph → List (L × List L)
  adjacency-list g = map (λ x → x , (filter (E-of? g x) (vertices g))) (vertices g)

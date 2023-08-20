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
  open import Agda.Builtin.Equality using (refl)
  open import Function using (_∘_)
  open import Relation.Nullary using (no; yes)
  open import Data.Sum using ([_,_]′)
  open import Data.Product using (_,_; proj₁; proj₂)
  open import Data.List using (List; []; [_]; deduplicate; filter; cartesianProduct)
  open import Data.List.Relation.Unary.All using (All)
  open import Data.List.Relation.Unary.AllPairs using (AllPairs)
  open import Data.List.Relation.Unary.Unique.Propositional using (Unique)

  open import Graph.Core.Definitions using (v-V; +-Vˡ; +-Vʳ; *-Vˡ; *-Vʳ)
  import Graph.Common.Algo.List
  module C = Graph.Common.Algo.List.Core
  module P = Graph.Common.Algo.List.Cartesian

  module _ where
    open C {L} {_≟ᴸ_}

    vertices : Graph → List L
    vertices ε = []
    vertices (v x) = [ x ]
    vertices (g₁ + g₂) = vertices g₁ ++ᵘ vertices g₂
    vertices (g₁ * g₂) = vertices g₁ ++ᵘ vertices g₂

    vertices-unique : (g : Graph) → Unique (vertices g)
    vertices-unique ε = AllPairs.[]
    vertices-unique (v x) = All.[] AllPairs.∷ AllPairs.[]
    vertices-unique (g₁ + g₂) = ++ᵘ-unique (vertices g₁) (vertices g₂) (vertices-unique g₁) (vertices-unique g₂)
    vertices-unique (g₁ * g₂) = ++ᵘ-unique (vertices g₁) (vertices g₂) (vertices-unique g₁) (vertices-unique g₂)

    ∈V⇒∈v : {x : L} → (g : Graph) → x ∈V[ g ] → x ∈ (vertices g)
    ∈V⇒∈v (v x) v-V = here
    ∈V⇒∈v (g₁ + g₂) (+-Vˡ x∈V) = ∈ˡ⇒∈++ (vertices g₁) (vertices g₂) (∈V⇒∈v g₁ x∈V)
    ∈V⇒∈v (g₁ + g₂) (+-Vʳ x∈V) = ∈ʳ⇒∈++ (vertices g₁) (vertices g₂) (∈V⇒∈v g₂ x∈V)
    ∈V⇒∈v (g₁ * g₂) (*-Vˡ x∈V) = ∈ˡ⇒∈++ (vertices g₁) (vertices g₂) (∈V⇒∈v g₁ x∈V)
    ∈V⇒∈v (g₁ * g₂) (*-Vʳ x∈V) = ∈ʳ⇒∈++ (vertices g₁) (vertices g₂) (∈V⇒∈v g₂ x∈V)

    ∈v⇒∈V : {x : L} → (g : Graph) → x ∈ (vertices g) → x ∈V[ g ]
    ∈v⇒∈V (v x) here = v-V
    ∈v⇒∈V (g₁ + g₂) x∈v = [ +-Vˡ ∘ (∈v⇒∈V g₁) , +-Vʳ ∘ ∈v⇒∈V g₂ ]′ (∈++⇒∈ˡ⊎∈ʳ (vertices g₁) (vertices g₂) x∈v)
    ∈v⇒∈V (g₁ * g₂) x∈v = [ *-Vˡ ∘ (∈v⇒∈V g₁) , *-Vʳ ∘ (∈v⇒∈V g₂) ]′ (∈++⇒∈ˡ⊎∈ʳ (vertices g₁) (vertices g₂) x∈v)

  module _ where
    _≟ᴱ_ : DecidableEquality (L × L)
    _≟ᴱ_ (x₁ , y₁) (x₂ , y₂) with x₁ ≟ᴸ x₂ | y₁ ≟ᴸ y₂
    ... | no  x₁≠x₂ | _         = no λ { refl → x₁≠x₂ refl}
    ... | yes _     | no  y₁≠y₂ = no λ { refl → y₁≠y₂ refl}
    ... | yes refl  | yes refl = yes refl
    
    open C {L × L} {_≟ᴱ_}
    open P {L} {L} {_≟ᴸ_} {_≟ᴸ_} {_≟ᴱ_}
  
    edges : Graph → List (L × L)
    edges g = deduplicate _≟ᴱ_ (filter (λ { (x , y) → E-of? g x y}) (cartesianProduct (vertices g) (vertices g)))

    edges-unique : (g : Graph) → Unique (edges g)
    edges-unique g = unique-deduplicate (filter (λ { (x , y) → E-of? g x y}) (cartesianProduct (vertices g) (vertices g)))

    ∈E⇒∈e : {x y : L} → (g : Graph) → x ↦ y ∈E[ g ] → (x , y) ∈ (edges g)
    ∈E⇒∈e {x} {y} g xy∈E = ∈-deduplicate (filter (λ { (x , y) → E-of? g x y}) (cartesianProduct (vertices g) (vertices g)))
      (∈-filter (λ (x , y) → x ↦ y ∈E[ g ]) (λ { (x , y) → E-of? g x y}) xy∈E (cartesianProduct (vertices g) (vertices g))
      (∈-cartesianProduct (vertices g) (vertices g)
      (∈V⇒∈v g (proj₁ (lemma-soundness g xy∈E))) (∈V⇒∈v g (proj₂ (lemma-soundness g xy∈E)))))

    ∈e⇒∈E : {x y : L} → (g : Graph) → (x , y) ∈ (edges g) → x ↦ y ∈E[ g ]
    ∈e⇒∈E g xy∈e = AllP⇒Px (all-deduplicate (all-filter (λ { (x , y) → E-of? g x y}) (cartesianProduct (vertices g) (vertices g)))) xy∈e
      

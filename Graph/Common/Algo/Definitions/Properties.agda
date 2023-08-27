open import Graph.Core
open import Graph.Core.Definitions using(_∈V[_])
open import Relation.Nullary using (Dec)
open import Relation.Binary using (DecidableEquality; _⇒_)
open import Data.Product using (_×_)
module Graph.Common.Algo.Definitions.Properties
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
  open import Data.List.Relation.Unary.Unique.Propositional using (Unique)

  open import Graph.Core.Definitions using (v-V; +-Vˡ; +-Vʳ; *-Vˡ; *-Vʳ)
  open import Graph.Common.Algo.Definitions {L} {_≟ᴸ_} {_↦_∈E[_]} {E-of?} {lemma-soundness}
  open import Graph.Common.Algo.List
  open import Graph.Common.Algo.List.Properties
  open import Graph.Common.Algo.List.Properties.Cartesian
 
  _∈ᴸ_ = _∈_ {L} {_≟ᴸ_}
  listᴸ-≟ = list-≟ {L} {_≟ᴸ_}
  _∈ᴱ_ = _∈_ {L × L} {×-≟ _≟ᴸ_ _≟ᴸ_}
  unique-deduplicateᴱ = unique-deduplicate {L × L} {×-≟ _≟ᴸ_ _≟ᴸ_}
  all-deduplicateᴱ = all-deduplicate {L × L} {×-≟ _≟ᴸ_ _≟ᴸ_}
  all-filterᴱ = all-filter {L × L} {×-≟ _≟ᴸ_ _≟ᴸ_}
  _∈ˣ_ = _∈_ {L × List L} {×-≟ _≟ᴸ_ listᴸ-≟}
  
  --==== vertices ====--

  vertices-unique : (g : Graph) → Unique (vertices g)
  vertices-unique ε = AllPairs.[]
  vertices-unique (v x) = All.[] AllPairs.∷ AllPairs.[]
  vertices-unique (g₁ + g₂) = ++ᵘ-unique (vertices g₁) (vertices g₂) (vertices-unique g₁) (vertices-unique g₂)
  vertices-unique (g₁ * g₂) = ++ᵘ-unique (vertices g₁) (vertices g₂) (vertices-unique g₁) (vertices-unique g₂)

  ∈V⇒∈v : {x : L} → (g : Graph) → x ∈V[ g ] → x ∈ᴸ (vertices g)
  ∈V⇒∈v (v x) v-V = here
  ∈V⇒∈v (g₁ + g₂) (+-Vˡ x∈V) = ∈ˡ⇒∈++ (vertices g₁) (vertices g₂) (∈V⇒∈v g₁ x∈V)
  ∈V⇒∈v (g₁ + g₂) (+-Vʳ x∈V) = ∈ʳ⇒∈++ (vertices g₁) (vertices g₂) (∈V⇒∈v g₂ x∈V)
  ∈V⇒∈v (g₁ * g₂) (*-Vˡ x∈V) = ∈ˡ⇒∈++ (vertices g₁) (vertices g₂) (∈V⇒∈v g₁ x∈V)
  ∈V⇒∈v (g₁ * g₂) (*-Vʳ x∈V) = ∈ʳ⇒∈++ (vertices g₁) (vertices g₂) (∈V⇒∈v g₂ x∈V)

  ∈v⇒∈V : {x : L} → (g : Graph) → x ∈ (vertices g) → x ∈V[ g ]
  ∈v⇒∈V (v x) here = v-V
  ∈v⇒∈V (g₁ + g₂) x∈v = [ +-Vˡ ∘ (∈v⇒∈V g₁) , +-Vʳ ∘ ∈v⇒∈V g₂ ]′ (∈++⇒∈ˡ⊎∈ʳ (vertices g₁) (vertices g₂) x∈v)
  ∈v⇒∈V (g₁ * g₂) x∈v = [ *-Vˡ ∘ (∈v⇒∈V g₁) , *-Vʳ ∘ (∈v⇒∈V g₂) ]′ (∈++⇒∈ˡ⊎∈ʳ (vertices g₁) (vertices g₂) x∈v)

  --==== edges ====--

  edges-unique : (g : Graph) → Unique (edges g)
  edges-unique g = unique-deduplicateᴱ (filter (λ { (x , y) → E-of? g x y}) (cartesianProduct (vertices g) (vertices g)))

  ∈E⇒∈e : {x y : L} → (g : Graph) → x ↦ y ∈E[ g ] → (x , y) ∈ᴱ (edges g)
  ∈E⇒∈e {x} {y} g xy∈E = ∈-deduplicate (filter (λ { (x , y) → E-of? g x y}) (cartesianProduct (vertices g) (vertices g)))
    (∈-filter (λ (x , y) → x ↦ y ∈E[ g ]) (λ { (x , y) → E-of? g x y}) xy∈E (cartesianProduct (vertices g) (vertices g))
    (∈-cartesianProduct (vertices g) (vertices g)
    (∈V⇒∈v g (proj₁ (lemma-soundness g xy∈E))) (∈V⇒∈v g (proj₂ (lemma-soundness g xy∈E)))))

  ∈e⇒∈E : {x y : L} → (g : Graph) → (x , y) ∈ᴱ (edges g) → x ↦ y ∈E[ g ]
  ∈e⇒∈E g xy∈e = AllP⇒Px (all-deduplicateᴱ (all-filterᴱ (λ { (x , y) → E-of? g x y}) (cartesianProduct (vertices g) (vertices g)))) xy∈e

  --==== adjacency-list ====--

  adj≠[]⇒vertices≠[] : {g : Graph} → ¬ (adjacency-list g ≡ []) → ¬ (vertices g ≡ [])
  adj≠[]⇒vertices≠[] {g} adj≠[] with vertices g | listᴸ-≟ (vertices g) []
  ... | [] | no ver≠[] = ver≠[]
  ... | x ∷ vs | no ver≠[] = λ ()
  ... | .[] | yes refl  = λ { refl → adj≠[] refl}

  vertices≠[]⇒adj≠[] : {g : Graph} → ¬ (vertices g ≡ []) → ¬ (adjacency-list g ≡ [])
  vertices≠[]⇒adj≠[] {g} ver≠[] with vertices g
  ... | [] = λ { refl → ver≠[] refl}
  ... | x ∷ vs = λ ()

  ∈E⇒∈adj : {x y : L} (g : Graph) → x ↦ y ∈E[ g ] → Σ (List L) (λ ys → (y ∈ᴸ ys) × ((x , ys) ∈ˣ adjacency-list g))
  ∈E⇒∈adj {x} {y} g ∈E with ∈V⇒∈v g (proj₁ (lemma-soundness g ∈E)) | ∈V⇒∈v g (proj₂ (lemma-soundness g ∈E))
  ... | x∈vs | y∈vs =
    let vs : List L
        vs = vertices g
        ys : List L
        ys = filter (E-of? g x) vs
        y∈ys : y ∈ᴸ ys
        y∈ys = ∈-filter (x ↦_∈E[ g ]) (E-of? g x) ∈E vs y∈vs
        x,ys∈adj : (x , filter (E-of? g x) vs) ∈ˣ (map (λ x₁ → x₁ , (filter (E-of? g x₁) vs)) vs)
        x,ys∈adj = ∈-map (λ x₁ → x₁ , (filter (E-of? g x₁) vs)) x∈vs
    in ys , y∈ys , x,ys∈adj

  ∈adj⇒∈E : {x y : L} {ys : List L} (g : Graph) → (x , ys) ∈ˣ adjacency-list g → y ∈ᴸ ys → x ↦ y ∈E[ g ]
  ∈adj⇒∈E g xys∈adj y∈ys = go (vertices g) xys∈adj y∈ys where
    go : {x y : L} {ys : List L} → (l₂ : List L) → (x , ys) ∈ˣ map (λ x₁ → x₁ , (filter (E-of? g x₁) (vertices g))) l₂ → y ∈ᴸ ys → x ↦ y ∈E[ g ]
    go (x ∷ l₂) here y∈ys = x∈filter⇒Px _ (E-of? g x) (vertices g) y∈ys
    go (_ ∷ l₂) (there ∈map) y∈ys = go l₂ ∈map y∈ys



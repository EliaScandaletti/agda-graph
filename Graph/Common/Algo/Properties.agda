open import Relation.Nullary using (Dec)
open import Relation.Binary using (DecidableEquality)
open import Data.Product using (_×_)
open import Data.List using (List)
open import Data.List.Membership.DecPropositional using (_∈_)
module Graph.Common.Algo.Properties
    {L Graph : Set} {_≟ᴸ_ : DecidableEquality L}
    {_∈V[_] : L → Graph → Set}
    (vertices : Graph → List L)
    (∈V⇒∈v : {x : L} → (g : Graph) → x ∈V[ g ] → _∈_ _≟ᴸ_ x (vertices g))  
    (∈v⇒∈V : {x : L} → (g : Graph) → _∈_ _≟ᴸ_ x (vertices g) → x ∈V[ g ])  
    {_↦_∈E[_] : L → L → Graph → Set}
    (E-of? : (g : Graph) → (x y : L) → Dec (x ↦ y ∈E[ g ]))
    (lemma-soundness : {x y : L} → (g : Graph) → x ↦ y ∈E[ g ] → x ∈V[ g ] × y ∈V[ g ]) where
  open import Agda.Builtin.Equality using (refl)
  open import Relation.Nullary using (no; yes)
  open import Data.Product using (Σ; _,_; proj₁; proj₂)
  open import Data.List using (_∷_; map; filter; cartesianProduct)
  open import Data.List.Relation.Unary.Any using (here; there)

  open import Graph.Common.Algo.Definitions vertices E-of?
  open import Algo.List.Properties
  open import Algo.List.Properties.Cartesian
 
  ×-≟ : {A B : Set} → DecidableEquality A → DecidableEquality B →  DecidableEquality (A × B)
  ×-≟ _≟ᴬ_ _≟ᴮ_ (x₁ , y₁) (x₂ , y₂) with x₁ ≟ᴬ x₂ | y₁ ≟ᴮ y₂
  ... | no x₁≠x₂ | _        = no λ { refl → x₁≠x₂ refl}
  ... | yes _    | no y₁≠y₂ = no λ { refl → y₁≠y₂ refl}
  ... | yes refl | yes refl = yes refl

  _∈ᴸ_ = _∈_ _≟ᴸ_
  _≟ᴱ_ = ×-≟ _≟ᴸ_ _≟ᴸ_
  _∈ᴱ_ = _∈_ _≟ᴱ_
  _≟ˣ_ = ×-≟ _≟ᴸ_ (list-≟ _≟ᴸ_)
  _∈ˣ_ = _∈_ _≟ˣ_

  --==== edges ====--

  ∈E⇒∈e : {x y : L} → (g : Graph) → x ↦ y ∈E[ g ] → (x , y) ∈ᴱ (edges g)
  ∈E⇒∈e {x} {y} g xy∈E = ∈-filter _≟ᴱ_ (λ { (x , y) → E-of? g x y}) xy∈E (cartesianProduct (vertices g) (vertices g))
                         (∈-cartesianProduct _≟ᴸ_ _≟ᴸ_ _≟ᴱ_ (vertices g) (vertices g)
                           (∈V⇒∈v g (proj₁ (lemma-soundness g xy∈E)))
                           (∈V⇒∈v g (proj₂ (lemma-soundness g xy∈E))))

  ∈e⇒∈E : {x y : L} → (g : Graph) → (x , y) ∈ᴱ (edges g) → x ↦ y ∈E[ g ]
  ∈e⇒∈E g xy∈e = AllP⇒Px _≟ᴱ_ (all-filter _≟ᴱ_ (λ { (x , y) → E-of? g x y}) (cartesianProduct (vertices g) (vertices g))) xy∈e

  --==== adjacency-list ====--

  ∈E⇒∈adj : {x y : L} (g : Graph) → x ↦ y ∈E[ g ] → Σ (List L) (λ ys → (y ∈ᴸ ys) × ((x , ys) ∈ˣ adjacency-list g))
  ∈E⇒∈adj {x} {y} g ∈E with ∈V⇒∈v g (proj₁ (lemma-soundness g ∈E)) | ∈V⇒∈v g (proj₂ (lemma-soundness g ∈E))
  ... | x∈vs | y∈vs =
    let vs : List L
        vs = vertices g
        ys : List L
        ys = filter (E-of? g x) vs
        y∈ys : y ∈ᴸ ys
        y∈ys = ∈-filter _≟ᴸ_ (E-of? g x) ∈E (vertices g) y∈vs
        x,ys∈adj : (x , filter (E-of? g x) vs) ∈ˣ (map (λ x₁ → x₁ , (filter (E-of? g x₁) vs)) vs)
        x,ys∈adj = ∈-map _≟ᴸ_ _≟ˣ_ (λ x₁ → x₁ , (filter (E-of? g x₁) vs)) x∈vs
    in ys , y∈ys , x,ys∈adj

  ∈adj⇒∈E : {x y : L} {ys : List L} (g : Graph) → (x , ys) ∈ˣ adjacency-list g → y ∈ᴸ ys → x ↦ y ∈E[ g ]
  ∈adj⇒∈E g xys∈adj y∈ys = go (vertices g) xys∈adj y∈ys where
    go : {x y : L} {ys : List L} → (l₂ : List L) → (x , ys) ∈ˣ map (λ x₁ → x₁ , (filter (E-of? g x₁) (vertices g))) l₂ → y ∈ᴸ ys → x ↦ y ∈E[ g ]
    go (x ∷ l₂) (here refl) y∈ys = x∈filter⇒Px _≟ᴸ_ _ (E-of? g x) (vertices g) y∈ys
    go (_ ∷ l₂) (there ∈map) y∈ys = go l₂ ∈map y∈ys
 
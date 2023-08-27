open import Relation.Binary using (DecidableEquality)
open import Data.Product using (_×_)
module Graph.Common.Algo.List.Properties.Cartesian {A B : Set}
  {_≟ᴬ_ : DecidableEquality A} {_≟ᴮ_ : DecidableEquality B} {_≟ˣ_ : DecidableEquality (A × B)}
  where
    open import Data.Product using (_,_)
    open import Data.List using (List; _∷_; map; cartesianProduct)

    open import Graph.Common.Algo.List {A} {_≟ᴬ_} renaming (_∈_ to _∈ᴬ_; here to hereᴬ; there to thereᴬ)
    open import Graph.Common.Algo.List {B} {_≟ᴮ_} renaming (_∈_ to _∈ᴮ_; here to hereᴮ; there to thereᴮ)
    open import Graph.Common.Algo.List {A × B} {_≟ˣ_} renaming (_∈_ to _∈ˣ_; here to hereˣ; there to thereˣ)

    open import Graph.Common.Algo.List.Properties 
  
    ∈-cartesianProduct : {x₁ : A} {x₂ : B} (l₁ : List A) → (l₂ : List B) → x₁ ∈ᴬ l₁ → x₂ ∈ᴮ l₂ → (x₁ , x₂) ∈ˣ (cartesianProduct l₁ l₂)
    ∈-cartesianProduct (x ∷ l₁) (x₁ ∷ l₂) hereᴬ hereᴮ = hereˣ
    ∈-cartesianProduct (x₁′ ∷ l₁) (x₂′ ∷ l₂′) hereᴬ (thereᴮ x₂∈l₂′) = ∈-++ˡ ((x₁′ , x₂′) ∷ map (x₁′ ,_) l₂′) (cartesianProduct l₁ (x₂′ ∷ l₂′)) (thereˣ (∈-map (x₁′ ,_) x₂∈l₂′))
    ∈-cartesianProduct (x₁′ ∷ l₁) (x₂′ ∷ l₂′) (thereᴮ x₁∈l₁) x₂∈l₂ = ∈-++ʳ ((x₁′ , x₂′) ∷ map (x₁′ ,_) l₂′) (cartesianProduct l₁ (x₂′ ∷ l₂′)) (∈-cartesianProduct l₁ (x₂′ ∷ l₂′) x₁∈l₁ x₂∈l₂)



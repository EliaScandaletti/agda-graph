open import Relation.Binary using (DecidableEquality)
open import Data.Product using (_×_)
module Algo.List.Properties.Cartesian {A B : Set}
  (_≟ᴬ_ : DecidableEquality A) (_≟ᴮ_ : DecidableEquality B) (_≟ˣ_ : DecidableEquality (A × B))
  where
    open import Agda.Builtin.Equality using (refl)
    open import Data.Product using (_,_)
    open import Data.List using (List; _∷_; map; cartesianProduct)
    open import Data.List.Membership.DecPropositional _≟ᴬ_ renaming (_∈_ to _∈ᴬ_)
    open import Data.List.Membership.DecPropositional _≟ᴮ_ renaming (_∈_ to _∈ᴮ_)
    open import Data.List.Membership.DecPropositional _≟ˣ_ renaming (_∈_ to _∈ˣ_)
    open import Data.List.Relation.Unary.Any using (here; there)

    open import Algo.List.Properties
  
    ∈-cartesianProduct : {x₁ : A} {x₂ : B} (l₁ : List A) → (l₂ : List B) → x₁ ∈ᴬ l₁ → x₂ ∈ᴮ l₂ → (x₁ , x₂) ∈ˣ (cartesianProduct l₁ l₂)
    ∈-cartesianProduct (x ∷ l₁)   (x₁ ∷ l₂) (here refl) (here refl)    = here refl
    ∈-cartesianProduct (x₁′ ∷ l₁) (x₂′ ∷ l₂′) (here refl) (there x₂∈l₂′) = ∈-++ˡ _≟ˣ_ ((x₁′ , x₂′) ∷ map (x₁′ ,_) l₂′) (cartesianProduct l₁ (x₂′ ∷ l₂′)) (there (∈-map _≟ᴮ_ _≟ˣ_ (x₁′ ,_) x₂∈l₂′))
    ∈-cartesianProduct (x₁′ ∷ l₁) (x₂′ ∷ l₂′) (there x₁∈l₁) x₂∈l₂ = ∈-++ʳ _≟ˣ_ ((x₁′ , x₂′) ∷ map (x₁′ ,_) l₂′) (cartesianProduct l₁ (x₂′ ∷ l₂′)) (∈-cartesianProduct l₁ (x₂′ ∷ l₂′) x₁∈l₁ x₂∈l₂)

open import Relation.Binary using (DecidableEquality)
module Graph.Common.Algo.List {A : Set} {_≟_ : DecidableEquality A} where
  open import Agda.Builtin.Equality using (_≡_; refl)
  open import Relation.Nullary using (Dec; ¬_; ¬?; no; yes; Reflects; ofⁿ; ofʸ)
  open import Relation.Nullary.Decidable using (does)
  open import Relation.Unary renaming (Decidable to Dec₁) hiding (_∈_; _∉_)
  open import Relation.Binary renaming (Decidable to Dec₂)
  open import Data.Empty using (⊥-elim)
  open import Data.Sum using (_⊎_; inj₁; inj₂; map₁)
  open import Data.Product using (Σ; _×_; _,_)
  open import Data.Bool using (not)
  open import Data.List using (List; []; _∷_; _++_; filter; deduplicate; cartesianProduct; map)
  open import Data.List.Relation.Unary.All using (All)
  open import Data.List.Relation.Unary.AllPairs using (AllPairs)
  open import Data.List.Relation.Unary.Unique.Propositional using (Unique)

  data _∈_ (x : A) : List A → Set where
    here  : {xs : List A} → x ∈ (x ∷ xs)
    there : {y : A} {xs : List A} → x ∈ xs → x ∈ (y ∷ xs)

  _∉_ : A → List A → Set
  _∉_ x xs = ¬ (x ∈ xs)
  

open import Relation.Binary using (DecidableEquality)
module Algo.List.Properties {A : Set} (_≟_ : DecidableEquality A) where
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
  open import Data.List.Membership.DecPropositional _≟_ using (_∈_; _∉_; _∈?_)
  open import Data.List.Relation.Unary.Any using (here; there)
  open import Data.List.Relation.Unary.All using (All)
  open import Data.List.Relation.Unary.AllPairs using (AllPairs)
  open import Data.List.Relation.Unary.Unique.Propositional using (Unique)

  list-≟ : (l₁ l₂ : List A) → Dec (l₁ ≡ l₂)
  list-≟ [] [] = yes refl
  list-≟ [] (_ ∷ _) = no (λ ())
  list-≟ (_ ∷ _) [] = no (λ ())
  list-≟ (x₁ ∷ l₁) (x₂ ∷ l₂) with x₁ ≟ x₂ | list-≟ l₁ l₂
  ... | no  x₁≠x₂ | _ = no λ { refl → x₁≠x₂ refl}
  ... | yes refl  | no l₁≠l₂ = no λ { refl → l₁≠l₂ refl}
  ... | yes refl  | yes refl = yes refl
                                     
  _≠?_ : (x₁ x₂ : A) → Dec (¬ x₁ ≡ x₂)
  x₁ ≠? x₂ = ¬? (x₁ ≟ x₂)

  All≠⇒∉ : {x : A} {xs : List A} → All (λ y → ¬ x ≡ y) xs → x ∉ xs
  All≠⇒∉ All.[] = λ ()
  All≠⇒∉ (x≠x₁ All.∷ All≠) = λ { (here refl) → x≠x₁ refl ; (there x∈xs) → All≠⇒∉ All≠ x∈xs}
  
  ∉⇒All≠ : {x : A} {xs : List A} → x ∉ xs → All (λ y → ¬ x ≡ y) xs
  ∉⇒All≠ {xs = []} x∉xs = All.[]
  ∉⇒All≠ {xs = x₁ ∷ xs} x∉x₁xs = (λ { refl → x∉x₁xs (here refl)}) All.∷ ∉⇒All≠ λ { x∈xs → x∉x₁xs (there x∈xs)}
  
  ∈ʳ⇒∈++ : {x : A} → (xs ys : List A) → x ∈ ys → x ∈ (xs ++ ys)
  ∈ʳ⇒∈++ [] ys x∈ys = x∈ys
  ∈ʳ⇒∈++ (x₁ ∷ xs) ys x∈ys = there (∈ʳ⇒∈++ xs ys x∈ys)
  
  ∈ˡ⇒∈++ : {x : A} → (xs ys : List A) → x ∈ xs → x ∈ (xs ++ ys)
  ∈ˡ⇒∈++ (x ∷ xs) ys (here refl) = here refl
  ∈ˡ⇒∈++ (x ∷ xs) ys (there x∈xs) = there (∈ˡ⇒∈++ xs ys x∈xs)

  ∈++⇒∈ˡ⊎∈ʳ : {x : A} (xs ys : List A) → x ∈ (xs ++ ys) → (x ∈ xs) ⊎ (x ∈ ys)
  ∈++⇒∈ˡ⊎∈ʳ [] ys x∈++ = inj₂ x∈++
  ∈++⇒∈ˡ⊎∈ʳ (x₁ ∷ xs) ys (here refl) = inj₁ (here refl)
  ∈++⇒∈ˡ⊎∈ʳ (x₁ ∷ xs) ys (there x∈++) = map₁ there (∈++⇒∈ˡ⊎∈ʳ xs ys x∈++)

  x∈filter⇒Px : {P : A → Set} → (x : A) → (P? : Dec₁ P) → (l : List A) → x ∈ (filter P? l) → P x
  x∈filter⇒Px x P? (x′ ∷ l) x∈fPl with P? x′
  ... | no ¬Px′ = x∈filter⇒Px x P? l x∈fPl
  ... | yes Px′ with x∈fPl
  ... | (here refl) = Px′
  ... | there x∈fPl = x∈filter⇒Px x P? l x∈fPl
        
  ∉-filter : {x : A} {P : A → Set} (P? : Dec₁ P) → ¬ (P x) → (l : List A) → x ∉ (filter P? l)
  ∉-filter P? ¬Px [] = λ ()
  ∉-filter {x} P? ¬Px (x₁ ∷ l) with P? x₁
  ... | no ¬Px₁ = ∉-filter P? ¬Px l
  ... | yes Px₁ with x ≟ x₁
  ... | no  x≠x₁ = λ { (here refl) → x≠x₁ refl ; (there x∈fPl) → ¬Px (x∈filter⇒Px x P? l x∈fPl)}
  ... | yes refl = ⊥-elim (¬Px Px₁)

  all-filter₂ : {P Q : A → Set} (P? : Dec₁ P) → (l : List A) → All Q l → All Q (filter P? l)
  all-filter₂ P? [] All.[] = All.[]
  all-filter₂ P? (x ∷ l) (Qx All.∷ AQl) with P? x
  ... | no ¬Px = all-filter₂ P? l AQl
  ... | yes Px = Qx All.∷ all-filter₂ P? l AQl

  unique-filter : {P : A → Set} (P? : Dec₁ P) → (l : List A) → Unique l → Unique (filter P? l)
  unique-filter P? [] Ul = Ul
  unique-filter P? (x ∷ l) (x₁ AllPairs.∷ Ul) with P? x
  ... | no ¬Px = unique-filter P? l Ul
  ... | yes Px = all-filter₂ P? l x₁ AllPairs.∷ unique-filter P? l Ul

  all-filter : {P : A → Set} (P? : Dec₁ P) → (l : List A) → All P (filter P? l)
  all-filter P? [] = All.[]
  all-filter P? (x ∷ l) with P? x
  ... | no ¬Px = all-filter P? l
  ... | yes Px = Px All.∷ (all-filter P? l)

  all-deduplicate : {l : List A} {P : A → Set} → All P l → All P (deduplicate _≟_ l)
  all-deduplicate All.[] = All.[]
  all-deduplicate (All._∷_ {x} {l} Px APl) = Px All.∷ all-filter₂ (x ≠?_) (deduplicate _≟_ l) (all-deduplicate APl)

  unique-deduplicate : (l : List A) → Unique (deduplicate _≟_ l)
  unique-deduplicate [] = AllPairs.[]
  unique-deduplicate (x ∷ l) = all-filter (x ≠?_) (deduplicate _≟_ l) AllPairs.∷ unique-filter (x ≠?_) (deduplicate _≟_ l) (unique-deduplicate l)

  AllP⇒Px : {x : A} {l : List A} {P : A → Set} → All P l → x ∈ l → P x
  AllP⇒Px (Px All.∷ _) (here refl) = Px
  AllP⇒Px (_ All.∷ APl) (there x∈l) = AllP⇒Px APl x∈l

  ∈-filter : {x : A} {P : A → Set} → (P? : Dec₁ P) → P x → (l : List A) → x ∈ l → x ∈ (filter P? l)
  ∈-filter P? Px (x ∷ l′) (here refl) with P? x
  ... | no ¬Px = ⊥-elim (¬Px Px)
  ... | yes Px = here refl
  ∈-filter P? Px (x₁ ∷ l′) (there x∈l′) with P? x₁
  ... | no ¬Px₁ = ∈-filter P? Px l′ x∈l′
  ... | yes Px₁ = there (∈-filter P? Px l′ x∈l′)

  filter-∈ : {x : A} {P : A → Set} → (P? : Dec₁ P) → P x → (l : List A) → x ∈ (filter P? l) → x ∈ l
  filter-∈ P? Px (x′ ∷ l) x∈f with P? x′
  ... | no ¬Px′ = there (filter-∈ P? Px l x∈f)
  filter-∈ P? Px (x′ ∷ l) (here refl) | yes Px′ = here refl
  filter-∈ P? Px (x′ ∷ l) (there x∈f) | yes Px′ = there (filter-∈ P? Px l x∈f)

  ∈-deduplicate : {x : A} → (l : List A) → x ∈ l → x ∈ deduplicate _≟_ l
  ∈-deduplicate (x ∷ l′) (here refl) = here refl
  ∈-deduplicate {x} (x₁ ∷ l′) (there x∈l′) with x₁ ≟ x
  ... | no  x₁≠x = there (∈-filter (x₁ ≠?_) x₁≠x (deduplicate _≟_ l′) (∈-deduplicate l′ x∈l′))
  ... | yes refl = here refl

  deduplicate-∈ : {x : A} → (l : List A) → x ∈ deduplicate _≟_ l → x ∈ l
  deduplicate-∈ (_ ∷ _) (here refl) = here refl
  deduplicate-∈ {x} (x′ ∷ l) (there x∈d) with x′ ≟ x
  deduplicate-∈ {x} (x′ ∷ l) (there x∈d) | no ¬p = there (deduplicate-∈ l (filter-∈ (λ x₁ → ¬? (x′ ≟ x₁)) ¬p (deduplicate _≟_ l) x∈d))
  ... | yes refl = here refl

  ∈-++ˡ : (l : List A) (l′ : List A) → {x : A} → x ∈ l → x ∈ (l ++ l′)
  ∈-++ˡ (x ∷ _) l′ (here refl) = here refl
  ∈-++ˡ (_ ∷ l) l′ (there x∈l) = there (∈-++ˡ l l′ x∈l)

  ∈-++ʳ : (l′ : List A) (l : List A) → {x : A} → x ∈ l → x ∈ (l′ ++ l)
  ∈-++ʳ [] l x∈l = x∈l
  ∈-++ʳ (x′ ∷ l′) l x∈l = there (∈-++ʳ l′ l x∈l)

  module _ {B : Set} (_≟ᴮ_ : DecidableEquality B) where
    open import Data.List.Membership.DecPropositional _≟ᴮ_ renaming (_∈_ to _∈ᴮ_)
    ∈-map : {x : A} {l : List A} (f : A → B) → x ∈ l → f x ∈ᴮ map f l
    ∈-map f (here refl) = here refl
    ∈-map f (there x∈l) = there (∈-map f x∈l)
 

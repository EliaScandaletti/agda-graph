open import Relation.Binary using (DecidableEquality)
module Graph.Common.Algo.List.Properties {A : Set} {_≟_ : DecidableEquality A} where
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

  open import Graph.Common.Algo.List {A} {_≟_}

  _∈?_ : Dec₂ _∈_
  x ∈? [] = no λ ()
  x ∈? (x₁ ∷ xs) with x ≟ x₁
  ... | yes refl = yes here
  ... | no  x≠x₁ with x ∈? xs
  ... | no  x∉xs = no (λ { here → x≠x₁ refl ; (there x∈xs) → x∉xs x∈xs})
  ... | yes x∈xs = yes (there x∈xs)

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
  
  _++ᵘ_ : (xs ys : List A) → List A
  [] ++ᵘ ys = ys
  (x ∷ xs) ++ᵘ ys with x ∈? ys
  ... | no  _ = x ∷ (xs ++ᵘ ys)
  ... | yes _ = xs ++ᵘ ys

  ∉-++ᵘ : (x : A) → (xs ys : List A) → x ∉ xs → x ∉ ys → x ∉ (xs ++ᵘ ys)
  ∉-++ᵘ x [] ys x∉xs x∉ys = x∉ys
  ∉-++ᵘ x (x₁ ∷ xs) ys x∉x₁xs x∉ys with x₁ ∈? ys
  ... | no  x₁∉ys = λ { here → x∉x₁xs here ; (there x∈xs++ys) → ∉-++ᵘ x xs ys (λ x∈xs → x∉x₁xs (there x∈xs)) x∉ys x∈xs++ys}
  ... | yes x₁∈ys = ∉-++ᵘ x xs ys (λ x∈xs → x∉x₁xs (there x∈xs)) x∉ys

  All≠⇒∉ : {x : A} {xs : List A} → All (λ y → ¬ x ≡ y) xs → x ∉ xs
  All≠⇒∉ All.[] = λ ()
  All≠⇒∉ (x≠x₁ All.∷ All≠) = λ { here → x≠x₁ refl ; (there x∈xs) → All≠⇒∉ All≠ x∈xs}
  
  ∉⇒All≠ : {x : A} {xs : List A} → x ∉ xs → All (λ y → ¬ x ≡ y) xs
  ∉⇒All≠ {xs = []} x∉xs = All.[]
  ∉⇒All≠ {xs = x₁ ∷ xs} x∉x₁xs = (λ { refl → x∉x₁xs here}) All.∷ ∉⇒All≠ λ { x∈xs → x∉x₁xs (there x∈xs)}
  
  ++ᵘ-unique : (xs ys : List A) → Unique xs → Unique ys → Unique (xs ++ᵘ ys)
  ++ᵘ-unique [] ys Uxs Uys = Uys
  ++ᵘ-unique (x ∷ xs) ys (x∉xs AllPairs.∷ Uxs) Uys with x ∈? ys
  ... | no  x∉ys = ∉⇒All≠ (∉-++ᵘ x xs ys (All≠⇒∉ x∉xs) x∉ys) AllPairs.∷ (++ᵘ-unique xs ys Uxs Uys)
  ... | yes _ = ++ᵘ-unique xs ys Uxs Uys
  
  ∈ʳ⇒∈++ : {x : A} → (xs ys : List A) → x ∈ ys → x ∈ (xs ++ᵘ ys)
  ∈ʳ⇒∈++ [] ys x∈ys = x∈ys
  ∈ʳ⇒∈++ (x₁ ∷ xs) ys x∈ys with x₁ ∈? ys
  ... | no  _ = there (∈ʳ⇒∈++ xs ys x∈ys)
  ... | yes _ = ∈ʳ⇒∈++ xs ys x∈ys
  
  ∈ˡ⇒∈++ : {x : A} → (xs ys : List A) → x ∈ xs → x ∈ (xs ++ᵘ ys)
  ∈ˡ⇒∈++ (x₁ ∷ xs) ys x∈xs with x₁ ∈? ys
  ∈ˡ⇒∈++ (_ ∷ xs) ys here         | no _ = here
  ∈ˡ⇒∈++ (_ ∷ xs) ys (there x∈xs) | no _ = there (∈ˡ⇒∈++ xs ys x∈xs)
  ∈ˡ⇒∈++ (_ ∷ xs) ys here         | yes x∈ys = ∈ʳ⇒∈++ xs ys x∈ys
  ∈ˡ⇒∈++ (_ ∷ xs) ys (there x∈xs) | yes _    = ∈ˡ⇒∈++ xs ys x∈xs

  ∈++⇒∈ˡ⊎∈ʳ : {x : A} (xs ys : List A) → x ∈ (xs ++ᵘ ys) → (x ∈ xs) ⊎ (x ∈ ys)
  ∈++⇒∈ˡ⊎∈ʳ [] ys x∈++ = inj₂ x∈++
  ∈++⇒∈ˡ⊎∈ʳ (x₁ ∷ xs) ys x∈++ with x₁ ∈? ys
  ∈++⇒∈ˡ⊎∈ʳ (x₁ ∷ xs) ys here | no _ = inj₁ here
  ∈++⇒∈ˡ⊎∈ʳ (x₁ ∷ xs) ys (there x∈++) | no _ = map₁ there (∈++⇒∈ˡ⊎∈ʳ xs ys x∈++)
  ... | yes _ = map₁ there (∈++⇒∈ˡ⊎∈ʳ xs ys x∈++)

  x∈filter⇒Px : {P : A → Set} → (x : A) → (P? : Dec₁ P) → (l : List A) → x ∈ (filter P? l) → P x
  x∈filter⇒Px x P? (x′ ∷ l) x∈fPl with P? x′
  ... | no ¬Px′ = x∈filter⇒Px x P? l x∈fPl
  ... | yes Px′ with x∈fPl
  ... | here = Px′
  ... | there x∈fPl = x∈filter⇒Px x P? l x∈fPl
        
  ∉-filter : {x : A} {P : A → Set} (P? : Dec₁ P) → ¬ (P x) → (l : List A) → x ∉ (filter P? l)
  ∉-filter P? ¬Px [] = λ ()
  ∉-filter {x} P? ¬Px (x₁ ∷ l) with P? x₁
  ... | no ¬Px₁ = ∉-filter P? ¬Px l
  ... | yes Px₁ with x ≟ x₁
  ... | no  x≠x₁ = λ { here → x≠x₁ refl ; (there x∈fPl) → ¬Px (x∈filter⇒Px x P? l x∈fPl)}
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
  AllP⇒Px (Px All.∷ _) here = Px
  AllP⇒Px (_ All.∷ APl) (there x∈l) = AllP⇒Px APl x∈l

  ∈-filter : {x : A} (P : A → Set) → (P? : Dec₁ P) → P x → (l : List A) → x ∈ l → x ∈ (filter P? l)
  ∈-filter P P? Px (x ∷ l′) here with P? x
  ... | no ¬Px = ⊥-elim (¬Px Px)
  ... | yes Px = here
  ∈-filter P P? Px (x₁ ∷ l′) (there x∈l′) with P? x₁
  ... | no ¬Px₁ = ∈-filter P P? Px l′ x∈l′
  ... | yes Px₁ = there (∈-filter P P? Px l′ x∈l′)

  ∈-deduplicate : {x : A} → (l : List A) → x ∈ l → x ∈ deduplicate _≟_ l
  ∈-deduplicate (x ∷ l′) here = here
  ∈-deduplicate {x} (x₁ ∷ l′) (there x∈l′) with x₁ ≟ x
  ... | no  x₁≠x = there (∈-filter (λ x → ¬ x₁ ≡ x) (x₁ ≠?_) x₁≠x (deduplicate _≟_ l′) (∈-deduplicate l′ x∈l′))
  ... | yes refl = here

  ∈-++ˡ : (l : List A) (l′ : List A) → {x : A} → x ∈ l → x ∈ (l ++ l′)
  ∈-++ˡ (x ∷ _) l′ here = here
  ∈-++ˡ (_ ∷ l) l′ (there x∈l) = there (∈-++ˡ l l′ x∈l)

  ∈-++ʳ : (l′ : List A) (l : List A) → {x : A} → x ∈ l → x ∈ (l′ ++ l)
  ∈-++ʳ [] l x∈l = x∈l
  ∈-++ʳ (x′ ∷ l′) l x∈l = there (∈-++ʳ l′ l x∈l)

  module _ {B : Set} {_≟ᴮ_ : DecidableEquality B} where
    open import Graph.Common.Algo.List {B} {_≟ᴮ_} renaming (_∈_ to _∈ᴮ_; here to hereᴮ; there to thereᴮ)
  
    ∈-map : {x : A} {l : List A} (f : A → B) → x ∈ l → f x ∈ᴮ map f l
    ∈-map f here = hereᴮ
    ∈-map f (there x∈l) = thereᴮ (∈-map f x∈l)

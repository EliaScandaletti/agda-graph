open import Relation.Binary using (DecidableEquality)

module Graph.Directed.Decidability {L : Set} {_≟ᴸ_ : DecidableEquality L} where
  open import Level renaming (0ℓ to 0𝓁)
  open import Agda.Builtin.Equality

  open import Function using (id)
  
  open import Relation.Nullary using (Dec; yes; no; _×-dec_; _⊎-dec_; _→-dec_)
  open import Relation.Unary using (Pred; _⊆_; _⊈_; _∪_)
  open import Relation.Binary using (Rel; _⇒_)

  open import Data.Empty using (⊥; ⊥-elim)
  open import Data.Bool using (true; false)
  open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
  open import Data.Product using (_×_; _,_; proj₁; proj₂)

  open import Graph.Directed.Core {L}
  
  V-of? : (g : Graph) → (x : L) → Dec (x ∈V[ g ])
  V-of? ε         x = no (λ x₁ → x₁)
  V-of? (v x₁)    x = x₁ ≟ᴸ x
  V-of? (g₁ + g₂) x = (V-of? g₁ x) ⊎-dec (V-of? g₂ x)
  V-of? (g₁ * g₂) x = (V-of? g₁ x) ⊎-dec (V-of? g₂ x)
  
  E-of? : (g : Graph) → (x y : L) → Dec (x ↦ y ∈E[ g ])
  E-of?  ε        x y = no id
  E-of? (v w)     x y = no id
  E-of? (g₁ + g₂) x y =  (E-of? g₁ x y) ⊎-dec (E-of? g₂ x y)
  E-of? (g₁ * g₂) x y = ((E-of? g₁ x y) ⊎-dec (E-of? g₂ x y))
                           ⊎-dec ((V-of? g₁ x) ×-dec (V-of? g₂ y))

  private
    _∪-⊆-dec_ : {A : Set} {P Q R : Pred A 0𝓁} → Dec (P ⊆ Q) → Dec (R ⊆ Q) → Dec (P ∪ R ⊆ Q)
    no  P⊈Q ∪-⊆-dec _       = no λ P∪R⊆Q → P⊈Q (λ x∈P → P∪R⊆Q (inj₁ x∈P))
    yes _   ∪-⊆-dec no  R⊈Q = no λ P∪R⊆Q → R⊈Q (λ x∈R → P∪R⊆Q (inj₂ x∈R))
    yes P⊆Q ∪-⊆-dec yes R⊆Q = yes λ { (inj₁ x∈P) → P⊆Q x∈P ; (inj₂ x∈R) → R⊆Q x∈R}

    _⊎-⇒-dec_ : {A : Set} {P Q R : Rel A 0𝓁} → Dec (P ⇒ Q) → Dec (R ⇒ Q) → Dec ((λ x y → P x y ⊎ R x y) ⇒ Q)
    no ¬P⇒Q ⊎-⇒-dec _        = no λ P⊎R⇒Q → ¬P⇒Q (λ xPy → P⊎R⇒Q (inj₁ xPy))
    yes _    ⊎-⇒-dec no ¬R⇒Q = no λ P⊎R⇒Q → ¬R⇒Q (λ xRy → P⊎R⇒Q (inj₂ xRy))
    yes P⇒Q ⊎-⇒-dec yes R⇒Q = yes λ { (inj₁ xPy) → P⇒Q xPy ; (inj₂ xRy) → R⇒Q xRy}

    V×V⇒E? : {g₁ g₂ g₃ : Graph} → ((x : L) → Dec (x ∈V[ g₁ ])) → ((y : L) → Dec (y ∈V[ g₂ ]))→ ((x y : L) → Dec (x ↦ y ∈E[ g₃ ]))
                                 → Dec ((λ x y → V-of g₁ x × V-of g₂ y) ⇒ E-of g₃)
    V×V⇒E? {ε}         _∈V₁? _∈V₂? _↦_∈E₃? = yes λ ()
    V×V⇒E? {v x} {ε}   _∈V₁? _∈V₂? _↦_∈E₃? = yes λ ()
    V×V⇒E? {v x} {v y} _∈V₁? _∈V₂? _↦_∈E₃? with x ∈V₁? | y ∈V₂? | x ↦ y ∈E₃?
    ... | no x≠x | _      | _ = ⊥-elim (x≠x refl)
    ... | yes _  | no y≠y | _ = ⊥-elim (y≠y refl)
    ... | yes _  | yes _  | no ¬xE₃y = no λ x₁ → ¬xE₃y (x₁ (refl , refl))
    ... | yes _  | yes _  | yes xE₃y = yes λ { (refl , refl) → xE₃y}
    V×V⇒E? {v x} {g₄ + g₅} _∈V₁? _∈V₂? _↦_∈E₃? with V×V⇒E? {v x} {g₄} _∈V₁? (V-of? g₄) _↦_∈E₃? | V×V⇒E? {v x} {g₅} _∈V₁? (V-of? g₅) _↦_∈E₃?
    ... | no ¬x×V₄⇒E₃ | _            = no λ x₁ → ¬x×V₄⇒E₃ λ { (refl , y∈V₄) → x₁ (refl , (inj₁ y∈V₄))}
    ... | yes _        | no ¬x×V₅⇒E₃ = no λ x₁ → ¬x×V₅⇒E₃ λ { (refl , y∈V₅) → x₁ (refl , (inj₂ y∈V₅))}
    ... | yes x×V₄⇒E₃ | yes x×V₅⇒E₃ = yes λ { (refl , inj₁ y∈V₄) → x×V₄⇒E₃ (refl , y∈V₄)
                                              ; (refl , inj₂ y∈V₅) → x×V₅⇒E₃ (refl , y∈V₅)}
    V×V⇒E? {v x} {g₄ * g₅} _∈V₁? _∈V₂? _↦_∈E₃? with V×V⇒E? {v x} {g₄} _∈V₁? (V-of? g₄) _↦_∈E₃? | V×V⇒E? {v x} {g₅} _∈V₁? (V-of? g₅) _↦_∈E₃?
    ... | no ¬x×V₄⇒E₃ | _            = no λ x₁ → ¬x×V₄⇒E₃ λ { (refl , y∈V₄) → x₁ (refl , (inj₁ y∈V₄))}
    ... | yes _        | no ¬x×V₅⇒E₃ = no λ x₁ → ¬x×V₅⇒E₃ λ { (refl , y∈V₅) → x₁ (refl , (inj₂ y∈V₅))}
    ... | yes x×V₄⇒E₃ | yes x×V₅⇒E₃ = yes λ { (refl , inj₁ y∈V₄) → x×V₄⇒E₃ (refl , y∈V₄)
                                              ; (refl , inj₂ y∈V₅) → x×V₅⇒E₃ (refl , y∈V₅)}
    V×V⇒E? {g₄ + g₅} {g₂}  _∈V₁? _∈V₂? _↦_∈E₃? with V×V⇒E? {g₄} {g₂} (V-of? g₄) _∈V₂?  _↦_∈E₃? | V×V⇒E? {g₅} {g₂} (V-of? g₅) _∈V₂?  _↦_∈E₃?
    ... | no ¬V₄×V₂⇒E₃ | _             = no λ x₁ → ¬V₄×V₂⇒E₃ λ (x∈V₄ , x∈V₂) → x₁ (inj₁ x∈V₄ , x∈V₂)
    ... | yes _         | no ¬V₅×V₂⇒E₃ = no λ x₁ → ¬V₅×V₂⇒E₃ λ (x∈V₅ , x∈V₂) → x₁ (inj₂ x∈V₅ , x∈V₂)
    ... | yes V₄×V₂⇒E₃ | yes V₅×V₂⇒E₃ = yes λ { (inj₁ x∈V₄ , y∈V₂) → V₄×V₂⇒E₃ (x∈V₄ , y∈V₂)
                                                ; (inj₂ x∈V₅ , y∈V₂) → V₅×V₂⇒E₃ (x∈V₅ , y∈V₂)}
    V×V⇒E? {g₄ * g₅} {g₂}  _∈V₁? _∈V₂? _↦_∈E₃? with V×V⇒E? {g₄} {g₂} (V-of? g₄) _∈V₂?  _↦_∈E₃? | V×V⇒E? {g₅} {g₂} (V-of? g₅) _∈V₂?  _↦_∈E₃?
    ... | no ¬V₄×V₂⇒E₃ | _             = no λ x₁ → ¬V₄×V₂⇒E₃ λ (x∈V₄ , x∈V₂) → x₁ (inj₁ x∈V₄ , x∈V₂)
    ... | yes _         | no ¬V₅×V₂⇒E₃ = no λ x₁ → ¬V₅×V₂⇒E₃ λ (x∈V₅ , x∈V₂) → x₁ (inj₂ x∈V₅ , x∈V₂)
    ... | yes V₄×V₂⇒E₃ | yes V₅×V₂⇒E₃ = yes λ { (inj₁ x∈V₄ , y∈V₂) → V₄×V₂⇒E₃ (x∈V₄ , y∈V₂)
                                                ; (inj₂ x∈V₅ , y∈V₂) → V₅×V₂⇒E₃ (x∈V₅ , y∈V₂)}
  
  _⊆ⱽ?_ : (g₁ g₂ : Graph) → Dec ((V-of g₁) ⊆ (V-of g₂))
  ε ⊆ⱽ? _ = yes (λ x → ⊥-elim x)
  (v x) ⊆ⱽ? ε = no (λ Vₓ⊆∅ → Vₓ⊆∅ refl)
  (v x₁) ⊆ⱽ? (v x₂) with x₂ ≟ᴸ x₁
  ... | no  x₂≠x₁ = no (λ x → x₂≠x₁ (x refl))
  ... | yes refl = yes (λ { refl → refl })
  (v x) ⊆ⱽ? (g₂ + g₃) with (v x) ⊆ⱽ? g₂ | (v x) ⊆ⱽ? g₃
  ... | no  Vₓ⊈V₂ | no  Vₓ⊈V₃ = no (λ x₁ → [ (λ x∈V₂ → Vₓ⊈V₂ λ { refl → x∈V₂}) , (λ x∈V₃ → Vₓ⊈V₃ (λ { refl → x∈V₃})) ] (x₁ refl))
  ... | no  Vₓ⊈V₂ | yes Vₓ⊆V₃ = yes (λ refl → inj₂ (Vₓ⊆V₃ refl))
  ... | yes Vₓ⊆V₂ | Q = yes (λ refl → inj₁ (Vₓ⊆V₂ refl))
  (v x) ⊆ⱽ? (g₂ * g₃) with (v x) ⊆ⱽ? g₂ | (v x) ⊆ⱽ? g₃
  ... | no  Vₓ⊈V₂ | no  Vₓ⊈V₃ = no (λ x₁ → [ (λ x∈V₂ → Vₓ⊈V₂ λ { refl → x∈V₂}) , (λ x∈V₃ → Vₓ⊈V₃ (λ { refl → x∈V₃})) ] (x₁ refl))
  ... | no  Vₓ⊈V₂ | yes Vₓ⊆V₃ = yes (λ refl → inj₂ (Vₓ⊆V₃ refl))
  ... | yes Vₓ⊆V₂ | Q = yes (λ refl → inj₁ (Vₓ⊆V₂ refl))
  (g₁ + g₂) ⊆ⱽ? g₃ = (g₁ ⊆ⱽ? g₃) ∪-⊆-dec (g₂ ⊆ⱽ? g₃)
  (g₁ * g₂) ⊆ⱽ? g₃ = (g₁ ⊆ⱽ? g₃) ∪-⊆-dec (g₂ ⊆ⱽ? g₃)

  _⊆ᴱ?_ : (g₁ g₂ : Graph) → Dec ((E-of g₁) ⇒ (E-of g₂))
  ε         ⊆ᴱ? _  = yes ⊥-elim
  (v x)     ⊆ᴱ? _  = yes ⊥-elim
  (g₁ + g₂) ⊆ᴱ? g₃ =  (g₁ ⊆ᴱ? g₃) ⊎-⇒-dec (g₂ ⊆ᴱ? g₃)
  (g₁ * g₂) ⊆ᴱ? g₃ = ((g₁ ⊆ᴱ? g₃) ⊎-⇒-dec (g₂ ⊆ᴱ? g₃)) ⊎-⇒-dec
                     (V×V⇒E? {g₁} {g₂} (V-of? g₁) (V-of? g₂) (E-of? g₃))

  _⊆ᵍ?_ : (g₁ g₂ : Graph) → Dec (g₁ ⊆ᵍ g₂)
  g₁ ⊆ᵍ? g₂ = (g₁ ⊆ⱽ? g₂) ×-dec (g₁ ⊆ᴱ? g₂)

  _≟_ : (g₁ g₂ : Graph) → Dec (g₁ ≡ᵍ g₂)
  g₁ ≟ g₂ = (g₁ ⊆ᵍ? g₂) ×-dec (g₂ ⊆ᵍ? g₁)

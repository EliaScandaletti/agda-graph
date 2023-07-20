open import Relation.Binary using (DecidableEquality)

module Graph.Core.Decidability {L : Set} {_≟ᴸ_ : DecidableEquality L} where
  open import Level renaming (0ℓ to 0𝓁)
  open import Agda.Builtin.Equality using (refl)
  open import Relation.Nullary using (Dec; yes; no; _⊎-dec_)
  open import Relation.Unary using (Pred; _⊆_; _∪_)
  open import Data.Sum using (inj₁; inj₂; [_,_])

  open import Graph.Core
  open import Graph.Core.Definitions
  
  V-of? : (g : Graph) → (x : L) → Dec (x ∈V[ g ])
  V-of? ε         x = no (λ x₁ → x₁)
  V-of? (v x₁)    x = x₁ ≟ᴸ x
  V-of? (g₁ + g₂) x = (V-of? g₁ x) ⊎-dec (V-of? g₂ x)
  V-of? (g₁ * g₂) x = (V-of? g₁ x) ⊎-dec (V-of? g₂ x)

  private
    _∪-⊆-dec_ : {A : Set} {P Q R : Pred A 0𝓁} → Dec (P ⊆ Q) → Dec (R ⊆ Q) → Dec (P ∪ R ⊆ Q)
    no  P⊈Q ∪-⊆-dec _       = no λ P∪R⊆Q → P⊈Q (λ x∈P → P∪R⊆Q (inj₁ x∈P))
    yes _   ∪-⊆-dec no  R⊈Q = no λ P∪R⊆Q → R⊈Q (λ x∈R → P∪R⊆Q (inj₂ x∈R))
    yes P⊆Q ∪-⊆-dec yes R⊆Q = yes λ { (inj₁ x∈P) → P⊆Q x∈P ; (inj₂ x∈R) → R⊆Q x∈R}
    
  _⊆ⱽ?_ : (g₁ g₂ : Graph) → Dec ((V-of g₁) ⊆ (V-of g₂))
  ε ⊆ⱽ? _ = yes λ ()
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
  
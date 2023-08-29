open import Relation.Binary using (DecidableEquality)
module Graph.Undirected.Decidability {L : Set} (_≟ᴸ_ : DecidableEquality L) where
  open import Relation.Nullary using (Dec; yes; no)
  open import Relation.Binary using (_⇒_)
  open import Data.Empty using (⊥)

  open import Graph.Undirected
  open import Graph.Core.Decidability _≟ᴸ_

  E-of? : (g : Graph) → (x y : L) → Dec (x ↦ y ∈E[ g ])
  E-of?  ε        x y = no λ ()
  E-of? (v w)     x y = no λ ()
  E-of? (g₁ + g₂) x y with E-of? g₁ x y | E-of? g₂ x y
  ... | no ¬xE₁y | no ¬xE₂y = no λ { (+-Eˡ xE₁y) → ¬xE₁y xE₁y ; (+-Eʳ xE₂y) → ¬xE₂y xE₂y}
  ... | no ¬xE₁y | yes xE₂y = yes (+-Eʳ xE₂y)
  ... | yes xE₁y | _        = yes (+-Eˡ xE₁y)
  E-of? (g₁ * g₂) x y with E-of? g₁ x y | E-of? g₂ x y
  ... | no ¬xE₁y | yes xE₂y = yes (*-Eʳ xE₂y)
  ... | yes xE₁y | _        = yes (*-Eˡ xE₁y)
  ... | no ¬xE₁y | no ¬xE₂y with V-of? g₁ x | V-of? g₁ y | V-of? g₂ x | V-of? g₂ y
  ...                       | no  x∉V₁ | _        | no  x∉V₂ | _        = no λ { (*-Eˡ xE₁y) → ¬xE₁y xE₁y
                                                                               ; (*-Eʳ xE₂y) → ¬xE₂y xE₂y
                                                                               ; (*-Eˣ₁ x∈V₁ y∈V₂) → x∉V₁ x∈V₁
                                                                               ; (*-Eˣ₂ y∈V₁ x∈V₂) → x∉V₂ x∈V₂}
  ...                       | no  x∉V₁ | no  y∉V₁ | yes _    | _        = no λ { (*-Eˡ xE₁y) → ¬xE₁y xE₁y
                                                                               ; (*-Eʳ xE₂y) → ¬xE₂y xE₂y
                                                                               ; (*-Eˣ₁ x∈V₁ y∈V₂) → x∉V₁ x∈V₁
                                                                               ; (*-Eˣ₂ y∈V₁ x∈V₂) → y∉V₁ y∈V₁}
  ...                       | no  _    | yes y∈V₁ | yes x∈V₂ | _        = yes (*-Eˣ₂ y∈V₁ x∈V₂)
  ...                       | yes _    | no  y∉V₁ | _        | no y∉V₂ = no λ { (*-Eˡ xE₁y) → ¬xE₁y xE₁y
                                                                              ; (*-Eʳ xE₂y) → ¬xE₂y xE₂y
                                                                              ; (*-Eˣ₁ x∈V₁ y∈V₂) → y∉V₂ y∈V₂
                                                                              ; (*-Eˣ₂ y∈V₁ x∈V₂) → y∉V₁ y∈V₁}
  ...                       | yes _    | yes _    | no  x∉V₂ | no  y∉V₂ = no λ { (*-Eˡ xE₁y) → ¬xE₁y xE₁y
                                                                              ; (*-Eʳ xE₂y) → ¬xE₂y xE₂y
                                                                              ; (*-Eˣ₁ x∈V₁ y∈V₂) → y∉V₂ y∈V₂
                                                                              ; (*-Eˣ₂ y∈V₁ x∈V₂) → x∉V₂ x∈V₂}
  ...                       | yes _    | yes y∈V₁ | yes x∈V₂ | no _     = yes (*-Eˣ₂ y∈V₁ x∈V₂)
  ...                       | yes x∈V₁ | _        | _        | yes y∈V₂ = yes (*-Eˣ₁ x∈V₁ y∈V₂)

  _⊆ᴱ?_ : (g₁ g₂ : Graph) → Dec (_↦_∈E[ g₁ ] ⇒ _↦_∈E[ g₂ ])
  g₁ ⊆ᴱ? g₂ = go g₁ g₂ (wf g₁) (wf g₂) where
    open import Relation.Binary.PropositionalEquality using (sym)
    open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s) renaming (_<_ to _<ᴺ_; _+_ to _+ᴺ_)
    open import Data.Nat.Properties using (m≤m+n; m≤n+m; +-monoʳ-≤; +-monoˡ-≤; +-suc; +-assoc)
    open Data.Nat.Properties.≤-Reasoning
    open import Graph.Core.Recursion using (#_; Acc; acc; _<_; lift; wf)
    l-+ : {g₃ g₄ : Graph} → g₃ < (g₃ + g₄)
    l-+ {g₃} {g₄} = lift (s≤s (m≤m+n (# g₃) (# g₄)))
    r-+ : {g₃ g₄ : Graph} → g₄ < (g₃ + g₄)
    r-+ {g₃} {g₄} = lift (s≤s (m≤n+m (# g₄) (# g₃)))
    l-* : {g₃ g₄ : Graph} → g₃ < (g₃ * g₄)
    l-* {g₃} {g₄} = lift (s≤s (m≤m+n (# g₃) (# g₄)))
    r-* : {g₃ g₄ : Graph} → g₄ < (g₃ * g₄)
    r-* {g₃} {g₄} = lift (s≤s (m≤n+m (# g₄) (# g₃)))
    l-*-+ : {g₃ g₄ g₅ : Graph} → (g₃ * g₄) < (g₃ * (g₄ + g₅))
    l-*-+ {g₃} {g₄} {g₅} = lift (s≤s (begin
      suc ((# g₃) +ᴺ (# g₄))               ≤⟨ s≤s (+-monoʳ-≤ (# g₃) (m≤m+n (# g₄) (# g₅))) ⟩
      suc ((# g₃) +ᴺ ((# g₄) +ᴺ (# g₅)))   ≡⟨ sym (+-suc (# g₃) ((# g₄) +ᴺ (# g₅))) ⟩
      ((# g₃) +ᴺ (suc ((# g₄) +ᴺ (# g₅)))) ∎))
    r-*-+ : {g₃ g₄ g₅ : Graph} → (g₃ * g₅) < (g₃ * (g₄ + g₅))
    r-*-+ {g₃} {g₄} {g₅} = lift (s≤s (begin
      suc ((# g₃) +ᴺ (# g₅))               ≤⟨ s≤s (+-monoʳ-≤ (# g₃) (m≤n+m (# g₅) (# g₄))) ⟩
      suc ((# g₃) +ᴺ ((# g₄) +ᴺ (# g₅)))   ≡⟨ sym (+-suc (# g₃) ((# g₄) +ᴺ (# g₅))) ⟩
      ((# g₃) +ᴺ (suc ((# g₄) +ᴺ (# g₅)))) ∎))
    l-*-*₁ : {g₃ g₄ g₅ : Graph} → (g₃ * g₄) < (g₃ * (g₄ * g₅))
    l-*-*₁ {g₃} {g₄} {g₅} = lift (s≤s (begin
      suc ((# g₃) +ᴺ (# g₄))               ≤⟨ s≤s (+-monoʳ-≤ (# g₃) (m≤m+n (# g₄) (# g₅))) ⟩
      suc ((# g₃) +ᴺ ((# g₄) +ᴺ (# g₅)))   ≡⟨ sym (+-suc (# g₃) ((# g₄) +ᴺ (# g₅))) ⟩
      ((# g₃) +ᴺ (suc ((# g₄) +ᴺ (# g₅)))) ∎))
    r-*-*₁ : {g₃ g₄ g₅ : Graph} → (g₃ * g₅) < (g₃ * (g₄ * g₅))
    r-*-*₁ {g₃} {g₄} {g₅ } = lift (s≤s (begin
      suc ((# g₃) +ᴺ (# g₅))               ≤⟨ s≤s (+-monoʳ-≤ (# g₃) (m≤n+m (# g₅) (# g₄))) ⟩
      suc ((# g₃) +ᴺ ((# g₄) +ᴺ (# g₅)))   ≡⟨ sym (+-suc (# g₃) ((# g₄) +ᴺ (# g₅))) ⟩
      ((# g₃) +ᴺ (suc ((# g₄) +ᴺ (# g₅)))) ∎))
    l-+-* : {g₃ g₄ g₅ : Graph} → (g₃ * g₅) < ((g₃ + g₄) * g₅)
    l-+-* {g₃} {g₄} {g₅} = lift (s≤s (s≤s (begin
      ((# g₃) +ᴺ (# g₅))             ≤⟨ +-monoʳ-≤ (# g₃) (m≤n+m (# g₅) (# g₄)) ⟩
      ((# g₃) +ᴺ ((# g₄) +ᴺ (# g₅))) ≡⟨ sym (+-assoc (# g₃) (# g₄) (# g₅)) ⟩
      (((# g₃) +ᴺ (# g₄)) +ᴺ (# g₅)) ∎)))
    r-+-* : {g₃ g₄ g₅ : Graph} → (g₄ * g₅) < ((g₃ + g₄) * g₅)
    r-+-* {g₃} {g₄} {g₅} = lift (s≤s (s≤s (+-monoˡ-≤ (# g₅) (m≤n+m (# g₄) (# g₃)))))
    l-*-*₂ : {g₃ g₄ g₅ : Graph} → (g₃ * g₅) < ((g₃ * g₄) * g₅)
    l-*-*₂ {g₃} {g₄} {g₅} = lift (s≤s (s≤s (+-monoˡ-≤ (# g₅) (m≤m+n (# g₃) (# g₄)))))
    r-*-*₂ : {g₃ g₄ g₅ : Graph} → (g₄ * g₅) < ((g₃ * g₄) * g₅)
    r-*-*₂ {g₃} {g₄} {g₅} = lift (s≤s (s≤s (+-monoˡ-≤ (# g₅) (m≤n+m (# g₄) (# g₃)))))

    go : (g₁ g₂ : Graph) → Acc g₁ → Acc g₂ → Dec (_↦_∈E[ g₁ ] ⇒ _↦_∈E[ g₂ ])
    go ε         _  _ _ = yes λ ()
    go (v x)     _  _ _ = yes λ ()
    go (g₁ + g₂) g₃ (acc step) a₃ with go g₁ g₃ (step l-+) a₃ | go g₂ g₃ (step r-+) a₃
    ... | no  E₁⊈E₃ | _         = no helper where
      helper : ({x y : L} → x ↦ y ∈E[ g₁ + g₂ ] → x ↦ y ∈E[ g₃ ]) → ⊥
      helper p = E₁⊈E₃ (λ z → p (+-Eˡ z))
    ... | yes E₁⊆E₃ | no  E₂⊈E₃ = no helper where
      helper : ({x y : L} → x ↦ y ∈E[ g₁ + g₂ ] → x ↦ y ∈E[ g₃ ]) → ⊥
      helper p = E₂⊈E₃ (λ z → p (+-Eʳ z))
    ... | yes E₁⊆E₃ | yes E₂⊆E₃ = yes λ { (+-Eˡ x) → E₁⊆E₃ x ; (+-Eʳ x) → E₂⊆E₃ x}
    go (g₁ * g₂) g₃ (acc step) a₃ with go g₁ g₃ (step l-*) a₃ | go g₂ g₃ (step r-*) a₃
    ... | no  E₁⊈E₃ | _         = no helper where
      helper : ({x y : L} → x ↦ y ∈E[ g₁ * g₂ ] → x ↦ y ∈E[ g₃ ]) → ⊥
      helper p = E₁⊈E₃ (λ z → p (*-Eˡ z))
    ... | yes E₁⊆E₃ | no  E₂⊈E₃ = no helper where
      helper : ({x y : L} → x ↦ y ∈E[ g₁ * g₂ ] → x ↦ y ∈E[ g₃ ]) → ⊥
      helper p = E₂⊈E₃ (λ z → p (*-Eʳ z))
    go ( ε    * g₂)    g₃ _ _ | yes _ | yes E₂⊆E₃ = yes λ { (*-Eʳ xE₂y) → E₂⊆E₃ xE₂y}
    go ((v x) *  ε)    g₃ _ _ | yes _ | yes E₂⊆E₃ = yes λ { (*-Eˡ ()) ; (*-Eʳ ()) ; (*-Eˣ₁ v-V ())}
    go ((v x) * (v y)) g₃ _ _ | yes E₁⊆E₃ | yes E₂⊆E₃ with E-of? g₃ x y | E-of? g₃ y x
    ... | no ¬xE₃y | _        = no λ {p → ¬xE₃y (p (*-Eˣ₁ v-V v-V))}
    ... | yes _    | no ¬yE₃x = no λ {p → ¬yE₃x (p (*-Eˣ₂ v-V v-V))}
    ... | yes xE₃y | yes yE₃x = yes λ { (*-Eˣ₁ v-V v-V) → xE₃y ; (*-Eˣ₂ v-V v-V) → yE₃x}
    go ((v x) * (g₄ + g₅)) g₃ (acc step) a₃ | yes E₁⊆E₃ | yes E₂⊆E₃ with go ((v x) * g₄) g₃ (step l-*-+) a₃ | go ((v x) * g₅) g₃ (step r-*-+) a₃
    ... | no  Eₓ⋆₄⊈E₃ | _           = no λ p → Eₓ⋆₄⊈E₃ λ { (*-Eʳ x∈V₄) → E₂⊆E₃ (+-Eˡ x∈V₄)
                                                         ; (*-Eˣ₁ x∈Vₓ y∈V₄) → p (*-Eˣ₁ x∈Vₓ (+-Vˡ y∈V₄))
                                                         ; (*-Eˣ₂ y∈Vₓ x∈V₄) → p (*-Eˣ₂ y∈Vₓ (+-Vˡ x∈V₄))}
    ... | yes _       | no  Eₓ⋆₅⊈E₃ = no λ p → Eₓ⋆₅⊈E₃ λ { (*-Eʳ x∈V₅) → E₂⊆E₃ (+-Eʳ x∈V₅)
                                                         ; (*-Eˣ₁ x∈Vₓ y∈V₅) → p (*-Eˣ₁ x∈Vₓ (+-Vʳ y∈V₅))
                                                         ; (*-Eˣ₂ y∈Vₓ x∈V₅) → p (*-Eˣ₂ y∈Vₓ (+-Vʳ x∈V₅))}
    ... | yes Eₓ⋆₄⊆E₃ | yes Eₓ⋆₅⊆E₃ = yes λ { (*-Eʳ xE₂y) → E₂⊆E₃ xE₂y
                                           ; (*-Eˣ₁ v-V (+-Vˡ y∈V₄)) → Eₓ⋆₄⊆E₃ (*-Eˣ₁ v-V y∈V₄)
                                           ; (*-Eˣ₁ v-V (+-Vʳ y∈V₅)) → Eₓ⋆₅⊆E₃ (*-Eˣ₁ v-V y∈V₅)
                                           ; (*-Eˣ₂ v-V (+-Vˡ x∈V₄)) → Eₓ⋆₄⊆E₃ (*-Eˣ₂ v-V x∈V₄)
                                           ; (*-Eˣ₂ v-V (+-Vʳ x∈V₅)) → Eₓ⋆₅⊆E₃ (*-Eˣ₂ v-V x∈V₅)}
    go ((v x) * (g₄ * g₅)) g₃ (acc step) a₃ | yes E₁⊆E₃ | yes E₂⊆E₃ with go ((v x) * g₄) g₃ (step l-*-*₁) a₃ | go ((v x) * g₅) g₃ (step r-*-*₁) a₃
    ... | no  Eₓ⋆₄⊈E₃ | _           = no λ p → Eₓ⋆₄⊈E₃ λ { (*-Eʳ x∈V₄) → E₂⊆E₃ (*-Eˡ x∈V₄)
                                                         ; (*-Eˣ₁ x∈Vₓ y∈V₄) → p (*-Eˣ₁ x∈Vₓ (*-Vˡ y∈V₄))
                                                         ; (*-Eˣ₂ y∈Vₓ x∈V₄) → p (*-Eˣ₂ y∈Vₓ (*-Vˡ x∈V₄))}
    ... | yes _       | no  Eₓ⋆₅⊈E₃ = no λ p → Eₓ⋆₅⊈E₃ λ { (*-Eʳ x∈V₅) → E₂⊆E₃ (*-Eʳ x∈V₅)
                                                         ; (*-Eˣ₁ x∈Vₓ y∈V₅) → p (*-Eˣ₁ x∈Vₓ (*-Vʳ y∈V₅))
                                                         ; (*-Eˣ₂ y∈Vₓ x∈V₅) → p (*-Eˣ₂ y∈Vₓ (*-Vʳ x∈V₅))}
    ... | yes Eₓ⋆₄⊆E₃ | yes Eₓ⋆₅⊆E₃ = yes λ { (*-Eʳ xE₂y) → E₂⊆E₃ xE₂y
                                           ; (*-Eˣ₁ v-V (*-Vˡ y∈V₄)) → Eₓ⋆₄⊆E₃ (*-Eˣ₁ v-V y∈V₄)
                                           ; (*-Eˣ₁ v-V (*-Vʳ y∈V₅)) → Eₓ⋆₅⊆E₃ (*-Eˣ₁ v-V y∈V₅)
                                           ; (*-Eˣ₂ v-V (*-Vˡ x∈V₄)) → Eₓ⋆₄⊆E₃ (*-Eˣ₂ v-V x∈V₄)
                                           ; (*-Eˣ₂ v-V (*-Vʳ x∈V₅)) → Eₓ⋆₅⊆E₃ (*-Eˣ₂ v-V x∈V₅)}
    go ((g₄ + g₅) *  g₂) g₃ (acc step) a₃ | yes E₁⊆E₃ | yes E₂⊆E₃ with go (g₄ * g₂) g₃ (step l-+-*) a₃ | go (g₅ * g₂) g₃ (step r-+-*) a₃
    ... | no  E₄⋆₂⊈E₃ | _           = no λ p → E₄⋆₂⊈E₃ λ { (*-Eˡ xE₄y) → p (*-Eˡ (+-Eˡ xE₄y))
                                                          ; (*-Eʳ xE₂y) → E₂⊆E₃ xE₂y
                                                          ; (*-Eˣ₁ x∈V₄ y∈V₂) → p (*-Eˣ₁ (+-Vˡ x∈V₄) y∈V₂)
                                                          ; (*-Eˣ₂ y∈V₄ x∈V₂) → p (*-Eˣ₂ (+-Vˡ y∈V₄) x∈V₂)}
    ... | yes _       | no  E₅⋆₂⊈E₃ = no λ p → E₅⋆₂⊈E₃ λ { (*-Eˡ xE₅y) → E₁⊆E₃ (+-Eʳ xE₅y)
                                                          ; (*-Eʳ xE₂y) → E₂⊆E₃ xE₂y
                                                          ; (*-Eˣ₁ x∈V₅ y∈V₂) → p (*-Eˣ₁ (+-Vʳ x∈V₅) y∈V₂)
                                                          ; (*-Eˣ₂ y∈V₅ x∈V₂) → p (*-Eˣ₂ (+-Vʳ y∈V₅) x∈V₂)}
    ... | yes E₄⋆₂⊆E₃ | yes E₅⋆₂⊆E₅ = yes λ { (*-Eˡ xE₁y) → E₁⊆E₃ xE₁y
                                            ; (*-Eʳ xE₂y) → E₂⊆E₃ xE₂y
                                            ; (*-Eˣ₁ (+-Vˡ x∈V₁) y∈V₂) → E₄⋆₂⊆E₃ (*-Eˣ₁ x∈V₁ y∈V₂)
                                            ; (*-Eˣ₁ (+-Vʳ x∈V₁) y∈V₂) → E₅⋆₂⊆E₅ (*-Eˣ₁ x∈V₁ y∈V₂)
                                            ; (*-Eˣ₂ (+-Vˡ y∈V₁) x∈V₂) → E₄⋆₂⊆E₃ (*-Eˣ₂ y∈V₁ x∈V₂)
                                            ; (*-Eˣ₂ (+-Vʳ y∈V₁) x∈V₂) → E₅⋆₂⊆E₅ (*-Eˣ₂ y∈V₁ x∈V₂)}
    go ((g₄ * g₅) *  g₂) g₃ (acc step) a₃ | yes E₁⊆E₃ | yes E₂⊆E₃ with go (g₄ * g₂) g₃  (step l-*-*₂) a₃ | go (g₅ * g₂) g₃ (step r-*-*₂) a₃
    ... | no  E₄⋆₂⊈E₃ | _           = no λ p → E₄⋆₂⊈E₃ λ { (*-Eˡ xE₄y) → p (*-Eˡ (*-Eˡ xE₄y))
                                                         ; (*-Eʳ xE₂y) → E₂⊆E₃ xE₂y
                                                         ; (*-Eˣ₁ x∈V₄ y∈V₂) → p (*-Eˣ₁ (*-Vˡ x∈V₄) y∈V₂)
                                                         ; (*-Eˣ₂ y∈V₄ x∈V₂) → p (*-Eˣ₂ (*-Vˡ y∈V₄) x∈V₂)}
    ... | yes _       | no  E₅⋆₂⊈E₃ = no λ p → E₅⋆₂⊈E₃ λ { (*-Eˡ xE₅y) → E₁⊆E₃ (*-Eʳ xE₅y)
                                                         ; (*-Eʳ xE₂y) → E₂⊆E₃ xE₂y
                                                         ; (*-Eˣ₁ x∈V₅ y∈V₂) → p (*-Eˣ₁ (*-Vʳ x∈V₅) y∈V₂)
                                                         ; (*-Eˣ₂ y∈V₅ x∈V₂) → p (*-Eˣ₂ (*-Vʳ y∈V₅) x∈V₂)}
    ... | yes E₄⋆₂⊆E₃ | yes E₅⋆₂⊆E₅ = yes λ { (*-Eˡ xE₁y) → E₁⊆E₃ xE₁y
                                            ; (*-Eʳ xE₂y) → E₂⊆E₃ xE₂y
                                            ; (*-Eˣ₁ (*-Vˡ x∈V₁) y∈V₂) → E₄⋆₂⊆E₃ (*-Eˣ₁ x∈V₁ y∈V₂)
                                            ; (*-Eˣ₁ (*-Vʳ x∈V₁) y∈V₂) → E₅⋆₂⊆E₅ (*-Eˣ₁ x∈V₁ y∈V₂)
                                            ; (*-Eˣ₂ (*-Vˡ y∈V₁) x∈V₂) → E₄⋆₂⊆E₃ (*-Eˣ₂ y∈V₁ x∈V₂)
                                            ; (*-Eˣ₂ (*-Vʳ y∈V₁) x∈V₂) → E₅⋆₂⊆E₅ (*-Eˣ₂ y∈V₁ x∈V₂)}

  open import Graph.Common.Decidability _≟ᴸ_ _⊆ⱽ?_ _⊆ᴱ?_ public

module Graph.Directed.Properties {L : Set} where
  open import Function using (id; _∘_)
  open import Data.Empty using (⊥-elim)
  open import Data.Sum using (inj₁; inj₂; swap; assocʳ; assocˡ; [_,_]) renaming (map to map⊎)
  open import Data.Product using (_×_; _,_; proj₂) renaming (map to map×)

  open import Graph.Directed.Core
  open import Graph.Common.Definitions {L} {E-of}
  open import Graph.Common.Properties {L} {E-of} public
  
  lemma-soundness : {x y : L} → (g : Graph) → x ↦ y ∈E[ g ] → x ∈V[ g ] × y ∈V[ g ]
  lemma-soundness (g₁ + g₂) (inj₁ x)        = map× inj₁ inj₁ (lemma-soundness g₁ x)
  lemma-soundness (g₁ + g₂) (inj₂ y)        = map× inj₂ inj₂ (lemma-soundness g₂ y)
  lemma-soundness (g₁ * g₂) (inj₁ (inj₁ x)) = map× inj₁ inj₁ (lemma-soundness g₁ x)
  lemma-soundness (g₁ * g₂) (inj₁ (inj₂ y)) = map× inj₂ inj₂ (lemma-soundness g₂ y)
  lemma-soundness (g₁ * g₂) (inj₂ y)        = map× inj₁ inj₂ y

  lemma-+-commutative : {g₁ g₂ : Graph} → g₁ + g₂ ≡ᵍ g₂ + g₁
  lemma-+-commutative = (swap , swap) , (swap , swap)
  
  lemma-+-associative : {g₁ g₂ g₃ : Graph} → (g₁ + g₂) + g₃ ≡ᵍ g₁ + (g₂ + g₃)
  lemma-+-associative = (assocʳ , assocʳ) , (assocˡ , assocˡ)

  lemma-+-congruenceˡ : {g₁ g₂ g₃ : Graph} -> g₁ ≡ᵍ g₂ -> g₁ + g₃ ≡ᵍ g₂ + g₃
  lemma-+-congruenceˡ ((V₁⊆V₂ , E₁⊆E₂) , (V₂⊆V₁ , E₂⊆E₁)) = (map⊎ V₁⊆V₂ id , map⊎ E₁⊆E₂ id)
                                                          , (map⊎ V₂⊆V₁ id , map⊎ E₂⊆E₁ id)

  lemma-+-congruenceʳ : {g₁ g₂ g₃ : Graph} -> g₁ ≡ᵍ g₂ -> g₃ + g₁ ≡ᵍ g₃ + g₂
  lemma-+-congruenceʳ ((V₁⊆V₂ , E₁⊆E₂) , (V₂⊆V₁ , E₂⊆E₁)) = (map⊎ id V₁⊆V₂ , map⊎ id E₁⊆E₂)
                                                          , (map⊎ id V₂⊆V₁ , map⊎ id E₂⊆E₁)

  lemma-+ε : {g : Graph} → g ≡ᵍ g + ε
  lemma-+ε = (inj₁ , inj₁) , ([ id , ⊥-elim ] , [ id , ⊥-elim ])
  
  lemma-*-associative : {g₁ g₂ g₃ : Graph} → (g₁ * g₂) * g₃ ≡ᵍ g₁ * (g₂ * g₃)
  lemma-*-associative = (assocʳ , λ { (inj₁ (inj₁ (inj₁ (inj₁ x)))) → inj₁ (inj₁ x)
                                    ; (inj₁ (inj₁ (inj₁ (inj₂ y)))) → inj₁ (inj₂ (inj₁ (inj₁ y)))
                                    ; (inj₁ (inj₁ (inj₂ (fst , snd)))) → inj₂ (fst , inj₁ snd)
                                    ; (inj₁ (inj₂ y)) → inj₁ (inj₂ (inj₁ (inj₂ y)))
                                    ; (inj₂ (inj₁ x , snd)) → inj₂ (x , inj₂ snd)
                                    ; (inj₂ (inj₂ y , snd)) → inj₁ (inj₂ (inj₂ (y , snd)))})
                      , (assocˡ , λ { (inj₁ (inj₁ x)) → inj₁ (inj₁ (inj₁ (inj₁ x)))
                                    ; (inj₁ (inj₂ (inj₁ (inj₁ x)))) → inj₁ (inj₁ (inj₁ (inj₂ x)))
                                    ; (inj₁ (inj₂ (inj₁ (inj₂ y)))) → inj₁ (inj₂ y)
                                    ; (inj₁ (inj₂ (inj₂ (fst , snd)))) → inj₂ (inj₂ fst , snd)
                                    ; (inj₂ (fst , inj₁ x)) → inj₁ (inj₁ (inj₂ (fst , x)))
                                    ; (inj₂ (fst , inj₂ y)) → inj₂ (inj₁ fst , y)})

  lemma-*-congruenceˡ : {g₁ g₂ g₃ : Graph} -> g₁ ≡ᵍ g₂ -> g₁ * g₃ ≡ᵍ g₂ * g₃
  lemma-*-congruenceˡ ((V₁⊆V₂ , E₁⊆E₂) , (V₂⊆V₁ , E₂⊆E₁)) = (map⊎ V₁⊆V₂ id , map⊎ (map⊎ E₁⊆E₂ id) (map× V₁⊆V₂ id))
                                                          , (map⊎ V₂⊆V₁ id , map⊎ (map⊎ E₂⊆E₁ id) (map× V₂⊆V₁ id))

  lemma-*-congruenceʳ : {g₁ g₂ g₃ : Graph} -> g₁ ≡ᵍ g₂ -> g₃ * g₁ ≡ᵍ g₃ * g₂
  lemma-*-congruenceʳ ((V₁⊆V₂ , E₁⊆E₂) , (V₂⊆V₁ , E₂⊆E₁)) = (map⊎ id V₁⊆V₂ , map⊎ (map⊎ id E₁⊆E₂) (map× id V₁⊆V₂))
                                                          , (map⊎ id V₂⊆V₁ , map⊎ (map⊎ id E₂⊆E₁) (map× id V₂⊆V₁))

  lemma-*ε : {g : Graph} → g ≡ᵍ g * ε
  lemma-*ε = (inj₁ , inj₁ ∘ inj₁) , ([ id , ⊥-elim ] , [ [ id , ⊥-elim ] , ⊥-elim ∘ proj₂ ])

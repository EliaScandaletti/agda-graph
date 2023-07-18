module Graph.Properties {L : Set} where
  open import Function using (id; _∘_)

  open import Relation.Binary using (IsEquivalence; IsPreorder; IsPartialOrder)

  open import Data.Empty using (⊥-elim)
  open import Data.Sum using (inj₁; inj₂; swap; assocʳ; assocˡ; [_,_]) renaming (map to map⊎)
  open import Data.Product using (_×_; _,_; proj₁; proj₂) renaming (map to map×)

  open import Graph.Core {L}
  
  lemma-soundness : {x y : L} → (g : Graph) → x ↦ y ∈E[ g ] → x ∈V[ g ] × y ∈V[ g ]
  lemma-soundness (g₁ + g₂) (inj₁ x) = (inj₁ (proj₁ (lemma-soundness g₁ x))) , (inj₁ (proj₂ (lemma-soundness g₁ x)))
  lemma-soundness (g₁ + g₂) (inj₂ y) = (inj₂ (proj₁ (lemma-soundness g₂ y))) , (inj₂ (proj₂ (lemma-soundness g₂ y)))
  lemma-soundness (g₁ * g₂) (inj₁ (inj₁ x)) = (inj₁ (proj₁ (lemma-soundness g₁ x))) , (inj₁ (proj₂ (lemma-soundness g₁ x)))
  lemma-soundness (g₁ * g₂) (inj₁ (inj₂ y)) = (inj₂ (proj₁ (lemma-soundness g₂ y))) , (inj₂ (proj₂ (lemma-soundness g₂ y)))
  lemma-soundness (g₁ * g₂) (inj₂ (inj₁ x)) = (inj₁ (proj₁ x)) , (inj₂ (proj₂ x))
  lemma-soundness (g₁ * g₂) (inj₂ (inj₂ y)) = (inj₂ (proj₁ y)) , (inj₁ (proj₂ y))

  lemma-≡ᵍ-refl : {g : Graph} → g ≡ᵍ g
  lemma-≡ᵍ-refl = (id , id) , (id , id)

  lemma-≡ᵍ-sym : {g₁ g₂ : Graph} → g₁ ≡ᵍ g₂ → g₂ ≡ᵍ g₁
  lemma-≡ᵍ-sym ((V₁⊆V₂ , E₁⊆E₂) , (V₂⊆V₁ , E₂⊆E₁)) = (V₂⊆V₁ , E₂⊆E₁) , V₁⊆V₂ , E₁⊆E₂
  
  lemma-≡ᵍ-trans : {g₁ g₂ g₃ : Graph} → g₁ ≡ᵍ g₂ → g₂ ≡ᵍ g₃ → g₁ ≡ᵍ g₃
  lemma-≡ᵍ-trans ((V₁⊆V₂ , E₁⊆E₂) , (V₂⊆V₁ , E₂⊆E₁)) ((V₂⊆V₃ , E₂⊆E₃) , (V₃⊆V₂ , E₃⊆E₂)) =
                 ((V₂⊆V₃ ∘ V₁⊆V₂) , (E₂⊆E₃ ∘ E₁⊆E₂)) , ((V₂⊆V₁ ∘ V₃⊆V₂) , (E₂⊆E₁ ∘ E₃⊆E₂))

  ≡ᵍ-is-equivalence : IsEquivalence _≡ᵍ_
  ≡ᵍ-is-equivalence = record { refl = lemma-≡ᵍ-refl ; sym = lemma-≡ᵍ-sym ; trans = lemma-≡ᵍ-trans }

  lemma-⊆ᵍ-refl : {g : Graph} → g ⊆ᵍ g
  lemma-⊆ᵍ-refl = id , id

  lemma-⊆ᵍ-trans : {g₁ g₂ g₃ : Graph} → g₁ ⊆ᵍ g₂ → g₂ ⊆ᵍ g₃ → g₁ ⊆ᵍ g₃
  lemma-⊆ᵍ-trans (V₁⊆V₂ , E₁⊆E₂) (V₂⊆V₃ , E₂⊆E₃) = (V₂⊆V₃ ∘ V₁⊆V₂) , (E₂⊆E₃ ∘ E₁⊆E₂)

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

  lemma-*-commutative : {g₁ g₂ : Graph} → g₁ * g₂ ≡ᵍ g₂ * g₁
  lemma-*-commutative = (swap , map⊎ swap swap) , (swap , map⊎ swap swap)
  
  lemma-*-associative : {g₁ g₂ g₃ : Graph} → (g₁ * g₂) * g₃ ≡ᵍ g₁ * (g₂ * g₃)
  lemma-*-associative = (assocʳ , λ { (inj₁ (inj₁ (inj₁ (inj₁ x)))) → inj₁ (inj₁ x)
                                    ; (inj₁ (inj₁ (inj₁ (inj₂ y)))) → inj₁ (inj₂ (inj₁ (inj₁ y)))
                                    ; (inj₁ (inj₁ (inj₂ (inj₁ (fst , snd))))) → inj₂ (inj₁ (fst , inj₁ snd))
                                    ; (inj₁ (inj₁ (inj₂ (inj₂ (fst , snd))))) → inj₂ (inj₂ (inj₁ fst , snd))
                                    ; (inj₁ (inj₂ y)) → inj₁ (inj₂ (inj₁ (inj₂ y)))
                                    ; (inj₂ (inj₁ (inj₁ x , snd))) → inj₂ (inj₁ (x , inj₂ snd))
                                    ; (inj₂ (inj₁ (inj₂ y , snd))) → inj₁ (inj₂ (inj₂ (inj₁ (y , snd))))
                                    ; (inj₂ (inj₂ (fst , inj₁ x))) → inj₂ (inj₂ (inj₂ fst , x))
                                    ; (inj₂ (inj₂ (fst , inj₂ y))) → inj₁ (inj₂ (inj₂ (inj₂ (fst , y))))})
                       , (assocˡ , λ { (inj₁ (inj₁ x)) → inj₁ (inj₁ (inj₁ (inj₁ x)))
                                    ; (inj₁ (inj₂ (inj₁ (inj₁ x)))) → inj₁ (inj₁ (inj₁ (inj₂ x)))
                                    ; (inj₁ (inj₂ (inj₁ (inj₂ y)))) → inj₁ (inj₂ y)
                                    ; (inj₁ (inj₂ (inj₂ (inj₁ (fst , snd))))) → inj₂ (inj₁ (inj₂ fst , snd))
                                    ; (inj₁ (inj₂ (inj₂ (inj₂ (fst , snd))))) → inj₂ (inj₂ (fst , inj₂ snd))
                                    ; (inj₂ (inj₁ (fst , inj₁ x))) → inj₁ (inj₁ (inj₂ (inj₁ (fst , x))))
                                    ; (inj₂ (inj₁ (fst , inj₂ y))) → inj₂ (inj₁ (inj₁ fst , y))
                                    ; (inj₂ (inj₂ (inj₁ x , snd))) → inj₁ (inj₁ (inj₂ (inj₂ (x , snd))))
                                    ; (inj₂ (inj₂ (inj₂ y , snd))) → inj₂ (inj₂ (y , inj₁ snd))})

  lemma-*-congruenceˡ : {g₁ g₂ g₃ : Graph} -> g₁ ≡ᵍ g₂ -> g₁ * g₃ ≡ᵍ g₂ * g₃
  lemma-*-congruenceˡ ((V₁⊆V₂ , E₁⊆E₂) , (V₂⊆V₁ , E₂⊆E₁)) = (map⊎ V₁⊆V₂ id , map⊎ (map⊎ E₁⊆E₂ id) (map⊎ (map× V₁⊆V₂ id) (map× id V₁⊆V₂)))
                                                          , (map⊎ V₂⊆V₁ id , map⊎ (map⊎ E₂⊆E₁ id) (map⊎ (map× V₂⊆V₁ id) (map× id V₂⊆V₁)))

  lemma-*-congruenceʳ : {g₁ g₂ g₃ : Graph} -> g₁ ≡ᵍ g₂ -> g₃ * g₁ ≡ᵍ g₃ * g₂
  lemma-*-congruenceʳ ((V₁⊆V₂ , E₁⊆E₂) , (V₂⊆V₁ , E₂⊆E₁)) = (map⊎ id V₁⊆V₂ , map⊎ (map⊎ id E₁⊆E₂) (map⊎ (map× id V₁⊆V₂) (map× V₁⊆V₂ id)))
                                                          , (map⊎ id V₂⊆V₁ , map⊎ (map⊎ id E₂⊆E₁) (map⊎ (map× id V₂⊆V₁) (map× V₂⊆V₁ id)))

  lemma-*ε : {g : Graph} → g ≡ᵍ g * ε
  lemma-*ε = (inj₁ , inj₁ ∘ inj₁) , ([ id , ⊥-elim ] , [ [ id , ⊥-elim ] , [ ⊥-elim ∘ proj₂ , ⊥-elim ∘ proj₁ ] ])

module Graph.Undirected.Properties {L : Set} where
  open import Data.Product using (_×_; _,_; map)

  open import Graph.Undirected.Core
  open import Graph.Common.Definitions {L} {_↦_∈E[_]}
  open import Graph.Common.Properties {L} {_↦_∈E[_]} public
  
  lemma-soundness : {x y : L} → (g : Graph) → x ↦ y ∈E[ g ] → x ∈V[ g ] × y ∈V[ g ]
  lemma-soundness (g₁ + g₂) (+-Eˡ xE₁y) = map +-Vˡ +-Vˡ (lemma-soundness g₁ xE₁y)
  lemma-soundness (g₁ + g₂) (+-Eʳ xE₂y) = map +-Vʳ +-Vʳ (lemma-soundness g₂ xE₂y)
  lemma-soundness (g₁ * g₂) (*-Eˡ xE₁y) = map *-Vˡ *-Vˡ (lemma-soundness g₁ xE₁y)
  lemma-soundness (g₁ * g₂) (*-Eʳ xE₂y) = map *-Vʳ *-Vʳ (lemma-soundness g₂ xE₂y)
  lemma-soundness (g₁ * g₂) (*-Eˣ₁ x∈V₁ y∈V₂) = *-Vˡ x∈V₁ , *-Vʳ y∈V₂
  lemma-soundness (g₁ * g₂) (*-Eˣ₂ y∈V₁ x∈V₂) = *-Vʳ x∈V₂ , *-Vˡ y∈V₁

  lemma-+-commutative : {g₁ g₂ : Graph} → g₁ + g₂ ≡ᵍ g₂ + g₁
  lemma-+-commutative = ((λ { (+-Vˡ x∈V₁) → +-Vʳ x∈V₁ ;
                              (+-Vʳ x∈V₂) → +-Vˡ x∈V₂})
                        , λ { (+-Eˡ xE₁y) → +-Eʳ xE₁y
                            ; (+-Eʳ xE₂y) → +-Eˡ xE₂y})
                      , ((λ { (+-Vˡ x∈V₂) → +-Vʳ x∈V₂
                            ; (+-Vʳ x∈V₁) → +-Vˡ x∈V₁})
                        , λ { (+-Eˡ xE₂y) → +-Eʳ xE₂y
                            ; (+-Eʳ xE₁y) → +-Eˡ xE₁y})
  
  lemma-+-associative : {g₁ g₂ g₃ : Graph} → (g₁ + g₂) + g₃ ≡ᵍ g₁ + (g₂ + g₃)
  lemma-+-associative = ((λ { (+-Vˡ (+-Vˡ x∈V₁)) → +-Vˡ x∈V₁
                            ; (+-Vˡ (+-Vʳ x∈V₂)) → +-Vʳ (+-Vˡ x∈V₂) ;
                              (+-Vʳ x∈V₃) → +-Vʳ (+-Vʳ x∈V₃)})
                        , λ { (+-Eˡ (+-Eˡ xE₁y)) → +-Eˡ xE₁y
                            ; (+-Eˡ (+-Eʳ xE₂y)) → +-Eʳ (+-Eˡ xE₂y)
                            ; (+-Eʳ xE₃y) → +-Eʳ (+-Eʳ xE₃y)})
                      , ((λ { (+-Vˡ x∈V₁) → +-Vˡ (+-Vˡ x∈V₁)
                            ; (+-Vʳ (+-Vˡ x∈V₂)) → +-Vˡ (+-Vʳ x∈V₂)
                            ; (+-Vʳ (+-Vʳ x∈V₃)) → +-Vʳ x∈V₃})
                        , λ { (+-Eˡ xE₁y) → +-Eˡ (+-Eˡ xE₁y)
                            ; (+-Eʳ (+-Eˡ xE₂y)) → +-Eˡ (+-Eʳ xE₂y)
                            ; (+-Eʳ (+-Eʳ xE₃y)) → +-Eʳ xE₃y})

  lemma-+-congruenceˡ : {g₁ g₂ g₃ : Graph} -> g₁ ≡ᵍ g₂ -> g₁ + g₃ ≡ᵍ g₂ + g₃
  lemma-+-congruenceˡ ((V₁⊆V₂ , E₁⊆E₂) , (V₂⊆V₁ , E₂⊆E₁)) = ((λ { (+-Vˡ x∈V₁) → +-Vˡ (V₁⊆V₂ x∈V₁)
                                                                ; (+-Vʳ x∈V₃) → +-Vʳ x∈V₃})
                                                          , (λ { (+-Eˡ xE₁y) → +-Eˡ (E₁⊆E₂ xE₁y)
                                                               ; (+-Eʳ xE₃y) → +-Eʳ xE₃y}))
                                                         , ((λ { (+-Vˡ x∈V₂) → +-Vˡ (V₂⊆V₁ x∈V₂)
                                                               ; (+-Vʳ x∈V₃) → +-Vʳ x∈V₃})
                                                          , (λ { (+-Eˡ xE₂y) → +-Eˡ (E₂⊆E₁ xE₂y)
                                                               ; (+-Eʳ xE₃y) → +-Eʳ xE₃y}))

  lemma-+-congruenceʳ : {g₁ g₂ g₃ : Graph} -> g₁ ≡ᵍ g₂ -> g₃ + g₁ ≡ᵍ g₃ + g₂
  lemma-+-congruenceʳ ((V₁⊆V₂ , E₁⊆E₂) , (V₂⊆V₁ , E₂⊆E₁)) = ((λ { (+-Vˡ x∈V₃) → +-Vˡ x∈V₃
                                                                ; (+-Vʳ x∈V₁) → +-Vʳ (V₁⊆V₂ x∈V₁)})
                                                           , (λ { (+-Eˡ xE₃y) → +-Eˡ xE₃y
                                                                ; (+-Eʳ xE₁y) → +-Eʳ (E₁⊆E₂ xE₁y)}))
                                                          , ((λ { (+-Vˡ x∈V₃) → +-Vˡ x∈V₃
                                                                ; (+-Vʳ x∈V₂) → +-Vʳ (V₂⊆V₁ x∈V₂)})
                                                           , (λ { (+-Eˡ xE₃y) → +-Eˡ xE₃y
                                                                ; (+-Eʳ xE₂y) → +-Eʳ (E₂⊆E₁ xE₂y)}))

  lemma-+ε : {g : Graph} → g ≡ᵍ g + ε
  lemma-+ε = ((λ {x∈V → +-Vˡ x∈V})
            , (λ {xEy → +-Eˡ xEy}))
           , ((λ { (+-Vˡ x∈V) → x∈V})
            , (λ { (+-Eˡ xEy) → xEy}))
  
  lemma-*-associative : {g₁ g₂ g₃ : Graph} → (g₁ * g₂) * g₃ ≡ᵍ g₁ * (g₂ * g₃)
  lemma-*-associative = ((λ { (*-Vˡ (*-Vˡ x∈V₁)) → *-Vˡ x∈V₁
                            ; (*-Vˡ (*-Vʳ x∈V₂)) → *-Vʳ (*-Vˡ x∈V₂)
                            ; (*-Vʳ x∈V₃) → *-Vʳ (*-Vʳ x∈V₃)})
                       , (λ { (*-Eˡ (*-Eˡ xE₁y)) → *-Eˡ xE₁y
                            ; (*-Eˡ (*-Eʳ xE₂y)) → *-Eʳ (*-Eˡ xE₂y)
                            ; (*-Eˡ (*-Eˣ₁ x∈V₁ y∈V₂)) → *-Eˣ₁ x∈V₁ (*-Vˡ y∈V₂)
                            ; (*-Eˡ (*-Eˣ₂ y∈V₁ x∈V₂)) → *-Eˣ₂ y∈V₁ (*-Vˡ x∈V₂)
                            ; (*-Eʳ xE₃y) → *-Eʳ (*-Eʳ xE₃y)
                            ; (*-Eˣ₁ (*-Vˡ x∈V₁) y∈V₃) → *-Eˣ₁ x∈V₁ (*-Vʳ y∈V₃)
                            ; (*-Eˣ₁ (*-Vʳ x∈V₂) y∈V₃) → *-Eʳ (*-Eˣ₁ x∈V₂ y∈V₃)
                            ; (*-Eˣ₂ (*-Vˡ x∈V₁) y∈V₃) → *-Eˣ₂ x∈V₁ (*-Vʳ y∈V₃)
                            ; (*-Eˣ₂ (*-Vʳ x∈V₂) y∈V₃) → *-Eʳ (*-Eˣ₂ x∈V₂ y∈V₃)}))
                      , ((λ { (*-Vˡ x∈V₁) → *-Vˡ (*-Vˡ x∈V₁)
                            ; (*-Vʳ (*-Vˡ x∈V₂)) → *-Vˡ (*-Vʳ x∈V₂)
                            ; (*-Vʳ (*-Vʳ x∈V₃)) → *-Vʳ x∈V₃})
                       , (λ { (*-Eˡ xE₁y) → *-Eˡ (*-Eˡ xE₁y)
                            ; (*-Eʳ (*-Eˡ xE₂y)) → *-Eˡ (*-Eʳ xE₂y)
                            ; (*-Eʳ (*-Eʳ xE₃y)) → *-Eʳ xE₃y
                            ; (*-Eʳ (*-Eˣ₁ x∈V₂ y∈V₃)) → *-Eˣ₁ (*-Vʳ x∈V₂) y∈V₃
                            ; (*-Eʳ (*-Eˣ₂ y∈V₂ x∈V₃)) → *-Eˣ₂ (*-Vʳ y∈V₂) x∈V₃
                            ; (*-Eˣ₁ x∈V₁ (*-Vˡ y∈V₂)) → *-Eˡ (*-Eˣ₁ x∈V₁ y∈V₂)
                            ; (*-Eˣ₁ x∈V₁ (*-Vʳ y∈V₃)) → *-Eˣ₁ (*-Vˡ x∈V₁) y∈V₃
                            ; (*-Eˣ₂ y∈V₁ (*-Vˡ x∈V₂)) → *-Eˡ (*-Eˣ₂ y∈V₁ x∈V₂)
                            ; (*-Eˣ₂ y∈V₁ (*-Vʳ x∈V₃)) → *-Eˣ₂ (*-Vˡ y∈V₁) x∈V₃}))

  lemma-*-congruenceˡ : {g₁ g₂ g₃ : Graph} -> g₁ ≡ᵍ g₂ -> g₁ * g₃ ≡ᵍ g₂ * g₃
  lemma-*-congruenceˡ ((V₁⊆V₂ , E₁⊆E₂) , (V₂⊆V₁ , E₂⊆E₁)) = ((λ { (*-Vˡ x∈V₁) → *-Vˡ (V₁⊆V₂ x∈V₁)
                                                                ; (*-Vʳ x∈V₃) → *-Vʳ x∈V₃})
                                                           , (λ { (*-Eˡ xE₁y) → *-Eˡ (E₁⊆E₂ xE₁y)
                                                                ; (*-Eʳ xE₃y) → *-Eʳ xE₃y
                                                                ; (*-Eˣ₁ x∈V₁ y∈V₃) → *-Eˣ₁ (V₁⊆V₂ x∈V₁) y∈V₃
                                                                ; (*-Eˣ₂ y∈V₁ x∈V₃) → *-Eˣ₂ (V₁⊆V₂ y∈V₁) x∈V₃}))
                                                          , ((λ { (*-Vˡ x∈V₂) → *-Vˡ (V₂⊆V₁ x∈V₂)
                                                                ; (*-Vʳ x∈V₃) → *-Vʳ x∈V₃})
                                                           , (λ { (*-Eˡ xE₂y) → *-Eˡ (E₂⊆E₁ xE₂y)
                                                                ; (*-Eʳ xE₃y) → *-Eʳ xE₃y
                                                                ; (*-Eˣ₁ x∈V₂ y∈V₃) → *-Eˣ₁ (V₂⊆V₁ x∈V₂) y∈V₃
                                                                ; (*-Eˣ₂ y∈V₂ x∈V₃) → *-Eˣ₂ (V₂⊆V₁ y∈V₂) x∈V₃}))

  lemma-*-congruenceʳ : {g₁ g₂ g₃ : Graph} -> g₁ ≡ᵍ g₂ -> g₃ * g₁ ≡ᵍ g₃ * g₂
  lemma-*-congruenceʳ ((V₁⊆V₂ , E₁⊆E₂) , (V₂⊆V₁ , E₂⊆E₁)) = ((λ { (*-Vˡ x∈V₃) → *-Vˡ x∈V₃
                                                                ; (*-Vʳ x∈V₁) → *-Vʳ (V₁⊆V₂ x∈V₁)})
                                                           , (λ { (*-Eˡ xE₃y) → *-Eˡ xE₃y
                                                                ; (*-Eʳ xE₁y) → *-Eʳ (E₁⊆E₂ xE₁y)
                                                                ; (*-Eˣ₁ x∈V₃ y∈V₁) → *-Eˣ₁ x∈V₃ (V₁⊆V₂ y∈V₁)
                                                                ; (*-Eˣ₂ y∈V₃ x∈V₁) → *-Eˣ₂ y∈V₃ (V₁⊆V₂ x∈V₁)}))
                                                          , ((λ { (*-Vˡ x∈V₃) → *-Vˡ x∈V₃
                                                                ; (*-Vʳ x∈V₂) → *-Vʳ (V₂⊆V₁ x∈V₂)})
                                                           , (λ { (*-Eˡ xE₃y) → *-Eˡ xE₃y
                                                                ; (*-Eʳ xE₂y) → *-Eʳ (E₂⊆E₁ xE₂y)
                                                                ; (*-Eˣ₁ x∈V₃ y∈V₂) → *-Eˣ₁ x∈V₃ (V₂⊆V₁ y∈V₂)
                                                                ; (*-Eˣ₂ y∈V₃ x∈V₂) → *-Eˣ₂ y∈V₃ (V₂⊆V₁ x∈V₂)}))

  lemma-*ε : {g : Graph} → g ≡ᵍ g * ε
  lemma-*ε = ((λ {x∈V → *-Vˡ x∈V})
            , (λ {xEy → *-Eˡ xEy}))
           , ((λ { (*-Vˡ x∈V) → x∈V})
            , (λ { (*-Eˡ xEy) → xEy}))

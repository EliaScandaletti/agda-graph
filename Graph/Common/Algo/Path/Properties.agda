open import Relation.Nullary using (Dec)
open import Relation.Binary using (DecidableEquality)
open import Data.Product using (_×_)
module Graph.Common.Algo.Path.Properties 
  {L Graph : Set}
  {_∈V[_] : L → Graph → Set}
  (V-of? : (g : Graph) → (x : L) → Dec (x ∈V[ g ]))
  {_↦_∈E[_] : L → L → Graph → Set}
  (E-of? : (g : Graph) → (x y : L) → Dec (x ↦ y ∈E[ g ]))
  (lemma-soundness : {x y : L} → (g : Graph) → x ↦ y ∈E[ g ] → x ∈V[ g ] × y ∈V[ g ])
  where
  open import Function using (_∘_)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; module ≡-Reasoning)
  open ≡-Reasoning
  open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Data.Product using (Σ; _,_; proj₁; proj₂)
  
  open import Graph.Common.Algo.Path V-of? E-of? lemma-soundness hiding (module Weighted)

  nf-cancel : {g : Graph} {s x d : L} {Esx : True (E-of? g s x)} → (p : Path g x d)
    → normal-form ((s ↦ normal-form p) {Esx}) ≡ normal-form ((s ↦ p) {Esx})
  nf-cancel (_ #) = refl
  nf-cancel (_ ↦ _ #) = refl
  nf-cancel (_ ↦ (_ #)) = refl
  nf-cancel (_ ↦ (_ ↦ _ #)) = refl
  nf-cancel {s = s} (x ↦ (y ↦ p)) = cong (s ↦_) (nf-cancel (y ↦ p))

  nf-nf≡nf : {g : Graph} {s d : L} → (p : Path g s d) → normal-form (normal-form p) ≡ normal-form p
  nf-nf≡nf (_ #) = refl
  nf-nf≡nf (_ ↦ _ #) = refl
  nf-nf≡nf (_ ↦ (_ #)) = refl
  nf-nf≡nf (_ ↦ (_ ↦ _ #)) = refl
  nf-nf≡nf (s ↦ (x ↦ p)) = nf-cancel (x ↦ p)

  split : {g : Graph} {s d : L} → (p : Path g s d) → {x : L} → p visits x
    → Σ ((Path g s x) × (Path g x d)) λ { (fst , snd) → fst ++ snd ≡ normal-form p}
  split ((s #) {rv}) refl = ((s #) {rv} , (s #)) , refl
  split {g} ((s ↦ d #) {Esx}) (inj₁ refl) = ((s #) {fromWitness (proj₁ (lemma-soundness g (toWitness Esx)))} , s ↦ d #) , refl
  split {g} ((s ↦ d #) {Esx}) (inj₂ refl) = (s ↦ d # , (d #) {fromWitness (proj₂ (lemma-soundness g (toWitness Esx)))}) , refl
  split {g} ((s ↦ p) {Esx}) (inj₁ refl) = ((s #) {fromWitness (proj₁ (lemma-soundness g (toWitness Esx)))} , (s ↦ p)) , refl
  split ((s ↦ p) {re}) (inj₂ vis) with split p vis
  ... | (fst , snd) , ++≡nf = ((s ↦ fst) {re} , snd) , (begin
    ((s ↦ fst) ++ snd) ≡⟨⟩
    normal-form (s ↦ (fst ++ snd)) ≡⟨ cong (normal-form ∘ (s ↦_)) ++≡nf ⟩
    normal-form (s ↦ (normal-form p)) ≡⟨ nf-cancel p ⟩
    normal-form (s ↦ p) ∎)
  
  open import Algebra.Structures using (IsMonoid)
  open import Relation.Binary using (IsDecTotalOrder)
  module Weighted
    {W : Set}
    {_+_ : W → W → W} {ε : W} (W-isMonoid : IsMonoid _≡_ _+_ ε)
    {_≤_ : W → W → Set} (W-isDecTotalOrder : IsDecTotalOrder _≡_ _≤_)
    {g : Graph} (w : {x y : L} → .(x ↦ y ∈E[ g ]) → W) where
    open import Graph.Common.Algo.Path V-of? E-of? lemma-soundness using (module Weighted)
    open Weighted W-isMonoid W-isDecTotalOrder w
    open IsMonoid W-isMonoid using (identity; assoc)

    weight-nf-≡ : {s d : L} → (p : Path g s d) → weight (normal-form p) ≡ weight p
    weight-nf-≡ (_ #) = refl
    weight-nf-≡ (_ ↦ _ #) = refl
    weight-nf-≡ (_ ↦ (_ #)) = sym ((proj₂ identity) _)
    weight-nf-≡ (_ ↦ (_ ↦ _ #)) = refl
    weight-nf-≡ (_ ↦ (x ↦ p)) = cong (_ +_) (weight-nf-≡ (x ↦ p))

    weight-++-≡ : {s x d : L} → (p : Path g s x) → (q : Path g x d) → weight (p ++ q) ≡ weight p + weight q
    weight-++-≡ (_ #) q rewrite weight-nf-≡ q = sym (proj₁ identity _)
    weight-++-≡ ((s ↦ _ #) {e}) q rewrite weight-nf-≡ ((s ↦ q) {e}) = refl
    weight-++-≡ ((s ↦ p) {e}) q rewrite weight-nf-≡ ((s ↦ (p ++ q)) {e}) | weight-++-≡ p q = sym (assoc _ (weight p) (weight q))

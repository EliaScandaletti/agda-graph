open import Relation.Nullary using (Dec)
open import Data.Product using (_×_)
module Graph.Common.Algo.Path
  {L Graph : Set}
  {_∈V[_] : L → Graph → Set}
  (V-of? : (g : Graph) → (x : L) → Dec (x ∈V[ g ]))
  {_↦_∈E[_] : L → L → Graph → Set}
  (E-of? : (g : Graph) → (x y : L) → Dec (x ↦ y ∈E[ g ]))
  (lemma-soundness : {x y : L} → (g : Graph) → x ↦ y ∈E[ g ] → x ∈V[ g ] × y ∈V[ g ])
  where
  open import Function using (_∘_)
  open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; module ≡-Reasoning)
  open ≡-Reasoning
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)

  data Path (g : Graph) : L → L → Set where
    _# : (v : L) → {True (V-of? g v)} → Path g v v
    _↦_# : (s d : L) → {True (E-of? g s d)} → Path g s d
    _↦_ : (s : L) → {x d : L} → Path g x d → {True (E-of? g s x)} → Path g s d

  normal-form : {g : Graph} {s d : L} → Path g s d → Path g s d
  normal-form ((s #) {Vs}) = (s #) {Vs}
  normal-form ((s ↦ d #) {Esd}) = (s ↦ d #) {Esd}
  normal-form ((s ↦ (d #)) {Esd}) = (s ↦ d #) {Esd}
  normal-form ((s ↦ ((x ↦ d #) {Exd})) {Esx}) = (s ↦ ((x ↦ d #) {Exd})) {Esx}
  normal-form ((s ↦ ((x ↦ p) {Exd})) {Esx}) = (s ↦ normal-form ((x ↦ p) {Exd})) {Esx}

  _visits_ : {g : Graph} {s d : L} → Path g s d → L → Set
  (s #) visits v = s ≡ v
  (s ↦ d #) visits v = s ≡ v ⊎ d ≡ v
  (s ↦ p) visits v = (s ≡ v) ⊎ (p visits v)

  _++_ : {g : Graph} {s x d : L} → Path g s x  → Path g x d → Path g s d
  (_ #) ++ p = normal-form p
  (_↦_# s x {sx∈E}) ++ p = normal-form ((s ↦ p) {sx∈E})
  (_↦_ s q {sx∈E}) ++ p = normal-form ((s ↦ (q ++ p)) {sx∈E})

  open import Algebra.Structures using (IsMonoid)
  open import Relation.Binary using (IsDecTotalOrder)
  module Weighted
    {W : Set}
    {_+_ : W → W → W} {ε : W} (W-isMonoid : IsMonoid _≡_ _+_ ε)
    {_≤_ : W → W → Set} (W-isDecTotalOrder : IsDecTotalOrder _≡_ _≤_)
    {g : Graph} (w : {x y : L} → .(x ↦ y ∈E[ g ]) → W) where
    open IsMonoid W-isMonoid using (identity; assoc)
    open IsDecTotalOrder W-isDecTotalOrder using (_≤?_)

    weight : {s d : L} → Path g s d → W
    weight (v #) = ε
    weight ((s ↦ d #) {q}) = w (toWitness q)
    weight ((s ↦ p) {q}) = (w (toWitness q)) + (weight p)
  
    _≼_ : {s d : L} → Path g s d → Path g s d → Set
    _≼_ p q = (weight p) ≤ (weight q)
    
    _≼?_ : {s d : L} → (p q : Path g s d) → Dec (p ≼ q)
    _≼?_ p q = (weight p) ≤? weight q

module Graph.Core.Recursion {L : Set} where
    open import Data.Nat using (ℕ; zero; suc; s≤s) renaming (_<_ to _<ᴺ_; _+_ to _+ᴺ_)
    open import Data.Nat.Properties using (≤-trans)

    open import Graph.Core {L}

    data Accᴺ : ℕ → Set where
      accᴺ : {x : ℕ} → ({y : ℕ} → y <ᴺ x → Accᴺ y) → Accᴺ x
    wfᴺ : (n : ℕ) → Accᴺ n
    wfᴺ zero    = accᴺ λ ()
    wfᴺ (suc n) with wfᴺ n
    ... | accᴺ y<n→Ay = accᴺ λ { {y} (s≤s y≤n) → accᴺ (λ {y₁} y₁<y → y<n→Ay (≤-trans y₁<y y≤n))}

    #_ : Graph → ℕ
    # ε = 0
    # (v x) = 0
    # (g₃ + g₄) = 1 +ᴺ (# g₃) +ᴺ (# g₄)
    # (g₃ * g₄) = 1 +ᴺ (# g₃) +ᴺ (# g₄)

    data _<_ : Graph → Graph → Set where
      lift : {g₃ g₄ : Graph} → (# g₃) <ᴺ (# g₄) → g₃ < g₄

    data Acc : Graph → Set where
      acc : {g : Graph} → ({g' : Graph} → g' < g → Acc g') → Acc g

    wf : (g : Graph) → Acc g
    wf g = l g (wfᴺ (# g)) where
      l : (g : Graph) → Accᴺ (# g) → Acc g
      l ε (accᴺ x) = acc λ { (lift ())}
      l (v x₁) (accᴺ x) = acc λ { (lift ())}
      l (g₁ + g₂) (accᴺ y≤#g→Ay) = acc λ { {g'} (lift (s≤s #g'≤#g)) → l g' (y≤#g→Ay (s≤s #g'≤#g))}
      l (g₁ * g₂) (accᴺ y≤#g→Ay) = acc λ { {g'} (lift (s≤s #g'≤#g)) → l g' (y≤#g→Ay (s≤s #g'≤#g))}

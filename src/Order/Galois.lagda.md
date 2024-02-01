```agda

open import Cat.Prelude
open import Order.Base

module Order.Galois where

-- private variable
--   o₁ o₂ ℓ₁ ℓ₂ {P : Poset o₁ ℓ₁} {Q : Poset o₂ ℓ₂} 

galois-level : ∀ {o₁ ℓ₁ o₂ ℓ₂} (P : Poset o₁ ℓ₁) (D : Poset o₂ ℓ₂)
          → Level
galois-level {o₁ = o₁} {ℓ₁} {o₂} {ℓ₂} _ _ = o₁ ⊔ o₂ ⊔ ℓ₁ ⊔ ℓ₂

module _ {o₁ o₂ ℓ₁ ℓ₂} {P : Poset o₁ ℓ₁} {Q : Poset o₂ ℓ₂} where
  private
    module P = Poset P
    module Q = Poset Q

  record _⊣_ (f : Monotone P Q) (g : Monotone Q P) : Type (galois-level P Q) where
    private
      module f = Monotone f
      module g = Monotone g
    field
      unit : idₘ =>ₘ (g ∘ₘ f)
      counit : (f ∘ₘ g) =>ₘ idₘ
      
    open _=>ₘ_ unit public
    open _=>ₘ_ counit public renaming (η to ε)

    -- Our definition implies the other standard one
    path : ∀ {a b} → Lift ℓ₁ (f # a Q.≤ b) ≡ Lift ℓ₂ (a P.≤ g # b)
    path = Iso→Path $ 
      (λ (lift q) → lift (P.≤-trans (η _) (g.pres-≤ q))) , 
      iso (λ (lift p) → lift (Q.≤-trans (f.pres-≤ p) (ε _)))
          (λ _ → prop!) 
          (λ _ → prop!) 



```
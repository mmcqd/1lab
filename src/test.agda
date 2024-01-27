

open import Cat.Prelude
open import Cat.Functor.Adjoint
open import Cat.Instances.Shape.Terminal
open import Cat.Instances.Product

open Precategory
open Functor
open _=>_
open _⊣_

module test where

module A κ where
  Forget = !F

  Cofree : Functor ⊤Cat (Sets κ)
  Cofree .F₀ _ = el! (Lift _ ⊤)
  Cofree .F₁ _ _ = lift tt
  Cofree .F-id = refl
  Cofree .F-∘ _ _ = refl

  Forget⊣Cofree : Forget ⊣ Cofree
  Forget⊣Cofree .unit .η _ _ = lift tt
  Forget⊣Cofree .unit .is-natural _ _ _ = refl
  Forget⊣Cofree .counit .η _ = tt
  Forget⊣Cofree .counit .is-natural _ _ _ = refl
  Forget⊣Cofree .zig = refl
  Forget⊣Cofree .zag = refl

  Free : Functor ⊤Cat (Sets κ)
  Free .F₀ _ = el! (Lift _ ⊥) 
  Free .F₁ _ x = x
  Free .F-id = refl
  Free .F-∘ _ _ = refl 

  Free⊣Forget : Free ⊣ Forget
  Free⊣Forget .unit .η _ = tt
  Free⊣Forget .unit .is-natural _ _ _ = refl
  Free⊣Forget .counit .η _ ()
  Free⊣Forget .counit .is-natural _ _ _ = ext λ ()
  Free⊣Forget .zig = ext λ ()
  Free⊣Forget .zag = refl

module B κ where
  Sets² = Sets κ ×ᶜ Sets κ

  Forget : Functor Sets² (Sets κ)
  Forget = Fst

  Cofree : Functor (Sets κ) Sets²
  Cofree .F₀ A = A , (el! (Lift _ ⊤))
  Cofree .F₁ f = f , (λ x → x)
  Cofree .F-id = refl
  Cofree .F-∘ f g = refl

  Forget⊣Cofree : Forget ⊣ Cofree
  Forget⊣Cofree .unit .η (A , B) = (λ x → x) , (λ _ → lift tt)
  Forget⊣Cofree .unit .is-natural _ _ (f , g) = refl
  Forget⊣Cofree .counit .η _ = λ x → x 
  Forget⊣Cofree .counit .is-natural _ _ _ = refl
  Forget⊣Cofree .zig = refl
  Forget⊣Cofree .zag = refl

  Free : Functor (Sets κ) Sets²
  Free .F₀ A = A , (el! (Lift _ ⊥))
  Free .F₁ f = f , (λ x → x)
  Free .F-id = refl
  Free .F-∘ _ _ = refl

  Free⊣Forget : Free ⊣ Forget
  Free⊣Forget .unit .η _ = λ x → x
  Free⊣Forget .unit .is-natural _ _ _ = refl
  Free⊣Forget .counit .η (A , B) = (λ z → z) , (λ ())
  Free⊣Forget .counit .is-natural _ _ _ = ext ((λ _ → refl) , λ ())
  Free⊣Forget .zig = ext ((λ _ → refl) , λ ())
  Free⊣Forget .zag = refl

module C κ where
  Sets² = Sets κ ×ᶜ Sets κ

  Pair : Functor Sets² (Sets κ)
  Pair .F₀ (A , B) = el! (⌞ A ⌟ × ⌞ B ⌟) 
  Pair .F₁ (f , g) (x , y) = f x , g y
  Pair .F-id = refl
  Pair .F-∘ f g = refl

  Δ : Functor (Sets κ) Sets²
  Δ .F₀ A = A , A
  Δ .F₁ f = f , f
  Δ .F-id = refl
  Δ .F-∘ f g = refl

  -- left : (Δ A → B) ≡ ((A , B) → Pair (C , D))
  -- right : (Pair (A , B) → (C , D)) ≡ (A → ℝ B)

  Δ⊣Pair : Δ ⊣ Pair
  Δ⊣Pair .unit .η A x = x , x
  Δ⊣Pair .unit .is-natural A B f = refl
  Δ⊣Pair .counit .η (A , B) = fst , snd
  Δ⊣Pair .counit .is-natural _ _ f = refl
  Δ⊣Pair .zig = refl
  Δ⊣Pair .zag = refl
  

  -- nope : (R : Functor (Sets κ) Sets²) → ¬ (Pair ⊣ R)
  -- nope R adj = {! Adj.unit .η  !} where
  --   module Adj = _⊣_ adj
    
  --   foo : Σ ∣ F₀ R (el! (Lift κ ⊥)) .fst ∣ (λ _ → ∣ F₀ R (el! (Lift κ ⊥)) .snd ∣) → Lift κ ⊥
  --   foo = Adj.counit .η (el! (Lift _ ⊥))
      
  Right : Functor (Sets κ) Sets²
  Right .F₀ A = el! (((⌞ A ⌟ → ⌞ A ⌟) → ⌞ A ⌟)) , el! (Lift _ ⊤)
  Right .F₁ f = (λ g a → {!   !}) , (λ x → x)
  Right .F-id = ext ({!   !} , {!   !})
  Right .F-∘ = {!   !}
  
  Pair⊣Right : Pair ⊣ Right
  Pair⊣Right .unit .η (A , B) = {!   !} , λ _ → lift tt
  Pair⊣Right .unit .is-natural = {!   !}
  Pair⊣Right .counit .η A (x , y) = {!   !}
  Pair⊣Right .counit .is-natural = {!   !}
  Pair⊣Right .zig = {!   !}
  Pair⊣Right .zag = {!   !}
  
  
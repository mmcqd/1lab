open import Cat.Prelude
open import Cat.Reasoning
open import Cat.Functor.Adjoint
open import Cat.Displayed.Reasoning
open import Cat.Displayed.Base
open import Cat.Displayed.Total hiding (∫ ; πᶠ) renaming (∫ᶠ to ∫ᶠ')
open import Cat.Displayed.Functor
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Cartesian.Discrete
open import Cat.Displayed.Cartesian.DFib
open import Cat.Displayed.Composition
open import Cat.Displayed.Instances.Pullback
open import Cat.Displayed.Instances.Product
open import Cat.Diagram.Terminal
open import Cat.Displayed.Instances.Lifting
open import Cat.Functor.Compose


module CwF-flat where


record Sub-notation {ℓ ℓ'} (Ix : Type ℓ) (A : Ix → Type ℓ') : Typeω where
  constructor sub-notation
  field
    {lvl} : Level
    Subst : Ix → Ix → Type lvl
    _[_] : ∀ {i j} → A i → Subst j i → A j
  infix 50 _[_]

open Sub-notation ⦃...⦄ using (_[_]) public

record Sub-Rel-notation {ℓ ℓ'} (Ix : Type ℓ) (A : Ix → Type ℓ') : Typeω where
  constructor sub-rel-notation
  field
    {l1 l2} : Level
    Subst : Ix → Ix → Type l1
    _[_]≡_ : ∀ {i j} → A i → Subst j i → A j → Type l2
  infix 40 _[_]≡_

open Sub-Rel-notation ⦃...⦄ using (_[_]≡_) public

{-# DISPLAY Sub-Rel-notation._[_]≡_ _ A γ B = A [ γ ]≡ B #-}

open Functor
open _=>_

record CwF oc ℓc ot ℓt : Type (lsuc (oc ⊔ ℓc ⊔ ot ⊔ ℓt)) where
  open ∫Hom  

  -- Contexts are just a category
  field
    𝒞 : Precategory oc ℓc

  DFib𝒞 : Precategory _ _
  DFib𝒞 = DFib 𝒞 ot ℓt

  module 𝒞 = Cat.Reasoning 𝒞
  module DFib𝒞 = Cat.Reasoning DFib𝒞

  field
    Tp : DFib𝒞.Ob
    Tm : DFib𝒞.Ob
    Infer : DFib𝒞.Hom Tm Tp
    ExtensionData : is-representable' Infer
  
  Extend = ExtensionData .fst

  Ext𝒞 : Functor (∫ Tp) 𝒞
  Ext𝒞 = πᶠ Tm F∘ Extend

  TpFam : DFib𝒞.Ob
  TpFam = {!   !}

--   P : ∀ {A : DFib𝒞.Ob} {B} → Functor (∫ A) B → Functor {! ∫ A   !} {!   !}
--   P f .F₀ x = {!   !}
--   P f .F₁ = {!   !}
--   P f .F-id = {!   !}
--   P f .F-∘ = {!   !} 
--     -- DFibΣ {!   !} ((f DFib^*) · {!   !})

--   -- DFibΠ : DFib𝒞.Ob → DFib𝒞/.Ob[ Tp ]
--   -- DFibΠ x = (Ext𝒞 DFib^*) · x

--   -- In Uemura's paper, (A ≡ SynData) and (B ≡ TpData)
--   TpFam : DFib𝒞.Ob
--   TpFam = DFibΣ Tp ((Ext𝒞 DFib^*) · Tp)


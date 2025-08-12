open import Cat.Prelude
open import Cat.Reasoning
open import Cat.Functor.Adjoint
open import Cat.Displayed.Reasoning
open import Cat.Displayed.Base
open import Cat.Displayed.Total
open import Cat.Displayed.Functor
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Cartesian.Discrete
open import Cat.Displayed.Cartesian.DFib
open import Cat.Displayed.Composition
open import Cat.Displayed.Instances.Pullback
open import Cat.Diagram.Terminal
open import Cat.Displayed.Instances.Lifting



module CwF where


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


record CwF oc ℓc ot ℓt : Type (lsuc (oc ⊔ ℓc ⊔ ot ⊔ ℓt)) where
  
  -- Contexts are just a category
  field
    𝒞 : Precategory oc ℓc

  DFib𝒞 : Precategory _ _
  DFib𝒞 = DFib 𝒞 ot ℓt

  DFib𝒞/ : Displayed DFib𝒞 _ _
  DFib𝒞/ = DFib/ 𝒞 ot ℓt

  module 𝒞 = Cat.Reasoning 𝒞
  module DFib𝒞 = Cat.Reasoning DFib𝒞
  module DFib𝒞⊤ = Terminal (DFib-terminal 𝒞 ot ℓt)
  module DFib/ {o ℓ o' ℓ'} {𝒮 : Precategory o ℓ} = Displayed (DFib/ 𝒮 o' ℓ')

  field
    TpData : DFib𝒞.Ob
    ChkData : DFib/.Ob[ TpData ]

  SynData : DFib𝒞.Ob
  SynData = TpData DFib/∘ ChkData

  Infer : DFib𝒞.Hom SynData TpData
  Infer = πᵈ

  Tps = TpData .fst
  Chks = ChkData .fst
  Syns = SynData .fst

  module Tps = DFib-Ob TpData
  module Chks = DFib-Ob ChkData
  module Syns = DFib-Ob SynData

  
  field
    ExtensionData : is-representable TpData ChkData
 
  Ext𝒞 : Functor (∫ Tps) 𝒞
  Ext𝒞 = (πᶠ Tps F∘ πᶠ Chks) F∘ ExtensionData .fst

  -- In Uemura's paper, (A ≡ SynData) and (B ≡ TpData)

  open Functor
  TpFamData : DFib/.Ob[ TpData ]
  TpFamData = (Ext𝒞 DFib^*) · TpData

  TpFam = TpFamData .fst

  ChkFamData : DFib/.Ob[ TpFamData ]
  ChkFamData = ({!   !} DFib^*) · ChkData


```agda

open import Cat.Prelude
open import Cat.Displayed.Base
open import Cat.Displayed.Total
open import Cat.Displayed.Cartesian.Discrete
open import Cat.Functor.Adjoint
open import Cat.Displayed.Instances.TotalProduct

import Cat.Reasoning
import Cat.Displayed.Reasoning

open Displayed

module Cat.DiscFibSem.NaturalModel where


record NaturalModel {o h t ot ht} : Type (lsuc (o ⊔ h ⊔ t ⊔ ot ⊔ ht)) where
  field
    {Ctxs} : Precategory o h
    Tp : Type t
    Tp-set : is-set Tp
    -- A presheaf (on Ctxs) of terms for each type
    Tm : (A : Tp) → Displayed Ctxs ot ht
    Tm-dfib : ∀ {A} → Discrete-fibration (Tm A)

    -- An inverse for projection, aka extension!
    Extend : ∀ A → Functor Ctxs (∫ (Tm A))

    -- Intuitively, πᶠ takes a context and a term in that context, and forgets the term
    -- So a right adjoint should undo projection in a way that preserves limits, e.g. concatenation
    -- (πᶠ (Tm A) (Γ , e) --> Γ) ≅ ((Γ , e) --> Extend A Γ)
    π⊣Extend : ∀ {A} → πᶠ (Tm A) ⊣ Extend A

    _`×_ : Tp → Tp → Tp
    -- `×-sem : ∀ {A B} → Tm (A `× B) ≡ {! _×ᵀᴰ_  !}

  private
    module Ctxs = Cat.Reasoning Ctxs
    module Tm A = Displayed (Tm A)
    module Tm* {A} = Discrete-fibration (Tm-dfib {A})
    module Extend A = Functor (Extend A)
    module π⊣Extend {A} = _⊣_ (π⊣Extend {A})
    open π⊣Extend
    open Total-hom

  Ctx : Type _
  Ctx = Ctxs.Ob

  Sub : Ctx → Ctx → Type _
  Sub = Ctxs.Hom

  _⊢_ : Ctx → Tp → Type _
  Γ ⊢ A = Tm.Ob[ A ] Γ

  variable
    Γ Δ Ξ : Ctx
    A B : Tp

  _[_] : Γ ⊢ A → Sub Δ Γ → Δ ⊢ A
  e [ γ ] = Tm*.lifts γ e .centre .fst

  _⨾_ : Ctx → Tp → Ctx
  Γ ⨾ A = Extend.₀ A Γ .fst






```
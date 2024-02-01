```agda

open import Cat.Prelude
open import Cat.Displayed.Base
open import Cat.Displayed.Total
open import Cat.Displayed.Cartesian.Discrete
open import Cat.Functor.Adjoint
open import Cat.Instances.DiscreteFibration
open import Cat.Diagram.Terminal
open import Cat.Diagram.Product
open import Cat.Diagram.Exponential
open import Cat.Displayed.Functor

import Cat.Reasoning
import Cat.Displayed.Reasoning

open Displayed
open Vertical-functor

module Cat.DiscFibSem.NaturalModel where


record NaturalModel {o h t κ} : Type (lsuc (o ⊔ h ⊔ t ⊔ κ)) where
  field
    {Ctxs} : Precategory o h
    Tp : Type t
    Tp-set : is-set Tp
    -- A presheaf (on Ctxs) of terms for each type
    Tm : (A : Tp) → Displayed Ctxs κ κ
    Tm-dfib : ∀ {A} → Discrete-fibration (Tm A)

    -- An inverse for projection, aka extension!
    -- Looks a bit weird because A is a type not a category.
    -- This is really a curried function, first argument is a type A
    -- second argument is a contest Γ
    -- the first argument is automatically functorial because it's a regular function
    -- the second is specified functorial by being a functor
    Extend : ∀ A → Functor Ctxs (∫ (Tm A))

    -- Intuitively, πᶠ takes a context and a term in that context, and forgets the term
    -- So a right adjoint should undo projection in a way that preserves limits, e.g. concatenation
    -- Sends a type and a context to a new context and the "least upper bound of terms in that context" aka 
    -- debruijn index zero
    -- (πᶠ (Tm A) (Γ , e) --> Γ) ≅ ((Γ , e) --> Extend A Γ)
    -- (πᶠ (Tm A) (Γ , e) → Δ) ≡ ((Γ , e) → Extend A Δ
    π⊣Extend : ∀ {A} → πᶠ (Tm A) ⊣ Extend A

  private
    module Ctxs = Cat.Reasoning Ctxs
    module Tm A = Displayed (Tm A)
    module Tm* {A} = Discrete-fibration (Tm-dfib {A})
    module Extend A = Functor (Extend A)
    module π⊣Extend {A} = _⊣_ (π⊣Extend {A})
    module DFib {o' ℓ'} = Cat.Reasoning (DFib Ctxs o' ℓ')
    open Binary-products (DFib Ctxs κ κ) (DFib-products _)
    open π⊣Extend
    open Total-hom

    ⟦_⟧ : Tp → DFib.Ob
    ⟦ A ⟧ = Tm A , Tm-dfib

  field
    `⊤ : Tp
    `⊤-sem : ⟦ `⊤ ⟧ DFib.≅ DFib-terminal Ctxs .Terminal.top

    _`×_ : (A B : Tp) → Tp
    `×-sem : ∀ {A B} → ⟦ A `× B ⟧ DFib.≅ (⟦ A ⟧ ⊗₀ ⟦ B ⟧)
    
  module `⊤-sem = DFib._≅_ `⊤-sem
  module `×-sem {A B} = DFib._≅_ (`×-sem {A} {B})
    
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
  e [ γ ] = e Tm*.[ γ ]

  _⨾_ : Ctx → Tp → Ctx
  Γ ⨾ A = Extend.₀ A Γ .fst

  `tt : Γ ⊢ `⊤
  `tt = `⊤-sem.from .F₀' (lift tt)

  -- `⊤-η : (x : Γ ⊢ `⊤) → `tt ≡ x
  -- `⊤-η x = sym (Tm*.hom→path foo) ∙ sym (ap fst $ Tm*.lifts Ctxs.id ? .paths (? , {! Tm*.lifts ? ? .centre .snd  !})) where
  
  --   foo : Tm.Hom[ `⊤ ] Ctxs.id (`⊤-sem.from .F₀' (lift tt)) (`⊤-sem.from .F₀' (lift tt))
  --   foo = `⊤-sem.from .F₁' refl





```
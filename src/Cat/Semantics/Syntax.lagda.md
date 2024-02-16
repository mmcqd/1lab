```agda
-- {-# OPTIONS --show-implicit #-}
open import Cat.Prelude hiding (⟪_⟫)
open import Cat.Diagram.Terminal
open import Cat.Diagram.Product
open import Cat.Semantics.NaturalModel
open import Cat.Functor.Naturality
open import Cat.Functor.Base
open import Cat.Functor.Hom.Representable
open import Data.Dec.Base
open import Cat.Functor.Hom
open import Cat.CartesianClosed.Instances.PSh

import Cat.Reasoning

open Precategory
open Functor
open _=>_
open make-natural-iso

open Terminal

module Cat.Semantics.Syntax where

infixr 25 _`×_ _`→_
data Tp : Type where
  `⊤ : Tp
  _`×_ _`→_ : Tp → Tp → Tp


instance
  Tp-discrete : Discrete Tp
  Tp-discrete = Discreteᵢ→discrete dec where
    dec : Discreteᵢ Tp
    dec `⊤ `⊤ = yes reflᵢ
    dec (x `× x₁) (y `× y₁) with dec x y | dec x₁ y₁
    ... | yes reflᵢ | yes reflᵢ = yes reflᵢ
    ... | yes a | no ¬a  = no λ where reflᵢ → ¬a reflᵢ 
    ... | no ¬a | yes a  = no λ where reflᵢ → ¬a reflᵢ
    ... | no ¬a | no ¬a₁ = no λ where reflᵢ → ¬a reflᵢ
    dec (x `→ x₁) (y `→ y₁) with dec x y | dec x₁ y₁
    ... | yes reflᵢ | yes reflᵢ = yes reflᵢ
    ... | yes a | no ¬a  = no λ where reflᵢ → ¬a reflᵢ 
    ... | no ¬a | yes a  = no λ where reflᵢ → ¬a reflᵢ
    ... | no ¬a | no ¬a₁ = no λ where reflᵢ → ¬a reflᵢ
    dec `⊤ (y `× y₁) = no (λ ())
    dec `⊤ (y `→ y₁) = no (λ ())
    dec (x `× x₁) `⊤ = no (λ ())
    dec (x `× x₁) (y `→ y₁) = no (λ ())
    dec (x `→ x₁) `⊤ = no (λ ())
    dec (x `→ x₁) (y `× y₁) = no (λ ())

  Tp-hlevel : ∀ {n} → H-Level Tp (2 + n)
  Tp-hlevel = basic-instance 2 (Discrete→is-set Tp-discrete)

Tp-set : is-set Tp
Tp-set = Discrete→is-set Tp-discrete


infixr 25 _⨾_
data Ctx : Type where
  ∅ : Ctx
  _⨾_ : Ctx → Tp → Ctx

instance
  Ctx-discrete : Discrete Ctx
  Ctx-discrete = Discreteᵢ→discrete dec where
    dec : Discreteᵢ Ctx
    dec ∅ ∅ = yes reflᵢ
    dec ∅ (Δ ⨾ x) = no (λ ())
    dec (Γ ⨾ x) ∅ = no (λ ())
    dec (Γ ⨾ x) (Δ ⨾ y) with dec Γ Δ | x ≡ᵢ? y
    ... | yes reflᵢ | yes reflᵢ = yes reflᵢ
    ... | yes a | no ¬a = no λ where reflᵢ → ¬a reflᵢ
    ... | no ¬a | yes a = no λ where reflᵢ → ¬a reflᵢ
    ... | no ¬a | no ¬a₁ = no λ where reflᵢ → ¬a reflᵢ

  Ctx-hlevel : ∀ {n} → H-Level Ctx (2 + n)
  Ctx-hlevel = basic-instance 2 (Discrete→is-set Ctx-discrete)

variable
  Γ Δ Ξ Θ : Ctx
  A B C : Tp

⨾-inj : Γ ⨾ A ≡ Δ ⨾ B → Γ ≡ Δ
⨾-inj {Γ = Γ} p = ap (λ { (Γ ⨾ A) → Γ ; ∅ → Γ }) p

data _∋_ : Ctx → Tp → Type where
  stop : Γ ⨾ A ∋ A
  pop : Γ ∋ A → Γ ⨾ B ∋ A


data _⊢_  : Ctx → Tp → Type 
data Sub  : Ctx → Ctx → Type

variable
  γ δ σ : Sub Γ Δ
  x y : Δ ⊢ A
  f : Δ ⊢ A `→ B
  e : Δ ⨾ A ⊢ B

_!⨾_ : Sub Γ Δ → Γ ⊢ A → Sub Γ (Δ ⨾ A)
!idₛ : Sub Γ Γ
_!∘ₛ_ : Sub Δ Ξ → Sub Γ Δ → Sub Γ Ξ
!πₛ : Sub Δ (Γ ⨾ A) → Sub Δ Γ

data _⊢_  where
  `πₜ : Sub Γ (Δ ⨾ A) → Γ ⊢ A
  `tt : Γ ⊢ `⊤
  `⟨_,_⟩ : Γ ⊢ A → Γ ⊢ B → Γ ⊢ A `× B
  `π₁ : Γ ⊢ A `× B → Γ ⊢ A
  `π₂ : Γ ⊢ A `× B → Γ ⊢ B
  `λ : Γ ⨾ A ⊢ B → Γ ⊢ A `→ B
  `ν : Γ ⊢ A `→ B → Γ ⨾ A ⊢ B  
  _[_] : Γ ⊢ A → Sub Δ Γ → Δ ⊢ A
  [id] : x [ !idₛ ] ≡ x
  [∘] : x [ γ !∘ₛ δ ] ≡ (x [ γ ]) [ δ ]
  `πₜ-β : `πₜ (γ !⨾ x) ≡ x
  [`πₜ] : (`πₜ σ [ γ ]) ≡ `πₜ (σ !∘ₛ γ)
  `ν-β : `ν (`λ e) ≡ e
  [`π₁] : (`π₁ x) [ γ ] ≡ `π₁ (x [ γ ])
  [`π₂] : (`π₂ x) [ γ ] ≡ `π₂ (x [ γ ])
  [`λ] : (`λ e) [ γ ] ≡ `λ (e [ (γ !∘ₛ !πₛ !idₛ) !⨾ (`πₜ !idₛ) ])
  `π₁-β : `π₁ `⟨ x , y ⟩ ≡ x 
  `π₂-β : `π₂ `⟨ x , y ⟩ ≡ y
  `×-η : `⟨ `π₁ x , `π₂ x ⟩ ≡ x
  `⊤-η : `tt ≡ x
  `→-η : `λ (`ν f) ≡ f
  trunc : is-set (Γ ⊢ A)

data Sub where
  ∅ : Sub Γ ∅
  idₛ : Sub Γ Γ 
  _⨾_ : Sub Γ Δ → Γ ⊢ A → Sub Γ (Δ ⨾ A)
  πₛ : Sub Δ (Γ ⨾ A) →  Sub Δ Γ
  _∘ₛ_ : Sub Δ Ξ → Sub Γ Δ → Sub Γ Ξ
  idrₛ : (γ ∘ₛ idₛ) ≡ γ
  idlₛ : (idₛ ∘ₛ γ) ≡ γ
  assocₛ : (γ ∘ₛ (δ ∘ₛ σ)) ≡ ((γ ∘ₛ δ) ∘ₛ σ)
  πₛ-β : πₛ (γ ⨾ x) ≡ γ
  ηₛ : πₛ γ ⨾ `πₜ γ ≡ γ
  πₛ-∘ : (πₛ σ ∘ₛ γ) ≡ πₛ (σ ∘ₛ γ)
  ∅-η : ∅ ≡ γ
  trunc : is-set (Sub Γ Δ)

!idₛ = idₛ
_!∘ₛ_ = _∘ₛ_
_!⨾_ = _⨾_
!πₛ = πₛ


Syntactic : Precategory _ _
Syntactic .Ob = Ctx
Syntactic .Hom = Sub
Syntactic .Hom-set Γ Δ = trunc
Syntactic .id = idₛ
Syntactic ._∘_ = _∘ₛ_
Syntactic .idr _ = idrₛ
Syntactic .idl _ = idlₛ
Syntactic .assoc _ _ _ = assocₛ

private
  module Syn = Cat.Reasoning Syntactic
  module Meta = Cat.Reasoning Cat[ Syntactic ^op , Sets lzero ]
open Meta.Inverses
open PSh-reasoning Syntactic

Tm : Tp → Meta.Ob
Tm A .F₀ Γ = el (Γ ⊢ A) trunc
Tm A .F₁ γ e = e [ γ ]
Tm A .F-id = ext λ _ → [id]
Tm A .F-∘ f g = ext λ _ → [∘]

private
  module Tm A = Functor (Tm A)
  module Y {A} = Yoneda Syntactic (Tm A)

⨾-sem : ∀ {Γ A} → ⟪ Γ ⨾ A ⟫ Meta.≅ ⟪ Γ ⟫ ⟪×⟫ Tm A
⨾-sem = to-natural-iso ni where
  ni : make-natural-iso _ _
  ni .eta Δ γ = πₛ γ , `πₜ γ
  ni .inv Δ (γ , e) = γ ⨾ e
  ni .eta∘inv Δ = ext λ γ x → πₛ-β , `πₜ-β
  ni .inv∘eta Δ = ext λ γ → ηₛ
  ni .natural Δ Ξ γ = ext λ σ → πₛ-∘ , [`πₜ]
  
module ⨾-sem {Γ A} = Meta._≅_ (⨾-sem {Γ} {A})


`⊤-sem : Tm `⊤ Meta.≅ ⟪⊤⟫
`⊤-sem = to-natural-iso ni where
  ni : make-natural-iso _ _
  ni .eta _ _ = lift tt
  ni .inv _ _ = `tt
  ni .eta∘inv _ = refl
  ni .inv∘eta _ = ext λ _ → `⊤-η
  ni .natural _ _ _ = refl

`×-sem : ∀ {A B} → Tm (A `× B) Meta.≅ Tm A ⟪×⟫ Tm B
`×-sem = to-natural-iso ni where
  ni : make-natural-iso _ _
  ni .eta Δ x = `π₁ x , `π₂ x
  ni .inv Δ (x , y) = `⟨ x , y ⟩
  ni .eta∘inv Δ = ext λ x y → `π₁-β , `π₂-β
  ni .inv∘eta Δ = ext λ x → `×-η
  ni .natural Δ Γ γ = ext λ x → [`π₁] , [`π₂]

`→-sem : ∀ {A B} → Tm (A `→ B) Meta.≅ Tm A ⟪→⟫ Tm B
`→-sem {A = A} {B = B} = Meta._Iso⁻¹ (to-natural-iso ni) where
  ni : make-natural-iso _ _
  ni .eta Γ α = `λ (Y.from (α ∘nt ⨾-sem.to))
  ni .inv Γ f = Y.to (`ν f) ∘nt ⨾-sem.from
  ni .eta∘inv Γ = ext λ f → 
    `λ (`ν f [ ⌜ πₛ idₛ ⨾ `πₜ idₛ ⌝ ]) ≡⟨ ap! ηₛ ⟩
    `λ ⌜ `ν f [ idₛ ] ⌝              ≡⟨ ap! [id] ⟩
    `λ (`ν f)                        ≡⟨ `→-η ⟩
     f                                ∎ 
  ni .inv∘eta Γ = funext λ α →
    Y.to ⌜ `ν (`λ (Y.from (α ∘nt ⨾-sem.to))) ⌝ ∘nt ⨾-sem.from ≡⟨ ap! `ν-β ⟩
    ⌜ Y.to (Y.from (α ∘nt ⨾-sem.to)) ⌝ ∘nt ⨾-sem.from ≡⟨ ap! (Y.ε (α ∘nt ⨾-sem.to)) ⟩
    (α ∘nt ⨾-sem.to) ∘nt ⨾-sem.from ≡⟨ trivial! ⟩
    α ∘nt (⨾-sem.to ∘nt ⨾-sem.from) ≡⟨ Meta.elimr ⨾-sem.invl ⟩
    α ∎
  ni .natural Γ Δ γ = ext λ α → 
    `λ (α .η (Γ ⨾ A) (πₛ idₛ , `πₜ idₛ)) [ γ ] ≡⟨ [`λ] ⟩
    `λ (α .η (Γ ⨾ A) (πₛ idₛ , `πₜ idₛ) [ (γ ∘ₛ πₛ idₛ) ⨾ `πₜ idₛ ]) ≡⟨ ap `λ (sym (α .is-natural _ _ _ $ₚ _)) ⟩
    `λ (α .η (Δ ⨾ A) (⌜ πₛ idₛ ∘ₛ ((γ ∘ₛ πₛ idₛ) ⨾ `πₜ idₛ) ⌝ ,  (`πₜ idₛ [ (γ ∘ₛ πₛ idₛ) ⨾ `πₜ idₛ ]))) ≡⟨ ap! lemma₁ ⟩
    `λ (α .η (Δ ⨾ A) ((γ ∘ₛ πₛ idₛ) , ⌜ `πₜ idₛ [ (γ ∘ₛ πₛ idₛ) ⨾ `πₜ idₛ ] ⌝)) ≡⟨ ap! lemma₂ ⟩ 
    `λ (α .η (Δ ⨾ A) ((γ ∘ₛ πₛ idₛ) , `πₜ idₛ)) ∎
    where
      lemma₁ : πₛ idₛ ∘ₛ ((γ ∘ₛ πₛ idₛ) ⨾ `πₜ idₛ) ≡ (γ ∘ₛ πₛ idₛ)
      lemma₁ = 
        πₛ idₛ ∘ₛ ((γ ∘ₛ πₛ idₛ) ⨾ `πₜ idₛ) ≡⟨ πₛ-∘ ⟩ 
        πₛ (idₛ ∘ₛ ((γ ∘ₛ πₛ idₛ) ⨾ `πₜ idₛ)) ≡⟨ ap πₛ idlₛ ⟩ 
        πₛ ((γ ∘ₛ πₛ idₛ) ⨾ `πₜ idₛ) ≡⟨ πₛ-β ⟩ 
        γ ∘ₛ πₛ idₛ ∎

      lemma₂ : `πₜ idₛ [ (γ ∘ₛ πₛ idₛ) ⨾ `πₜ idₛ ] ≡ `πₜ idₛ
      lemma₂ = 
        `πₜ idₛ [ (γ ∘ₛ πₛ idₛ) ⨾ `πₜ idₛ ] ≡⟨ [`πₜ] ⟩
        `πₜ (idₛ ∘ₛ ((γ ∘ₛ πₛ idₛ) ⨾ `πₜ idₛ)) ≡⟨ ap `πₜ idlₛ ⟩
        `πₜ ((γ ∘ₛ πₛ idₛ) ⨾ `πₜ idₛ) ≡⟨ `πₜ-β ⟩
        `πₜ idₛ ∎


Syntactic-model : Strict-model lzero lzero
Syntactic-model .Strict-model.model .Natural-model.Ctx = Syntactic
Syntactic-model .Strict-model.model .Natural-model.Tp = Tp
Syntactic-model .Strict-model.model .Natural-model.Tp-set = Tp-set
Syntactic-model .Strict-model.model .Natural-model.Tm = Tm
Syntactic-model .Strict-model.model .Natural-model._⨾_ = _⨾_
Syntactic-model .Strict-model.model .Natural-model.⨾-sem = ⨾-sem
Syntactic-model .Strict-model.model .Natural-model.`⊤ = `⊤
Syntactic-model .Strict-model.model .Natural-model.`⊤-sem = `⊤-sem
Syntactic-model .Strict-model.model .Natural-model._`×_ = _`×_
Syntactic-model .Strict-model.model .Natural-model.`×-sem = `×-sem
Syntactic-model .Strict-model.model .Natural-model._`→_ = _`→_
Syntactic-model .Strict-model.model .Natural-model.`→-sem = `→-sem
Syntactic-model .Strict-model.model .Natural-model.∅ = ∅
Syntactic-model .Strict-model.model .Natural-model.∅-empty Γ .centre = ∅
Syntactic-model .Strict-model.model .Natural-model.∅-empty Γ .paths _ = ∅-η
Syntactic-model .Strict-model.has-is-strict = hlevel!
  

    
          
```              
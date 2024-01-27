```agda
-- {-# OPTIONS --show-implicit #-}
open import Cat.Prelude hiding (⟪_⟫)
open import Cat.Diagram.Terminal
open import Cat.Semantics.NaturalModel
open import Cat.Functor.Naturality
open import Cat.Functor.Base
open import Cat.Functor.Hom.Representable
open import Data.Dec.Base
open import 1Lab.Reflection.Induction

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

_!⨾_ : Sub Γ Δ → Γ ⊢ A → Sub Γ (Δ ⨾ A)
!idₛ : Sub Γ Γ
_!∘ₛ_ : Sub Δ Ξ → Sub Γ Δ → Sub Γ Ξ
-- wkₛ : Sub Γ Δ → Sub (Γ ⨾ A) (Δ ⨾ A)

data _⊢_  where
  `var : Γ ∋ A → Γ ⊢ A
  `tt : Γ ⊢ `⊤
  `⟨_,_⟩ : Γ ⊢ A → Γ ⊢ B → Γ ⊢ A `× B
  `π₁ : Γ ⊢ A `× B → Γ ⊢ A
  `π₂ : Γ ⊢ A `× B → Γ ⊢ B
  `λ : Γ ⨾ A ⊢ B → Γ ⊢ A `→ B
  _`$_ : Γ ⊢ A `→ B → Γ ⊢ A → Γ ⊢ B  
  _[_] : Γ ⊢ A → Sub Δ Γ → Δ ⊢ A
  [id] : (x : Γ ⊢ A) → x [ !idₛ ] ≡ x
  [∘] : (γ : Sub Δ Ξ) (σ : Sub Γ Δ) (x : Ξ ⊢ A) → x [ γ !∘ₛ σ ] ≡ (x [ γ ]) [ σ ]
  -- `var-∘ : (γ : Sub Δ (Ξ ⨾ A)) (σ : Sub Γ Δ) → `var γ [ σ ] ≡ `var (γ !∘ₛ σ)
  [stop] : (γ : Sub Γ Δ) (x : Γ ⊢ A) → `var stop [ γ !⨾ x ] ≡ x
  [pop] : (γ : Sub Γ Δ) (x : Γ ⊢ A) (n : Δ ∋ B) → `var (pop n) [ γ !⨾ x ] ≡ `var n [ γ ]
  [`π₁] : (γ : Sub Γ Δ) (x : Δ ⊢ A `× B) → (`π₁ x) [ γ ] ≡ `π₁ (x [ γ ])
  [`π₂] : (γ : Sub Γ Δ) (x : Δ ⊢ A `× B) → (`π₂ x) [ γ ] ≡ `π₂ (x [ γ ])
  -- `νβ : (f : Δ ⨾ A ⊢ B) → `ν (`λ f) ≡ f
  -- [`ν] : (γ : Sub Γ Δ) (σ : Sub Ξ Γ) (f : Δ ⊢ A `→ B) (x : Ξ ⊢ A) → `ν f [ (γ !∘ₛ σ) !⨾ x ] ≡ `ν (f [ γ ]) [ σ !⨾ x ]
  `π₁β : (x : Δ ⊢ A) (y : Δ ⊢ B) → `π₁ `⟨ x , y ⟩ ≡ x 
  `π₂β : (x : Δ ⊢ A) (y : Δ ⊢ B) → `π₂ `⟨ x , y ⟩ ≡ y
  `×-η : (x : Γ ⊢ A `× B) → `⟨ `π₁ x , `π₂ x ⟩ ≡ x
  `⊤-η : (x : Γ ⊢ `⊤) → `tt ≡ x
  -- `→-η : (f : Δ ⊢ A `→ B) → `λ (`ν f) ≡ f
  trunc : is-set (Γ ⊢ A)

data Sub where
  ∅ : Sub Γ ∅
  idₛ : Sub Γ Γ 
  _⨾_ : Sub Γ Δ → Γ ⊢ A → Sub Γ (Δ ⨾ A)
  π : Sub Δ (Γ ⨾ A) →  Sub Δ Γ
  _∘ₛ_ : Sub Δ Ξ → Sub Γ Δ → Sub Γ Ξ
  idrₛ : (f : Sub Γ Δ) → (f ∘ₛ idₛ) ≡ f
  idlₛ : (f : Sub Γ Δ) → (idₛ ∘ₛ f) ≡ f
  assocₛ : (f : Sub Ξ Θ) (g : Sub Δ Ξ) (h : Sub Γ Δ) → (f ∘ₛ (g ∘ₛ h)) ≡ ((f ∘ₛ g) ∘ₛ h)
  π-∘ : (γ : Sub Γ Δ) (σ : Sub Δ (Ξ ⨾ A)) → π σ ∘ₛ γ ≡ π (σ ∘ₛ γ)
  π-⨾ : (γ : Sub Γ Δ) (x : Γ ⊢ A) → π (γ ⨾ x) ≡ γ
  ηₛ : (γ : Sub Γ (Δ ⨾ A)) → π γ ⨾ (`var stop [ γ ]) ≡ γ
  η-∅ : (γ : Sub Γ ∅) → ∅ ≡ γ
  ⨾-∘ : (γ : Sub Γ Δ) (σ : Sub Ξ Γ) (x : Γ ⊢ A) → ((γ ⨾ x) ∘ₛ σ) ≡ (γ ∘ₛ σ) ⨾ (x [ σ ]) 
  trunc : is-set (Sub Γ Δ)

!idₛ = idₛ
_!∘ₛ_ = _∘ₛ_
_!⨾_ = _⨾_


-- unquoteDecl Tm-elim = make-elim-n 2 Tm-elim (quote _⊢_)
-- unquoteDecl Sub-elim = make-elim-n 2 Sub-elim (quote Sub)


Syntactic : Precategory _ _
Syntactic .Ob = Ctx
Syntactic .Hom = Sub
Syntactic .Hom-set Γ Δ = trunc
Syntactic .id = idₛ
Syntactic ._∘_ = _∘ₛ_
Syntactic .idr = idrₛ
Syntactic .idl = idlₛ
Syntactic .assoc = assocₛ

module Syn = Cat.Reasoning Syntactic
module Meta = Cat.Reasoning Cat[ Syntactic ^op , Sets lzero ]
open Meta.Inverses
open PSh-reasoning Syntactic

Tm : Tp → Meta.Ob
Tm A .F₀ Γ = el (Γ ⊢ A) trunc
Tm A .F₁ γ e = e [ γ ]
Tm A .F-id = ext [id]
Tm A .F-∘ f g = ext ([∘] g f)

module Tm A = Functor (Tm A)

-- I think means we have lifts??
⊢⟪_⟫ : Γ ⊢ A → ⟪ Γ ⟫ => Tm A
⊢⟪ f ⟫ = NT (λ Δ γ → f [ γ ]) λ Δ Ξ δ → ext λ δ → Tm.F-∘ _ _ _ #ₚ f

⟪_⟫⊢ : ⟪ Γ ⟫ => Tm A → Γ ⊢ A
⟪ φ ⟫⊢ = φ .η _ idₛ


⨾-sem : ∀ {Γ A} → ⟪ Γ ⨾ A ⟫ Meta.≅ ⟪ Γ ⟫ ⟪×⟫ Tm A
⨾-sem = to-natural-iso ni where
  ni : make-natural-iso _ _
  ni .eta Δ γ = π γ , ((`var stop) [ γ ])
  ni .inv Δ (γ , e) = γ ⨾ e
  ni .eta∘inv Δ = ext λ γ x → π-⨾ _ _ , [stop] _ _
  ni .inv∘eta Δ = ext λ γ → ηₛ _
  ni .natural Δ Ξ γ = ext λ σ → π-∘ _ _ , sym ([∘] _ _ _)

`⊤-sem : Tm `⊤ Meta.≅ ⟪⊤⟫
`⊤-sem = to-natural-iso ni where
  ni : make-natural-iso _ _
  ni .eta _ _ = lift tt
  ni .inv _ _ = `tt
  ni .eta∘inv _ = refl
  ni .inv∘eta _ = ext `⊤-η
  ni .natural _ _ _ = refl

`×-sem : ∀ {A B} → Tm (A `× B) Meta.≅ Tm A ⟪×⟫ Tm B
`×-sem = to-natural-iso ni where
  ni : make-natural-iso _ _
  ni .eta Δ x = `π₁ x , `π₂ x
  ni .inv Δ (x , y) = `⟨ x , y ⟩
  ni .eta∘inv Δ = ext λ x y → `π₁β _ _ , `π₂β _ _
  ni .inv∘eta Δ = ext λ x → `×-η _
  ni .natural Δ Γ γ = ext λ x → [`π₁] _ _ , [`π₂] _ _

`→-sem : ∀ {A B} → Tm (A `→ B) Meta.≅ Tm A ⟪→⟫ Tm B
`→-sem {A = A} = to-natural-iso ni where
  ni : make-natural-iso _ _
  ni .eta = {!   !}
  ni .inv = {!   !}
  ni .eta∘inv = {!   !}
  ni .inv∘eta = {!   !}
  ni .natural = {!   !}
  -- ni .eta Δ f = ⊢⟪ `ν f ⟫ ∘nt ⨾-sem .Meta.from
  -- ni .inv Δ φ = `λ ⟪ φ ∘nt ⨾-sem .Meta.to ⟫⊢
  -- ni .eta∘inv Δ = ext λ φ Γ γ x →
  --   ⌜ `ν (`λ (φ .η (Δ ⨾ A) (π idₛ , `var idₛ))) ⌝ [ γ ⨾ x ] ≡⟨ ap! (`νβ _) ⟩
  --   φ .η (Δ ⨾ A) (π idₛ , `var idₛ) [ γ ⨾ x ]               ≡˘⟨ φ .is-natural _ _ (γ ⨾ x) #ₚ (π idₛ , `var idₛ) ⟩
  --   φ .η Γ ⌜ π idₛ ∘ₛ (γ ⨾ x) , `var idₛ [ γ ⨾ x ] ⌝        ≡⟨ ap! (ext (π-∘ _ _ , `var-∘ _ _)) ⟩
  --   φ .η Γ (π ⌜ idₛ ∘ₛ (γ ⨾ x) ⌝ , `var ⌜ idₛ ∘ₛ (γ ⨾ x) ⌝) ≡⟨ ap! (idlₛ _) ⟩
  --   φ .η Γ ⌜ π (γ ⨾ x) , `var (γ ⨾ x) ⌝                    ≡⟨ ap! (ext (π-⨾ _ _ , `var-⨾ _ _)) ⟩
  --   φ .η Γ (γ , x)                                        ∎
  -- ni .inv∘eta Δ = ext λ f →
  --   `λ (`ν f [ ⌜ π idₛ ⨾ `var idₛ ⌝ ]) ≡⟨ ap! (ηₛ _) ⟩
  --   `λ ⌜ `ν f [ idₛ ] ⌝               ≡⟨ ap! ([id] _) ⟩
  --   `λ (`ν f)                         ≡⟨ `→-η _ ⟩
  --   f                                 ∎ 
  -- ni .natural Δ Γ γ = ext λ f Ξ σ x → {!   !}
  -- [`ν] _ _ _ _

Syntactic-model : Natural-model lzero lzero
Syntactic-model .Natural-model.Ctx = Syntactic
Syntactic-model .Natural-model.Tp = Tp
Syntactic-model .Natural-model.Tp-set = Tp-set
Syntactic-model .Natural-model.Tm = Tm
Syntactic-model .Natural-model.∅ = ∅
Syntactic-model .Natural-model.∅-empty Γ .centre = ∅
Syntactic-model .Natural-model.∅-empty Γ .paths = η-∅
Syntactic-model .Natural-model._⨾_ = _⨾_
Syntactic-model .Natural-model.⨾-sem = ⨾-sem
Syntactic-model .Natural-model.`⊤ = `⊤
Syntactic-model .Natural-model.`⊤-sem = `⊤-sem
Syntactic-model .Natural-model._`×_ = _`×_
Syntactic-model .Natural-model.`×-sem = `×-sem
Syntactic-model .Natural-model._`→_ = _`→_
Syntactic-model .Natural-model.`→-sem = `→-sem
      
  
        
```     
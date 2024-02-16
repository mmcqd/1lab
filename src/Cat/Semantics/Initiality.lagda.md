```agda

open import Cat.Prelude
open import Cat.Univalent
open import Cat.Semantics.NaturalModel
open import Cat.Semantics.StrictModels
open import Cat.Semantics.Syntax
open import Cat.Functor.Base
open import Cat.Functor.Adjoint
open import Cat.Diagram.Initial
open import Cat.Morphism
open import Cat.Instances.Shape.Terminal
open import Cat.Functor.Hom
import Cat.Strict.Reasoning

open Initial
open Precategory
open Functor
open _=>_
open _⊣_

module Cat.Semantics.Initiality where

module ⟦⟧ (M : Strict-model lzero lzero) where
  private module M = Strict-model M
    
  ⟦_⟧ᵗ : Tp → M.Tp
  ⟦ `⊤ ⟧ᵗ = M.`⊤
  ⟦ A `× B ⟧ᵗ = ⟦ A ⟧ᵗ M.`× ⟦ B ⟧ᵗ
  ⟦ A `→ B ⟧ᵗ = ⟦ A ⟧ᵗ M.`→ ⟦ B ⟧ᵗ

  ⟦_⟧ᶜ : Ctx → M.Ob
  ⟦ ∅ ⟧ᶜ = M.∅
  ⟦ Γ ⨾ A ⟧ᶜ = ⟦ Γ ⟧ᶜ M.⨾ ⟦ A ⟧ᵗ

  ⟦_⟧ˢ : ∀ {Γ Δ} → Sub Γ Δ → M.Hom ⟦ Γ ⟧ᶜ ⟦ Δ ⟧ᶜ
  ⟦_⟧ᵉ : ∀ {Γ A} → Γ ⊢ A → ⟦ Γ ⟧ᶜ M.⊢ ⟦ A ⟧ᵗ


  ⟦ ∅ ⟧ˢ = M.∅.!
  ⟦ idₛ ⟧ˢ = M.idₛ
  ⟦ γ ⨾ x ⟧ˢ = ⟦ γ ⟧ˢ M.⨾ₛ ⟦ x ⟧ᵉ
  ⟦ πₛ γ ⟧ˢ = M.πₛ ⟦ γ ⟧ˢ
  ⟦ γ ∘ₛ δ ⟧ˢ = ⟦ γ ⟧ˢ M.∘ₛ ⟦ δ ⟧ˢ
  ⟦ idrₛ {γ = γ} i ⟧ˢ = M.idrₛ {γ = ⟦ γ ⟧ˢ}  i
  ⟦ idlₛ {γ = γ} i ⟧ˢ = M.idlₛ {γ = ⟦ γ ⟧ˢ}  i
  ⟦ assocₛ {γ = γ} {δ = δ} {σ = σ} i ⟧ˢ = M.assocₛ {γ = ⟦ γ ⟧ˢ} {δ = ⟦ δ ⟧ˢ} {σ = ⟦ σ ⟧ˢ} i
  ⟦ πₛ-β {γ = γ} {x = x} i ⟧ˢ = M.πₛ-β {γ = ⟦ γ ⟧ˢ} {x = ⟦ x ⟧ᵉ} i
  ⟦ ηₛ {γ = γ} i ⟧ˢ = M.ηₛ {γ = ⟦ γ ⟧ˢ} i
  ⟦ πₛ-∘ {σ = σ} {γ = γ} i ⟧ˢ = M.πₛ-∘ {σ = ⟦ σ ⟧ˢ} {γ = ⟦ γ ⟧ˢ} i
  ⟦ ∅-η {γ = γ} i ⟧ˢ = M.∅-η {γ = ⟦ γ ⟧ˢ} i
  ⟦ trunc γ δ x y i j ⟧ˢ = M.Hom-set _ _ ⟦ γ ⟧ˢ ⟦ δ ⟧ˢ (λ i → ⟦ x i ⟧ˢ) (λ i → ⟦ y i ⟧ˢ) i j

  ⟦ `πₜ γ ⟧ᵉ = M.`πₜ ⟦ γ ⟧ˢ
  ⟦ `tt ⟧ᵉ = M.`tt
  ⟦ `⟨ x , y ⟩ ⟧ᵉ = M.`⟨ ⟦ x ⟧ᵉ , ⟦ y ⟧ᵉ ⟩
  ⟦ `π₁ x ⟧ᵉ = M.`π₁ ⟦ x ⟧ᵉ
  ⟦ `π₂ x ⟧ᵉ = M.`π₂ ⟦ x ⟧ᵉ
  ⟦ `λ x ⟧ᵉ = M.`λ ⟦ x ⟧ᵉ
  ⟦ `ν x ⟧ᵉ = M.`ν ⟦ x ⟧ᵉ
  ⟦ x [ γ ] ⟧ᵉ = ⟦ x ⟧ᵉ M.[ ⟦ γ ⟧ˢ ]
  ⟦ [id] {x = x} i ⟧ᵉ = M.[id] {x = ⟦ x ⟧ᵉ} i
  ⟦ [∘] {x = x} {γ = γ} {δ = δ} i ⟧ᵉ = M.[∘] {x = ⟦ x ⟧ᵉ} {γ = ⟦ γ ⟧ˢ} {δ = ⟦ δ ⟧ˢ} i
  ⟦ `πₜ-β {γ = γ} {x = x} i ⟧ᵉ = M.`πₜ-β {γ = ⟦ γ ⟧ˢ} {x = ⟦ x ⟧ᵉ} i
  ⟦ [`πₜ] {σ = σ} {γ = γ} i ⟧ᵉ = M.[`πₜ] {σ = ⟦ σ ⟧ˢ} {γ = ⟦ γ ⟧ˢ} i
  ⟦ `ν-β {e = e} i ⟧ᵉ = M.`ν-β {e = ⟦ e ⟧ᵉ} i
  ⟦ [`π₁] {x = x} {γ = γ} i ⟧ᵉ = M.[`π₁] {x = ⟦ x ⟧ᵉ} {γ = ⟦ γ ⟧ˢ} i
  ⟦ [`π₂] {x = x} {γ = γ} i ⟧ᵉ = M.[`π₂] {x = ⟦ x ⟧ᵉ} {γ = ⟦ γ ⟧ˢ} i
  ⟦ [`λ] {e = e} {γ = γ} i ⟧ᵉ = M.[`λ] {e = ⟦ e ⟧ᵉ} {γ = ⟦ γ ⟧ˢ} i
  ⟦ `π₁-β {x = x} {y = y} i ⟧ᵉ = M.`π₁-β {x = ⟦ x ⟧ᵉ} {y = ⟦ y ⟧ᵉ} i
  ⟦ `π₂-β {x = x} {y = y} i ⟧ᵉ = M.`π₂-β {x = ⟦ x ⟧ᵉ} {y = ⟦ y ⟧ᵉ} i
  ⟦ `×-η {x = x} i ⟧ᵉ = M.`×-η {x = ⟦ x ⟧ᵉ} i
  ⟦ `⊤-η {x = x} i ⟧ᵉ = M.`⊤-η {x = ⟦ x ⟧ᵉ} i
  ⟦ `→-η {f = f} i ⟧ᵉ = M.`→-η {f = ⟦ f ⟧ᵉ} i
  ⟦ trunc x x₁ x₂ y i i₁ ⟧ᵉ = M.tm-set ⟦ x ⟧ᵉ ⟦ x₁ ⟧ᵉ (λ i → ⟦ x₂ i ⟧ᵉ) (λ i → ⟦ y i ⟧ᵉ) i i₁


  Ctx-hom : Functor Syntactic M.Ctx
  Ctx-hom .F₀ = ⟦_⟧ᶜ
  Ctx-hom .F₁ = ⟦_⟧ˢ
  Ctx-hom .F-id = refl
  Ctx-hom .F-∘ _ _ = refl


  Syntax-hom : Strict-model-hom Syntactic-model M
  Syntax-hom .Strict-model-hom.F = Ctx-hom
  Syntax-hom .Strict-model-hom.F-tp = ⟦_⟧ᵗ
  Syntax-hom .Strict-model-hom.F-tm A .η Γ = ⟦_⟧ᵉ
  Syntax-hom .Strict-model-hom.F-tm A .is-natural Γ Δ γ = refl
  Syntax-hom .Strict-model-hom.pres-∅ = refl
  Syntax-hom .Strict-model-hom.pres-⨾ = refl
  Syntax-hom .Strict-model-hom.pres-`⊤ = refl
  Syntax-hom .Strict-model-hom.pres-`× = refl
  Syntax-hom .Strict-model-hom.pres-`→ = refl
 
Initiality : Initial (Strict-models lzero lzero)
Initiality .bot = Syntactic-model
Initiality .has⊥ M .centre = ⟦⟧.Syntax-hom M
Initiality .has⊥ M .paths H = Strict-model-hom-path {! Func  !} {!   !} {!   !}
  where
    open ⟦⟧ M
    module M = Strict-model M
    module S = Strict-model-hom Syntax-hom
    module H = Strict-model-hom H
    module Syn = Strict-model Syntactic-model
    module Y = Yoneda M.Ctx

    open Cat.Strict.Reasoning M.Ctx hlevel!

    tp : ∀ A → H.F-tp A ≡ ⟦ A ⟧ᵗ
    tp `⊤ = H.pres-`⊤
    tp (A `× B) = H.pres-`× ∙ (ap₂ M._`×_ (tp A) (tp B))
    tp (A `→ B) = H.pres-`→ ∙ (ap₂ M._`→_ (tp A) (tp B))

    ctx : ∀ Γ → H.₀ Γ ≡ ⟦ Γ ⟧ᶜ
    ctx ∅ = H.pres-∅
    ctx (Γ ⨾ x) = H.pres-⨾ ∙ ap₂ M._⨾_ (ctx Γ) (tp x)

    

    sub : ∀ {Γ Δ} (γ : Sub Γ Δ) → cast-hom (ctx Γ) (ctx Δ) (H.₁ γ) ≡ ⟦ γ ⟧ˢ
    sub ∅ = sym (M.∅.has⊤ _ .paths _)
    sub {Γ} {.Γ} idₛ = 
      cast-hom (ctx Γ) (ctx Γ) ⌜ H.₁ idₛ ⌝ ≡⟨ ap! H.F-id ⟩
      cast-hom (ctx Γ) (ctx Γ) M.id ≡⟨ cast-id _ ⟩
      M.id ∎
    sub (γ ⨾ x) = {! H  !}
      -- sym $ 
      -- M.⨾-sem .from .η _ (⟦ γ ⟧ˢ , ⟦ x ⟧ᵉ) ≡⟨ {!   !} ⟩
      -- {!   !}
    sub (πₛ γ) = {!   !}
    sub (γ ∘ₛ γ₁) = {!   !}
    sub (idrₛ i) = {!   !}
    sub (idlₛ i) = {!   !}
    sub (assocₛ i) = {!   !}
    sub (πₛ-β i) = {!   !}
    sub (ηₛ i) = {!   !}
    sub (πₛ-∘ i) = {!   !}
    sub (∅-η i) = {!   !}
    sub (trunc γ γ₁ x y i i₁) = {!   !}
    --  cast-cod (ctx _) M.id M.∘ (H.₁ γ M.∘ ⌜ cast-dom (ctx _) M.id ⌝) ≡˘⟨ ap¡ (cast-id-swap _) ⟩
    --  ⌜ cast-cod (ctx _) M.id ⌝ M.∘ (H.₁ γ M.∘ cast-cod (sym (ctx _)) M.id) ≡⟨ ap! (cast-id-swap _) ⟩
    --  cast-dom (sym (ctx _)) {!   !} M.∘ (H.₁ γ M.∘ cast-cod (sym (ctx _)) M.id) ≡⟨ {!   !} ⟩
    --   {!   !}


      -- lemma : ∀ {Γ Δ} (γ : Sub Γ Δ) → transport (λ i → M.Ctx.Hom ⟦ Δ ⟧ᶜ (ctx Δ i)) M.Ctx.id M.Ctx.∘ ⟦ γ ⟧ˢ M.Ctx.∘ transport (λ i → M.Ctx.Hom (ctx Γ i) ⟦ Γ ⟧ᶜ) M.Ctx.id ≡ H.₁ γ
      -- lemma ∅ = {! transport (λ i → M.Ctx.Hom ⟦ ∅ ⟧ᶜ (sym H.pres-∅ i)) M.Ctx.id !}
      -- lemma idₛ = {!   !}
      -- lemma (γ ⨾ x) = {!   !}
      -- lemma (πₛ γ) = {!   !}
      -- lemma (γ ∘ₛ γ₁) = {!   !}
      -- lemma (idrₛ i) = {!   !}
      -- lemma (idlₛ i) = {!   !}
      -- lemma (assocₛ i) = {!   !}
      -- lemma (πₛ-β i) = {!   !}
      -- lemma (ηₛ i) = {!   !}
      -- lemma (πₛ-∘ i) = {!   !}
      -- lemma (∅-η i) = {!   !}
      -- lemma (trunc γ γ₁ x y i i₁) = {!   !}
        -- ⌜ transport (λ i → M.Ctx.Hom ⟦ Δ ⟧ᶜ (ctx Δ i)) M.Ctx.id ⌝ M.Ctx.∘ ⟦ γ ⟧ˢ M.Ctx.∘ transport (λ i → M.Ctx.Hom (ctx Γ i) ⟦ Γ ⟧ᶜ) M.Ctx.id ≡⟨ ap! (Hom-transport-id M.Ctx refl (ctx _)) ⟩
        -- {! transp (λ i → M.Ctx.Hom ⟦ Δ ⟧ᶜ (ctx Δ i)) i0 M.Ctx.id M.Ctx.∘\ntransp (λ i → M.Ctx.Hom ⟦ Δ ⟧ᶜ ⟦ Δ ⟧ᶜ) i0 M.Ctx.id !} M.Ctx.∘ ⟦ γ ⟧ˢ M.Ctx.∘ transport (λ i → M.Ctx.Hom (ctx Γ i) ⟦ Γ ⟧ᶜ) M.Ctx.id ≡⟨ {!   !} ⟩ 
        -- {!   !}
      
    -- f-path : S.F ≡ H.Fc
    -- f-path = Functor-path ctx {! H.F-tm  !}
    
```      
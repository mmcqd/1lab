```agda

open import Cat.Prelude
open import Cat.Semantics.NaturalModel
open import Cat.Semantics.StrictModels
open import Cat.Semantics.Syntax
open import Cat.Diagram.Initial
open import Cat.Morphism

open Initial
open Precategory
open Functor
open _=>_

module Cat.Semantics.Initiality (M : Natural-model lzero lzero) where
  

module M = Natural-model M
  
⟦_⟧ᵗ : Tp → M.Tp
⟦ `⊤ ⟧ᵗ = M.`⊤
⟦ A `× B ⟧ᵗ = ⟦ A ⟧ᵗ M.`× ⟦ B ⟧ᵗ
⟦ A `→ B ⟧ᵗ = ⟦ A ⟧ᵗ M.`→ ⟦ B ⟧ᵗ

⟦_⟧ᶜ : Ctx → M.Ob
⟦ ∅ ⟧ᶜ = M.∅
⟦ Γ ⨾ A ⟧ᶜ = ⟦ Γ ⟧ᶜ M.⨾ ⟦ A ⟧ᵗ

⟦_⟧ˢ : ∀ {Γ Δ} → Sub Γ Δ → M.Hom ⟦ Γ ⟧ᶜ ⟦ Δ ⟧ᶜ
⟦_⟧ᵉ : ∀ {Γ A} → Γ ⊢ A → ⟦ Γ ⟧ᶜ M.⊢ ⟦ A ⟧ᵗ




⟦ ∅ ⟧ˢ = M.∅-empty _ .centre
⟦ idₛ ⟧ˢ = M.id
⟦ γ ⨾ x ⟧ˢ = M.⨾-sem .from .η _ (⟦ γ ⟧ˢ , ⟦ x ⟧ᵉ)
⟦ π γ ⟧ˢ = M.⨾-sem .to .η _ ⟦ γ ⟧ˢ .fst
⟦ γ ∘ₛ σ ⟧ˢ = ⟦ γ ⟧ˢ M.∘ ⟦ σ ⟧ˢ
⟦ idrₛ x i ⟧ˢ = M.idr ⟦ x ⟧ˢ i
⟦ idlₛ x i ⟧ˢ = M.idl ⟦ x ⟧ˢ i
⟦ assocₛ x x₁ x₂ i ⟧ˢ = M.assoc ⟦ x ⟧ˢ ⟦ x₁ ⟧ˢ ⟦ x₂ ⟧ˢ i
⟦ π-∘ x x₁ i ⟧ˢ = M.π-∘ ⟦ x ⟧ˢ ⟦ x₁ ⟧ˢ i
⟦ π-⨾ x x₁ i ⟧ˢ = M.π-⨾ ⟦ x ⟧ˢ ⟦ x₁ ⟧ᵉ i
⟦ ηₛ x i ⟧ˢ = {!  M.ηₛ ⟦ x ⟧ˢ i  !}
⟦ η-∅ x i ⟧ˢ = M.η-∅ ⟦ x ⟧ˢ i
⟦ trunc x x₁ x₂ y i i₁ ⟧ˢ = M.Hom-set _ _ ⟦ x ⟧ˢ ⟦ x₁ ⟧ˢ (λ i → ⟦ x₂ i ⟧ˢ) (λ i → ⟦ y i ⟧ˢ) i i₁

⟦ `var γ ⟧ᵉ = M.`var ⟦ γ ⟧ˢ
⟦ `tt ⟧ᵉ = {!   !}
⟦ `⟨ x , x₁ ⟩ ⟧ᵉ = {!   !}
⟦ `π₁ x ⟧ᵉ = {!   !}
⟦ `π₂ x ⟧ᵉ = {!   !}
⟦ `λ x ⟧ᵉ = {!   !}
⟦ `ν x ⟧ᵉ = {!   !}
⟦ x [ x₁ ] ⟧ᵉ = {!   !}
⟦ [id] x i ⟧ᵉ = {!   !}
⟦ [∘] γ σ x i ⟧ᵉ = {!   !}
⟦ `var-∘ γ σ i ⟧ᵉ = {!   !}
⟦ `var-⨾ γ x i ⟧ᵉ = {!   !}
⟦ [`π₁] γ x i ⟧ᵉ = {!   !}
⟦ [`π₂] γ x i ⟧ᵉ = {!   !}
⟦ `νβ x i ⟧ᵉ = {!   !}
⟦ [`ν] γ σ x x₁ i ⟧ᵉ = {!   !}
⟦ `π₁β x x₁ i ⟧ᵉ = {!   !}
⟦ `π₂β x x₁ i ⟧ᵉ = {!   !}
⟦ `×-η x i ⟧ᵉ = {!   !}
⟦ `⊤-η x i ⟧ᵉ = {!   !}
⟦ `→-η x i ⟧ᵉ = {!   !}
⟦ trunc x x₁ x₂ y i i₁ ⟧ᵉ = {!   !}

Ctx-hom : (M : Natural-model lzero lzero) → Functor Syntactic M.Ctx
Ctx-hom M .F₀ = ⟦_⟧ᶜ
Ctx-hom M .F₁ = {!   !}
Ctx-hom M .F-id = {!   !}
Ctx-hom M .F-∘ = {!   !}


-- Syntax-hom : (M : Natural-model lzero lzero) → Model-hom Syntactic-model M
-- Syntax-hom M .Model-hom.F = {!   !}
-- Syntax-hom M .Model-hom.F-tp = {!   !}
-- Syntax-hom M .Model-hom.F-tm = {!   !}
-- Syntax-hom M .Model-hom.pres-⨾ = {!   !}
-- Syntax-hom M .Model-hom.pres-`⊤ = {!   !}
-- Syntax-hom M .Model-hom.pres-`× = {!   !}
-- Syntax-hom M .Model-hom.pres-`→ = {!   !}
 
-- Initiality : Initial (Strict-models lzero lzero)
-- Initiality .bot = Syntactic-model , hlevel!
-- Initiality .has⊥ (M , M-strict) .centre = {!   !}
-- Initiality .has⊥ (M , M-strict) .paths = {!   !}
   
```
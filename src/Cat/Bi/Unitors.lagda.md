```agda

open import Cat.Prelude
open import Cat.Bi.Base
open import Cat.Bi.Instances.Opposite

import Cat.Reasoning as Cr
import Cat.Bi.Morphism as Bm

module Cat.Bi.Unitors {o oh ℓh} (B : Prebicategory o oh ℓh) where

open Functor
open Prebicategory-Hom-Reasoning B

private
  module B^op = Prebicategory (B ^Op)
  module B^co = Prebicategory (B ^Co)
  module B^coop = Prebicategory (B ^Coop)

open Bm B

variable
  a b c d : Ob
  f g h k : a ↦ b
  β γ : f ⇒ g


⊗-▶ : (f ⊗ g) ▶ β ≡ α← _ _ _ ∘ f ▶ (g ▶ β) ∘ α→ _ _ _
⊗-▶ {f = f} {g = g} {β = β} = 
  Hom.has-section→epic (Hom.iso→from-has-section (α≅ _ _ _)) _ _ $
  (⌜ Hom.id ⌝ ◆ β) ∘ α← _ _ _                    ≡˘⟨ ap¡ compose.F-id ⟩
  ((Hom.id ◆ Hom.id) ◆ β) ∘ α← _ _ _             ≡˘⟨ α←nat _ _ _ ⟩
  α← _ _ _ ∘ (Hom.id ◆ (Hom.id ◆ β))             ≡⟨⟩
  α← _ _ _ ∘ f ▶ (g ▶ β)                         ≡˘⟨ Hom.pullr (Hom.cancelr (α≅.invl _ _ _)) ⟩
  (α← _ _ _ ∘ f ▶ (g ▶ β) ∘ α→ _ _ _) ∘ α← _ _ _ ∎

▶-⊗ : f ▶ (g ▶ β) ≡ α→ _ _ _ ∘ (f ⊗ g) ▶ β ∘ α← _ _ _
▶-⊗ {f = f} {g = g} {β = β} = 
  Hom.pre-invl.to (Hom.iso→invertible (α≅ _ _ _)) $
  Hom.post-invr.from (Hom.iso→invertible (α≅ _ _ _)) $
  sym (⊗-▶ ∙ Hom.assoc _ _ _)

⊗-◀ : β ◀ (f ⊗ g) ≡ α→ _ _ _ ∘ (β ◀ f) ◀ g ∘ α← _ _ _
⊗-◀ {β = β} {f = f} {g = g} =
  Hom.has-section→epic (Hom.iso→to-has-section (α≅ _ _ _)) _ _ $
  (β ◆ ⌜ Hom.id ⌝) ∘ α→ _ _ _                    ≡˘⟨ ap¡ compose.F-id ⟩
  (β ◆ (Hom.id ◆ Hom.id)) ∘ α→ _ _ _             ≡˘⟨ α→nat _ _ _ ⟩
  α→ _ _ _ ∘ ((β ◆ Hom.id) ◆ Hom.id)             ≡⟨⟩
  α→ _ _ _ ∘ (β ◀ f) ◀ g                         ≡˘⟨ Hom.pullr (Hom.cancelr (α≅.invr _ _ _)) ⟩
  (α→ _ _ _ ∘ (β ◀ f) ◀ g ∘ α← _ _ _) ∘ α→ _ _ _ ∎

◀-⊗ : (β ◀ f) ◀ g ≡ α← _ _ _ ∘ β ◀ (f ⊗ g) ∘ α→ _ _ _
◀-⊗ {β = β}  {f = f} {g = g} =
  Hom.pre-invl.to (Hom.iso→invertible (α≅ _ _ _ Hom.Iso⁻¹)) $
  Hom.post-invr.from (Hom.iso→invertible (α≅ _ _ _ Hom.Iso⁻¹)) $
  sym (⊗-◀ ∙ Hom.assoc _ _ _)

swap-▶◀ : (f ▶ β) ◀ g ≡ α← _ _ _ ∘ f ▶ (β ◀ g) ∘ α→ _ _ _
swap-▶◀ {f = f} {β = β} {g = g} = 
  Hom.has-section→epic (Hom.iso→from-has-section (α≅ _ _ _)) _ _ $
  ((Hom.id ◆ β) ◆ Hom.id) ∘ α← _ _ _ ≡˘⟨ α←nat _ _ _ ⟩
  α← _ _ _ ∘ ((Hom.id ◆ (β ◆ Hom.id))) ≡˘⟨ Hom.pullr (Hom.cancelr (α≅.invl _ _ _)) ⟩ 
  (α← _ _ _ ∘ f ▶ (β ◀ g) ∘ α→ _ _ _) ∘ α← _ _ _  ∎

ρ←◀ : ρ← f ◀ id ≡ ρ← (f ⊗ id)
ρ←◀ {f = f} = 
  Hom.has-section→epic (Hom.iso→to-has-section (ρ≅ _)) _ _ $
  ρ← f ◀ id ∘ ρ→ (f ⊗ id)   ≡˘⟨ ρ→nat _ ⟩ 
  ρ→ f ∘ ρ← f               ≡⟨ ρ≅.invl _ ⟩
  Hom.id                    ≡˘⟨ ρ≅.invr _ ⟩ 
  ρ← (f ⊗ id) ∘ ρ→ (f ⊗ id) ∎


▶λ← : id ▶ λ← f ≡ λ← (id ⊗ f)
▶λ← = 
  Hom.has-section→epic (Hom.iso→to-has-section (λ≅ _)) _ _ $
  (id ▶ λ← _) ∘ λ→ _ ≡˘⟨ λ→nat _ ⟩
  λ→ _ ∘ λ← _        ≡⟨ λ≅.invl _ ⟩
  Hom.id             ≡˘⟨ λ≅.invr _ ⟩
  λ← _ ∘ λ→ _        ∎


id-◀-monic : β ◀ id ≡ γ ◀ id → β ≡ γ
id-◀-monic {β = β} {γ = γ} p = 
  Hom.has-retract→monic (Hom.iso→to-has-retract (ρ≅ _)) _ _ $
  ρ→ _ ∘ β        ≡⟨ ρ→nat _ ⟩ 
  (β ◀ id) ∘ ρ→ _ ≡⟨ p Hom.⟩∘⟨refl ⟩
  (γ ◀ id) ∘ ρ→ _ ≡˘⟨ ρ→nat _ ⟩
  ρ→ _ ∘ γ        ∎ 


id-▶-monic : id ▶ β ≡ id ▶ γ → β ≡ γ
id-▶-monic {β = β} {γ = γ} p = 
  Hom.has-retract→monic (Hom.iso→to-has-retract (λ≅ _)) _ _ $
  λ→ _ ∘ β        ≡⟨ λ→nat _ ⟩
  (id ▶ β) ∘ λ→ _ ≡⟨ p Hom.⟩∘⟨refl ⟩
  (id ▶ γ) ∘ λ→ _ ≡˘⟨ λ→nat _ ⟩ 
  λ→ _ ∘ γ        ∎

-- lemma : (f ▶ (ρ← _ ◀ id)) ∘ (f ▶ α← _ _ _) ≡ f ▶ (id  ▶ λ← _)
-- lemma {f = f} = 
--   (f ▶ (ρ← _ ◀ id)) ∘ (f ▶ α← _ _ _) ≡˘⟨ postaction B f .F-∘ _ _ ⟩
--   f ▶ (ρ← _ ◀ id ∘ α← _ _ _) ≡⟨ ap (f ▶_) (triangle _ _) ⟩
--   f ▶ (id  ▶ λ← _) ∎ 





▶ρ← : f ▶ ρ← id ≡ ρ← (f ⊗ id) ∘ α← _ _ _ 
▶ρ← {f = f} = id-◀-monic $ 
  (f ▶ ρ← _) ◀ id ≡⟨ swap-▶◀ ⟩ 
  α← f id id ∘ f ▶ (ρ← id ◀ id) ∘ α→ f (id ⊗ id) id ≡⟨⟩
  Hom.has-section→epic (Hom.iso→from-has-section ((▶-iso B f (α≅ _ _ _)) Hom.∘Iso (α≅ _ _ _))) _ _ (
    (α← _ _ _ ∘ f ▶ (ρ← _ ◀ id) ∘ α→ _ _ _) ∘ (α← _ _ _ ∘ f ▶ α← _ _ _) ≡⟨ Hom.pullr (Hom.pullr (Hom.cancell (α≅.invl _ _ _))) ⟩
    α← _ _ _ ∘ (f ▶ (ρ← _ ◀ id)) ∘ (f ▶ α← _ _ _)                       ≡˘⟨ Hom.refl⟩∘⟨ postaction B f .F-∘ _ _ ⟩
    α← _ _ _ ∘ f ▶ ⌜ (ρ← _ ◀ id) ∘ α← id id id ⌝                        ≡⟨ ap! (triangle _ _) ⟩
    α← _ _ _ ∘ f ▶ (id ▶ λ← _)                                          ≡⟨ α←nat _ _ _ ⟩
    (⌜ Hom.id ◆ Hom.id ⌝ ◆ λ← id) ∘ α← _ _ _                            ≡⟨ ap! compose.F-id ⟩
    ⌜ (f ⊗ id) ▶ λ← _ ⌝ ∘ α← _ _ _                                      ≡˘⟨ ap¡ (triangle _ _) ⟩
    (⌜ ρ← _ ◀ id ⌝ ∘ α← _ _ _) ∘ α← _ _ _                               ≡⟨ ap! ρ←◀ ⟩
    (ρ← _ ∘ α← _ _ _) ∘ α← _ _ _                                        ≡⟨ Hom.pullr (sym (pentagon _ _ _ _)) ⟩ 
    ρ← _ ∘ α← _ _ _ ◀ id ∘ α← _ _ _ ∘ f ▶ α← _ _ _                      ≡⟨ Hom.assoc _ _ _ ⟩
    (⌜ ρ← _ ⌝ ∘ ((α← _ _ _) ◀ id)) ∘ (α← _ _ _ ∘ f ▶ α← _ _ _)          ≡˘⟨ ap¡ ρ←◀ ⟩
    ((ρ← _ ◀ id) ∘ ((α← _ _ _) ◀ id)) ∘ (α← _ _ _ ∘ f ▶ α← _ _ _)       ≡˘⟨ (preaction B id .F-∘ _ _) Hom.⟩∘⟨refl ⟩
    (ρ← _ ∘ α← _ _ _) ◀ id ∘ (α← _ _ _ ∘ f ▶ α← _ _ _) ∎
  )



λ←≡ρ← : λ← (id {a}) ≡ ρ← id
λ←≡ρ← = id-▶-monic $
  id ▶ λ← id ≡⟨ Hom.insertr (α≅.invl _ _ _) ⟩ 
  (id ▶ λ← id ∘ α→ _ _ _) ∘ α← _ _ _  ≡⟨ (B^op.triangle _ _) Hom.⟩∘⟨refl ⟩
  ρ← _ ◀ id ∘ α← _ _ _                ≡⟨ ρ←◀ Hom.⟩∘⟨refl ⟩
  ρ← _ ∘ α← _ _ _ ≡˘⟨ ▶ρ← ⟩
  id ▶ ρ← id ∎

λ→≡ρ→ : λ→ (id {a}) ≡ ρ→ id
λ→≡ρ→ = Hom.inv-path (Hom.iso→invertible (λ≅ _)) (Hom.iso→invertible (ρ≅ _)) λ←≡ρ←


-- lemma : λ→ id ≡ (λ← _ ∘ (α→ _ _ _)) ∘ ρ→ _ ∘ λ→ _
-- lemma = {!   !}

```
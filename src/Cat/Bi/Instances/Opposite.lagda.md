```agda

open import Cat.Prelude
open import Cat.Bi.Base
open import Cat.Bi.Displayed.Base
open import Cat.Displayed.Base
open import Cat.Functor.Naturality
open import Cat.Instances.Product
open import Cat.Functor.Bifunctor


import Cat.Reasoning as CR
import Cat.Morphism.Duality as CMD

module Cat.Bi.Instances.Opposite where

module _ {o oh ℓh} (B : Prebicategory o oh ℓh) where
  open Prebicategory B hiding (module Hom)
  open Functor
  open make-natural-iso
  
  private module Hom {A B : Ob} where
    open CMD (Hom A B) public
    open CR (Hom A B) public

  ◆-invertible 
    : ∀ {a b c} 
    → {f g : b ↦ c} {h k : a ↦ b} 
    → {α : f ⇒ g} {β : h ⇒ k} 
    → Hom.is-invertible α → Hom.is-invertible β → Hom.is-invertible (α ◆ β) 
  ◆-invertible α-inv β-inv = 
    Hom.make-invertible 
      ((α-inv.inv) ◆ (β-inv.inv)) 
      ((sym $ compose.F-∘ _ _) ∙∙ (ap₂ (λ x y → x ◆ y) α-inv.invl β-inv.invl) ∙∙ compose.F-id) 
      ((sym $ compose.F-∘ _ _) ∙∙ (ap₂ (λ x y → x ◆ y) α-inv.invr β-inv.invr) ∙∙ compose.F-id) 
    where
      module α-inv = Hom.is-invertible α-inv
      module β-inv = Hom.is-invertible β-inv 
  
  ◆-iso  
    : ∀ {a b c} 
    → {f g : b ↦ c} {h k : a ↦ b} 
    → f Hom.≅ g → h Hom.≅ k → (f ⊗ h) Hom.≅ (g ⊗ k)
  ◆-iso i j = Hom.invertible→iso (i .Hom.to ◆ j .Hom.to) (◆-invertible (Hom.iso→invertible i) (Hom.iso→invertible j))

  _^Op : Prebicategory _ _ _
  _^Op .Prebicategory.Ob = Ob
  _^Op .Prebicategory.Hom A B = Hom B A
  _^Op .Prebicategory.id = id
  _^Op .Prebicategory.compose = Flip compose
  _^Op .Prebicategory.unitor-l = iso→isoⁿ (isoⁿ→iso unitor-r) λ f → sym $ ρ→nat f
  _^Op .Prebicategory.unitor-r = iso→isoⁿ (isoⁿ→iso unitor-l) λ f → sym $ λ→nat f
  _^Op .Prebicategory.associator = iso→isoⁿ (λ (f , g , h) → α≅ h g f Hom.Iso⁻¹) λ (f , g , h) → sym $ α←nat h g f

  _^Op .Prebicategory.triangle f g = 
    Hom.has-section→epic (Hom.iso→from-has-section (α≅ _ _ _)) _ _ $
    ((g ▶ λ← f) ∘ (α→ g id f)) ∘ (α← g id f) ≡⟨ Hom.cancelr (α≅.invl g id f) ⟩
    g ▶ λ← f                                 ≡˘⟨ triangle g f ⟩
    (ρ← g ◀ f) ∘ α← g id f                   ∎

  _^Op .Prebicategory.pentagon f g h i = 
    Hom.inv-path 
      (Hom.iso→invertible $ ◆-iso Hom.id-iso (α≅ _ _ _) Hom.∘Iso α≅ _ _ _ Hom.∘Iso ◆-iso (α≅ _ _ _) Hom.id-iso)
      (Hom.iso→invertible $ (α≅ _ _ _) Hom.∘Iso (α≅ _ _ _))
      ((sym $ Hom.assoc _ _ _) ∙ pentagon _ _ _ _)



  compose^co : ∀ {A B C} → Functor (Hom B C ^op ×ᶜ Hom A B ^op) (Hom A C ^op)
  compose^co .F₀ = compose.F₀
  compose^co .F₁ = compose.F₁
  compose^co .F-id = compose.F-id
  compose^co .F-∘ f g = compose.F-∘ g f

  _^Co : Prebicategory _ _ _
  _^Co .Prebicategory.Ob = Ob
  _^Co .Prebicategory.Hom A B = Hom A B ^op
  _^Co .Prebicategory.id = id
  _^Co .Prebicategory.compose = compose^co
  _^Co .Prebicategory.unitor-l = iso→isoⁿ (λ x → Hom.iso→co-iso (λ≅ x Hom.Iso⁻¹)) λ f → λ←nat f
  _^Co .Prebicategory.unitor-r = iso→isoⁿ (λ x → Hom.iso→co-iso (ρ≅ x Hom.Iso⁻¹)) λ f → ρ←nat f
  _^Co .Prebicategory.associator = iso→isoⁿ (λ (f , g , h) → Hom.iso→co-iso (α≅ f g h Hom.Iso⁻¹)) λ (f , g , h) → α←nat f g h
  _^Co .Prebicategory.triangle f g = 
    Hom.inv-path 
      (Hom.iso→invertible $ (α≅ _ _ _) Hom.∘Iso (◆-iso (ρ≅ _) Hom.id-iso))
      (Hom.iso→invertible $ ◆-iso Hom.id-iso (λ≅ _))
      (triangle f g)

  _^Co .Prebicategory.pentagon f g h i = 
    Hom.inv-path 
      (Hom.iso→invertible $ ◆-iso (α≅ _ _ _) Hom.id-iso Hom.∙Iso α≅ _ _ _ Hom.∙Iso ◆-iso Hom.id-iso (α≅ _ _ _))
      (Hom.iso→invertible $ (α≅ _ _ _) Hom.∘Iso (α≅ _ _ _)) 
      (pentagon f g h i)

module _ {o oh ℓh} (B : Prebicategory o oh ℓh) where

  _^Coop : Prebicategory _ _ _
  _^Coop = B ^Co ^Op

``` 
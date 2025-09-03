```agda


open import Cat.Prelude
open import Cat.Bi.Base
open import Cat.Bi.Instances.Opposite
open import Cat.Bi.Displayed.Base
open import Cat.Bi.Displayed.Cartesian
open import Cat.Displayed.Base
open import Cat.Displayed.Functor
open import Cat.Displayed.Functor.Naturality
open import Cat.Displayed.Instances.Elements
open import Cat.Displayed.Instances.TotalProduct
open import Cat.Functor.Base
open import Cat.Functor.Naturality
open import Cat.Morphism.Duality

import Cat.Reasoning as CR


module Cat.Bi.Displayed.Instances.Elements
  {o oh ℓh oc ℓc} {B : Prebicategory o oh ℓh}
  (P : Pseudofunctor (B ^Coop) (Cat oc ℓc))
  where

  open Prebicategory B hiding (module Hom)
  module Hom {A B : Ob} where
    open CR (Hom A B) public

  open Functor
  open Displayed-functor
  open _=>_
  open make-natural-iso[_]

  module Cat = Prebicategory (Cat oc ℓc)
  module P where
    open Pseudofunctor P public
    module _ {A : Ob} where
      open CR (P₀ A) public

  -- Fibre : Ob → Precategory _ _
  -- Fibre X .Precategory.Ob = P.₀ ʻ X
  -- Fibre X .Precategory.Hom a b = P.Hom a (P.₁ id · b)
  -- Fibre X .Precategory.Hom-set a b = hlevel 2
  -- Fibre X .Precategory.id = P.υ→ .η _
  -- Fibre X .Precategory._∘_ f g = f P.∘ P.υ← .η _ P.∘ g
  -- Fibre X .Precategory.idr f = P.elimr (P.unitor.invr ηₚ _)
  -- Fibre X .Precategory.idl f = P.cancell (P.unitor.invl ηₚ _)
  -- Fibre X .Precategory.assoc f g h = P.pulll3 refl

  
  El-hom : ∀ {A B} → P.₀ ʻ A → P.₀ ʻ B → ⌞ PSh ℓc (Hom A B) ⌟
  El-hom A' B' .F₀ f = el! (P.Hom A' (P.₁ f · B'))
  El-hom A' B' .F₁ α Γ = P.₂ α .η B' P.∘ Γ
  El-hom A' B' .F-id = ext λ x → ap (P._∘ x) (P.₂-id ηₚ _) ∙ P.idl _
  El-hom A' B' .F-∘ f g = ext λ x → P.pushl (P.₂-∘ _ _ ηₚ _)

  El-compose : ∀ {A B C A' B' C'} → Displayed-functor compose 
      (∫ (Hom B C) (El-hom B' C') ×ᵀᴰ ∫ (Hom A B) (El-hom A' B'))
      (∫ (Hom A C) (El-hom A' C'))
  El-compose {A' = A'} .F₀' {f , g} (f' , g') = P.γ→ g f .η _ P.∘ P.₁ g .F₁ f' P.∘ g'
  El-compose  {A' = A'} {B' = B'} {C' = C'} .F₁' {a = f , g} {b = h , k} {f = α , β} {a' = f' , g'} {b' = h' , k'} (α' , β') =
    P.₂ (α ◆ β) .η _ P.∘ P.γ→ k h .η _ P.∘ (P.₁ k) .F₁ h' P.∘ k' ≡⟨ P.pulll (sym (P.γ→nat β α ηₚ _)) ⟩
    (P.γ→ g f .η _ P.∘ (P.₁ g) .F₁ (P.₂ α .η _) P.∘ P.₂ β .η _) P.∘ (P.₁ k) .F₁ h' P.∘ k'     ≡⟨ P.pullr $ P.pullr $ P.pulll $ P.₂ β .is-natural _ _ _ ⟩
    P.γ→ g f .η _ P.∘ (P.₁ g) .F₁ (P.₂ α .η _) P.∘ ⌜ ((P.₁ g) .F₁ h' P.∘ P.₂ β .η _) P.∘ k' ⌝ ≡⟨ ap! $ P.pullr β' ⟩
    P.γ→ g f .η _ P.∘ (P.₁ g) .F₁ (P.₂ α .η _) P.∘ (P.₁ g) .F₁ h' P.∘ g'                      ≡⟨ P.pulll3 (P.refl⟩∘⟨ sym (P.₁ g .F-∘ _ _)) ⟩
    (P.γ→ g f .η _ P.∘ (P.₁ g) .F₁ ⌜ P.₂ α .η _ P.∘ h' ⌝) P.∘ g'                              ≡⟨ ap! α' ⟩
    (P.γ→ g f .η _ P.∘ (P.₁ g) .F₁ f') P.∘ g'                                                 ≡˘⟨ P.assoc _ _ _ ⟩ 
    P.γ→ g f .η _ P.∘ F₁ (P.₁ g) f' P.∘ g'                                                    ∎
  El-compose .F-id' = prop!
  El-compose .F-∘' = prop!


  El : Bidisplayed B _ _ _
  El .Bidisplayed.Ob[_] A = P.₀ ʻ A
  El .Bidisplayed.Hom[_,_] {A = A} {B = B} A' B' = ∫ _ (El-hom A' B')
  El .Bidisplayed.↦id' = P.υ→ .η _
  El .Bidisplayed.compose' {A' = A'} {B'} {C'} = El-compose {A' = A'} {B'} {C'} 
  El .Bidisplayed.unitor-l' {A' = A'} {B' = B'} = to-natural-iso' ni where

    p : ∀ {x} x' → _
    p {x} x' = P.pushr (P.pushr ((sym (P.idr _)) P.⟩∘⟨refl)) ∙∙ (ap (P._∘ x') $ P.right-unit x ηₚ B') ∙∙ P.idl _

    ni : make-natural-iso[ _ ] _ _
    ni .eta' {x} x' = p x'
    ni .inv' {x} x' = P.has-retract→monic (P.invertible→from-has-retract inv) _ _ $ P.cancell inv.invr ∙ sym (p x')
      where
        inv : P.is-invertible (P.₂ (λ← x) .η B')
        inv = P.iso→invertible $ isoⁿ→iso (F-map-iso P.P₁ (iso→co-iso _ (λ≅ x Hom.Iso⁻¹))) B'
        module inv = P.is-invertible inv

    ni .eta∘inv' _ = prop!
    ni .inv∘eta' _ = prop!
    ni .natural' _ _ _ = prop!
  El .Bidisplayed.unitor-r' {A' = A'} {B' = B'} = to-natural-iso' ni where

    p : ∀ {x} x' → _
    p {x} x' = P.pushr (P.pushr (sym ((P.eliml (P.₁ id .F-id) P.⟩∘⟨refl) ∙ P.unitor .η Id .is-natural _ _ _))) ∙∙ ap (P._∘ x') $ P.left-unit x ηₚ B' ∙∙ P.idl _
    
    ni : make-natural-iso[ _ ] _ _
    ni .eta' {x} x' = p x'
    ni .inv' {x} x' = 
      P.has-retract→monic (P.invertible→from-has-retract inv) _ _ $ P.cancell inv.invr ∙ sym (p x')
      where
        inv : P.is-invertible (P.₂ (ρ← x) .η B')
        inv = P.iso→invertible $ isoⁿ→iso (F-map-iso P.P₁ (iso→co-iso _ (ρ≅ x Hom.Iso⁻¹))) B'
        module inv = P.is-invertible inv

    ni .eta∘inv' _ = prop!
    ni .inv∘eta' _ = prop!
    ni .natural' _ _ _ = prop!
-- hexagon
--       : ∀ {a b c d} (f : c B.↦ d) (g : b B.↦ c) (h : a B.↦ b)
--       → ₂ (B.α→ f g h) C.∘ γ→ (f B.⊗ g) h C.∘ (γ→ f g C.◀ ₁ h)
--       ≡ γ→ f (g B.⊗ h) C.∘ (₁ f C.▶ γ→ g h) C.∘ C.α→ (₁ f) (₁ g) (₁ h)

  El .Bidisplayed.associator' {A' = A'} {B' = B'} {C' = C'} {D' = D'} = to-natural-iso' ni where

 
    ni : make-natural-iso[ _ ] _ _
    ni .eta' {f , g , h} (f' , g' , h') = 
      P.₂ (α→ f g h) .η _ P.∘ P.γ→ (g ⊗ h) f .η _ P.∘ P.₁ (g ⊗ h) .F₁ f' P.∘ ⌜ P.γ→ h g .η C' P.∘ (P.₁ h) .F₁ g' P.∘ h' ⌝  ≡⟨ ap! {!P.γ→nat _ _   !} ⟩
      P.₂ (α→ f g h) .η _ P.∘ P.γ→ (g ⊗ h) f .η _ P.∘ P.₁ (g ⊗ h) .F₁ f' P.∘ P.γ→ h g .η C' P.∘ (P.₂ id Cat.◆ {!   !}) .η _ ≡⟨ {!   !} ⟩ 
      {!   !} ≡⟨ {!   !} ⟩
      (P.₂ (α→ f g h) .η _ P.∘ P.γ→ (g ⊗ h) f .η _ P.∘ ⌜ P.γ→ h g .η _ ⌝) P.∘ w ≡˘⟨ ap¡ (P.eliml (P.₁ (g ⊗ h) .F-id)) ⟩ 
      (P.₂ (α→ f g h) .η _ P.∘ P.γ→ (g ⊗ h) f .η _ P.∘ P.₁ (g ⊗ h) .F₁ P.id P.∘ P.γ→ h g .η _) P.∘ _ ≡⟨ ap (P._∘ w) $ P.hexagon h g f ηₚ _ ⟩
      (P.γ→ h (f ⊗ g) .η _ P.∘ ((P.₁ h) .F₁ (P.γ→ g f .η _) P.∘ P.id) P.∘ P.id) P.∘ (P.₁ h) .F₁ ((P.₁ g) .F₁ f') P.∘ (P.₁ h) .F₁ g' P.∘ h' ≡⟨ {!   !} ⟩
      P.γ→ h (f ⊗ g) .η _ P.∘ (P.₁ h) .F₁ (P.γ→ g f .η _ P.∘ (P.₁ g) .F₁ f' P.∘ g') P.∘ h' ∎
      where
        w = (P.₁ h Cat.⊗ P.₁ g) .F₁ f' P.∘ P.₁ h .F₁ g' P.∘ h'

    ni .inv' = {!   !}
    ni .eta∘inv' _ = prop!
    ni .inv∘eta' _ = prop!
    ni .natural' _ _ _ = prop!

  El .Bidisplayed.triangle' _ _ = prop!
  El .Bidisplayed.pentagon' _ _ _ _  = prop!

```
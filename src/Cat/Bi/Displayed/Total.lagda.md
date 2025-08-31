```agda

open import Cat.Prelude
open import Cat.Functor.Naturality
open import Cat.Instances.Product
open import Cat.Bi.Base
open import Cat.Bi.Displayed.Base
open import Cat.Displayed.Base
open import Cat.Displayed.Functor
open import Cat.Displayed.Total

module Cat.Bi.Displayed.Total where

module _ {o oh ℓh o' oh' ℓh'} {B : Prebicategory o oh ℓh} (E : Bidisplayed B o' oh' ℓh') where

  open Prebicategory B
  open Bidisplayed E
  open make-natural-iso
  open Functor
  open _=>_
  open _=[_]=>_

  ∫compose : ∀ {A B C} {A' : Ob[ A ]} {B' : Ob[ B ]} {C' : Ob[ C ]} → Functor (∫ Hom[ B' , C' ] ×ᶜ ∫ Hom[ A' , B' ]) (∫ Hom[ A' , C' ])
  ∫compose .F₀ ((f , f') , (g , g')) = f ⊗ g , f' ⊗' g'
  ∫compose .F₁ (∫hom α α' , ∫hom β β') = ∫hom (α ◆ β) (α' ◆' β')
  ∫compose .F-id = ∫Hom-path _ compose.F-id compose'.F-id'
  ∫compose .F-∘ _ _ = ∫Hom-path _ (compose.F-∘ _ _) compose'.F-∘'

  B∫ : Prebicategory _ _ _
  B∫ .Prebicategory.Ob = Σ[ x ∈ Ob ] Ob[ x ]
  B∫ .Prebicategory.Hom = λ (x , x') (y , y') → ∫ Hom[ x' , y' ]
  B∫ .Prebicategory.id = id , ↦id'
  B∫ .Prebicategory.compose = ∫compose
  B∫ .Prebicategory.unitor-l = to-natural-iso ni where
    ni : make-natural-iso _ _
    ni .eta _ = ∫hom (λ→ _) (λ→' _)
    ni .inv _ = ∫hom (λ← _) (λ←' _)
    ni .eta∘inv _ = ∫Hom-path _ (unitor-l.invl ηₚ _) (unitor-l'.invl' ηₚ' _)
    ni .inv∘eta _ = ∫Hom-path _ (unitor-l.invr ηₚ _) (unitor-l'.invr' ηₚ' _)
    ni .natural x y f = sym $ ∫Hom-path _ (λ→nat _) (λ→nat' _)
  B∫ .Prebicategory.unitor-r = to-natural-iso ni where
    ni : make-natural-iso _ _
    ni .eta _ = ∫hom (ρ→ _) (ρ→' _)
    ni .inv _ = ∫hom (ρ← _) (ρ←' _)
    ni .eta∘inv _ = ∫Hom-path _ (unitor-r.invl ηₚ _) (unitor-r'.invl' ηₚ' _)
    ni .inv∘eta _ = ∫Hom-path _ (unitor-r.invr ηₚ _) (unitor-r'.invr' ηₚ' _)
    ni .natural x y f = sym $ ∫Hom-path _ (ρ→nat _) (ρ→nat' _)
  B∫ .Prebicategory.associator = to-natural-iso ni where
    ni : make-natural-iso _ _
    ni .eta _ = ∫hom (α→ _ _ _) (α→' _ _ _)
    ni .inv _ = ∫hom (α← _ _ _) (α←' _ _ _)
    ni .eta∘inv _ = ∫Hom-path _ (associator.invl ηₚ _) (associator'.invl' ηₚ' _)
    ni .inv∘eta _ = ∫Hom-path _ (associator.invr ηₚ _) (associator'.invr' ηₚ' _)
    ni .natural x y f = sym $ ∫Hom-path _ (α→nat _ _ _) (α→nat' _ _ _)
  B∫ .Prebicategory.triangle (f , f') (g , g') = ∫Hom-path _ (triangle f g) (triangle' f' g')
  B∫ .Prebicategory.pentagon (f , f') (g , g') (h , h') (i , i') = ∫Hom-path _ (pentagon f g h i) (pentagon' f' g' h' i')
```
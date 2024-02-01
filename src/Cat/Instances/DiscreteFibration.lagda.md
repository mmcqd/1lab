```agda

open import Cat.Prelude
open import Cat.Displayed.Base
open import Cat.Displayed.Functor
open import Cat.Displayed.Cartesian.Discrete
open import Cat.Functor.Hom using (よ₀ ; よ₁) 
open import Cat.Functor.Base
open import Cat.Functor.Equivalence
open import Cat.Functor.Equivalence.Path
open import Cat.Displayed.Cartesian.Right
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Instances.Elements
open import Cat.Diagram.Terminal
open import Cat.Diagram.Product
open import Cat.Diagram.Exponential
open import Cat.CartesianClosed.Instances.PSh

open Precategory
open Displayed
open Discrete-fibration
open Vertical-functor
open Functor
open _=>_
open is-precat-iso

module Cat.Instances.DiscreteFibration {o ℓ} (B : Precategory o ℓ) where

private module B = Precategory B

DFib : ∀ o' ℓ' → Precategory _ _
DFib o' ℓ' .Ob = Σ[ E ∈ Displayed B o' ℓ' ] Discrete-fibration E
DFib o' ℓ' .Hom (E , E-disc) (F , F-disc) = Vertical-functor E F
DFib o' ℓ' .Hom-set (E , E-disc) (F , F-disc) = is-hlevel≃ 2 (Iso→Equiv eqv) hlevel!
  where 
    unquoteDecl eqv = declare-record-iso eqv (quote Vertical-functor)
    module F = Displayed F
    instance
      _ : ∀ {x n} → H-Level F.Ob[ x ] (2 + n)
      _ = basic-instance 2 (F-disc .fibre-set _)

DFib o' ℓ' .id = IdV
DFib o' ℓ' ._∘_ = _V∘_
DFib o' ℓ' .idr f = Vertical-functor-path (λ _ → refl) (λ _ → refl)
DFib o' ℓ' .idl f = Vertical-functor-path (λ _ → refl) (λ _ → refl)
DFib o' ℓ' .assoc f g h = Vertical-functor-path (λ _ → refl) (λ _ → refl)

private module DFib {o' ℓ'} = Precategory (DFib o' ℓ')

DFib-よ₀ : B.Ob → DFib ℓ ℓ .Ob
DFib-よ₀ x = presheaf→discrete B (よ₀ B x)

DFib-よ₁ : ∀ {x y} → B.Hom x y → DFib.Hom (DFib-よ₀ x) (DFib-よ₀ y)
DFib-よ₁ f = nat→vertical B (よ₁ B f)

DFib-よ : Functor B (DFib ℓ ℓ)
DFib-よ .F₀ = DFib-よ₀
DFib-よ .F₁ = DFib-よ₁
DFib-よ .F-id = Vertical-functor-path (λ x' → B.idl x') λ f → prop!
DFib-よ .F-∘ f g = Vertical-functor-path (λ x' → sym (B.assoc _ _ _)) λ f → prop!


PSh≡DFib : ∀ {κ} → PSh κ B ≡ DFib κ κ 
PSh≡DFib = Precategory-path F ipc where
  F : Functor _ _
  F .F₀ = presheaf→discrete B
  F .F₁ = nat→vertical B
  F .F-id = Vertical-functor-path (λ _ → refl) (λ _ → prop!)
  F .F-∘ f g = Vertical-functor-path (λ _ → refl) (λ _ → prop!)

  module F = Functor F
    

  F₁-iso : ∀ {x y} → is-iso (F.₁ {x} {y})
  F₁-iso .is-iso.inv G = NT (λ x → G .F₀' {x}) λ x y f → ext λ x' → sym (G .F₁' refl)
  F₁-iso .is-iso.rinv G = Vertical-functor-path (λ _ → refl) (λ _ → prop!)
  F₁-iso .is-iso.linv α = trivial!

  
  ipc : is-precat-iso F
  ipc .has-is-ff = is-iso→is-equiv F₁-iso
  ipc .has-is-iso = is-iso→is-equiv (presheaf≃discrete B)

 
DFib-terminal : ∀ {κ} → Terminal (DFib κ κ)
DFib-terminal {κ} = subst Terminal PSh≡DFib (PSh-terminal {κ = κ} {C = B})

DFib-products : ∀ {κ} → has-products (DFib κ κ)
DFib-products {κ} = subst has-products PSh≡DFib (PSh-products {κ = κ} {C = B})


-- lemma : ∀ {κ} → PathP (λ i → Terminal (PSh≡DFib i)) (PSh-terminal {κ = κ} {C = B}) DFib-terminal
-- lemma = to-pathp refl

-- lemma' : ∀ {κ} → PathP (λ i → has-products (PSh≡DFib i)) (PSh-products {κ = κ} {C = B}) DFib-products
-- lemma' = to-pathp refl

-- PSh-closed : Cartesian-closed (PSh (o ⊔ h ⊔ κ) C) (PSh-products {C = C}) (PSh-terminal {C = C})

-- DFib-closed : ∀ {κ} → Cartesian-closed (DFib _ _) DFib-products DFib-terminal
-- DFib-closed {κ} = transport (λ i → Cartesian-closed (PSh≡DFib i) (lemma' i) (lemma i)) (PSh-closed {o = o} {h = ℓ} {κ = κ} {C = B})

``` 
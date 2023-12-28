```agda
open import Cat.Prelude
open import Order.Base
open import Order.Instances.Pointwise
open import Order.DCPO
import Order.Reasoning
import Order.Diagram.Lub
open import Cat.Diagram.Product.Indexed
open import Cat.Functor.Subcategory
open Indexed-product
open is-indexed-product
open Subcat-hom

module Order.DCPO.Pointwise where


module _ {o ℓ κ} (I : Set κ) (F : ⌞ I ⌟ → DCPO (o ⊔ κ) (ℓ ⊔ κ)) where
  private

    Fᵖ = fst ⊙ F
    
    ⌞F⌟ = ⌞_⌟ ⊙ Fᵖ

    open is-dcpo
    open is-directed-family

    
    module F {i : ⌞ I ⌟} where
      open DCPO (F i) public
      open Order.Diagram.Lub poset public
      open Lub public
      open is-lub public

    module ΠFᵖ where
      open Order.Reasoning (Pointwise ⌞ I ⌟ Fᵖ) public hiding (≤-refl')
      open Order.Diagram.Lub (Pointwise ⌞ I ⌟ Fᵖ) public
      open Indexed-product (Posets-has-indexed-products {o} {ℓ} Fᵖ) public
      open Lub public
      open is-lub public


    ΠFᵖ = Pointwise ⌞ I ⌟ Fᵖ

  ΠFᵖ-is-dcpo : is-dcpo ΠFᵖ
  ΠFᵖ-is-dcpo .directed-lubs f dir .ΠFᵖ.lub i = F.⋃ ((_$ i) ⊙ f) (monotone∘directed (prjᵖ {P = Fᵖ} i) dir)
  ΠFᵖ-is-dcpo .directed-lubs f dir .ΠFᵖ.has-lub .ΠFᵖ.fam≤lub a i = F.fam≤⋃ ((_$ i) ⊙ f) (monotone∘directed (prjᵖ {P = Fᵖ} i) dir) a
  ΠFᵖ-is-dcpo .directed-lubs f dir .ΠFᵖ.has-lub .ΠFᵖ.least ub' le i = F.⋃-least ((_$ i) ⊙ f) (monotone∘directed (prjᵖ {P = Fᵖ} i) dir) (ub' i) ((_$ i) ⊙ le)
  

  DCPOs-has-indexed-products : Indexed-product (DCPOs _ _) F
  DCPOs-has-indexed-products .ΠF = ΠFᵖ , ΠFᵖ-is-dcpo
  DCPOs-has-indexed-products .π i .hom = prjᵖ i
  DCPOs-has-indexed-products .π i .witness s dir lub is-lub .F.fam≤lub a = is-lub .ΠFᵖ.fam≤lub a i
  DCPOs-has-indexed-products .π i .witness s dir lub is-lub .F.least ub' le = {!   !}
  DCPOs-has-indexed-products .has-is-ip .tuple = {!   !}
  DCPOs-has-indexed-products .has-is-ip .commute = {!   !}
  DCPOs-has-indexed-products .has-is-ip .unique = {!   !}
  
```    
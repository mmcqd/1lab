
<!--
```agda
open import Cat.Prelude

open import Cat.Functor.Subcategory
open import Order.DCPO
open import Order.Base
open import Cat.Diagram.Product
open import Cat.Diagram.Terminal
open import Order.Instances.Pointwise

import Order.Diagram.Lub


```
-->


```agda

module Order.DCPO.Product where

```


<!--
```agda
_ = DCPOs
``` 
-->

# Products of DCPOs

We show that `DCPOs`{.Agda} has all finite products

```agda

module _ {o ℓ} (D E : DCPO o ℓ) where
  open Order.Diagram.Lub
  open Lub
  open is-lub
  open Terminal
  
  private
    module D where
      open DCPO D public
      open Order.Diagram.Lub poset public

    module E where
      open DCPO E public
      open Order.Diagram.Lub poset public
  
    module D×ᵖE where
      open Order.Diagram.Lub (D.poset ×ᵖ E.poset) public
      open Product (Posets-has-products D.poset E.poset) public
      
  _×ᵖ_is-dcpo : is-dcpo (D.poset ×ᵖ E.poset)
  _×ᵖ_is-dcpo .is-dcpo.directed-lubs f dir = D×ᵖE-Lub
    where

      module ⋃D = D.⋃ _ (monotone∘directed Fstᵖ dir)
      module ⋃E = E.⋃ _ (monotone∘directed Sndᵖ dir)
      
      D×ᵖE-Lub : D×ᵖE.Lub f
      D×ᵖE-Lub .lub = ⋃D.lub , ⋃E.lub
      D×ᵖE-Lub .has-lub .fam≤lub i = ⋃D.fam≤lub i , ⋃E.fam≤lub i
      D×ᵖE-Lub .has-lub .least (ubD' , ubE') le = ⋃D.least ubD' (fst ⊙ le) , ⋃E.least ubE' (snd ⊙ le)


  DCPOs-has-products : Product (DCPOs _ _) D E
  DCPOs-has-products = prod
    where
      open Product
      open is-product
      open Subcat-hom
      
      prod : Product (DCPOs _ _) D E
      prod .apex .fst = D×ᵖE.apex
      prod .apex .snd = _×ᵖ_is-dcpo
      prod .π₁ = to-scottᵐ Fstᵖ λ s dir → D.⋃.has-lub (fst ⊙ s) (monotone∘directed Fstᵖ dir) 
      prod .π₂ = to-scottᵐ Sndᵖ λ s dir → E.⋃.has-lub (snd ⊙ s) (monotone∘directed Sndᵖ dir)
      prod .has-is-product .⟨_,_⟩ f g = to-scott-directed (λ x → f # x , g # x) λ where 
        s dir x l .fam≤lub i → (f .witness s dir x l .fam≤lub i) , (g .witness s dir x l .fam≤lub i)
        s dir x l .least ub' l' → (f .witness s dir x l .least (ub' .fst) (fst ⊙ l')) , (g .witness s dir x l .least (ub' .snd) (snd ⊙ l'))
      prod .has-is-product .π₁∘factor = trivial!
      prod .has-is-product .π₂∘factor = trivial!
      prod .has-is-product .unique other α β = ext λ x → happly (ap (hom ⊙ Subcat-hom.hom) α) x , happly (ap (hom ⊙ Subcat-hom.hom) β) x 

  
  DCPOs-terminal : Terminal (DCPOs o ℓ)
  DCPOs-terminal .top .fst = Posets-terminal .top
  DCPOs-terminal .top .snd .is-dcpo.directed-lubs f x .lub = lift tt
  DCPOs-terminal .top .snd .is-dcpo.directed-lubs f x .has-lub .fam≤lub _ = lift tt
  DCPOs-terminal .top .snd .is-dcpo.directed-lubs f x .has-lub .least _ _ = lift tt
  DCPOs-terminal .has⊤ x .centre .Subcat-hom.hom = Posets-terminal .has⊤ (x .fst) .centre
  DCPOs-terminal .has⊤ x .centre .Subcat-hom.witness s fam y l .fam≤lub _ = lift tt
  DCPOs-terminal .has⊤ x .centre .Subcat-hom.witness s fam y l .least _ _ = lift tt
  DCPOs-terminal .has⊤ x .paths y = trivial!
```

 
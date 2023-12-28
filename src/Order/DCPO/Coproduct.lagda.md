
<!--
```agda
open import Cat.Prelude

open import Cat.Functor.Subcategory
open import Order.DCPO
open import Order.Base
open import Order.Displayed
open import Cat.Diagram.Coproduct
open import Cat.Diagram.Coproduct.Indexed
open import Cat.Diagram.Initial
open import Order.Instances.Coproduct
open import Order.DCPO.Disjoint
open import Data.Sum
open import Data.Bool
open import Order.Univalent

open import 1Lab.Reflection.Marker

open import Order.Instances.Disjoint hiding (_≤[_]_)

import Order.Diagram.Lub
import Order.Reasoning


```
-->


```agda

module Order.DCPO.Coproduct where

```


<!--
```agda
_ = DCPOs
``` 
-->

# Products of DCPOs

We show that `DCPOs`{.Agda} has all finite coproducts


```agda

module _ {o ℓ} (D E : DCPO o ℓ) where

  open Coproduct
  open is-coproduct
  open Initial
  open is-directed-family
  open is-dcpo
  open import Cat.Morphism
  open Inverses

  module D = DCPO D
  module E = DCPO E

  DCPOs-has-coproducts : Coproduct (DCPOs o ℓ) D E
  DCPOs-has-coproducts = bool-indexed-coproducts→coproducts (DCPOs _ _) (DCPOs-has-set-indexed-coproducts (el! Bool)) D E
  
  ⊎ᵖ-is-coproducts : DCPOs-has-coproducts .coapex .fst ≡ D.poset ⊎ᵖ E.poset
  ⊎ᵖ-is-coproducts = sym (subst (λ f → D.poset ⊎ᵖ E.poset ≡ ∫ (Disjoint-over (el! Bool) f)) (ext (Bool-elim _ refl refl)) (⊎≡Disjoint-bool D.poset E.poset))

  DCPOs-initial : Initial (DCPOs o ℓ)
  DCPOs-initial .bot .fst = Posets-initial .bot
  DCPOs-initial .bot .snd .directed-lubs f dir = ∥-∥-rec! (λ i → absurd (f i .Lift.lower)) (dir .elt)
    where open Order.Diagram.Lub (𝟘ᵖ {o} {ℓ})
  DCPOs-initial .has⊥ x .centre = to-scott-directed (λ ()) λ s dir _ _ → ∥-∥-rec! (λ i → absurd (s i .Lift.lower)) (dir .elt) 
    where open Order.Diagram.Lub (x .fst)
  DCPOs-initial .has⊥ x .paths f = ext λ ()
```      
                                
                                    
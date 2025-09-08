```agda

open import Cat.Prelude
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Functor
open import Cat.Bi.Base
open import Cat.Bi.Displayed.Base
open import Cat.Bi.Displayed.Instances.2FullSubBicategory 

module Cat.Bi.Displayed.Instances.Fib o ℓ o' ℓ' where

open 2-full-sub-bicat

private module Disp = Bidisplayed (Displayed-cat o ℓ o' ℓ')
```
*Fib*, the displayed bicategory of fibrations, is the 2-full sub-bicategory
of `Displayed-cat` which picks out the cartesian fibrations and 
the fibred functors between them.

```agda 

Fib : Bidisplayed (Cat o ℓ ) _ _ _
Fib = Birestrict (Displayed-cat o ℓ o' ℓ') λ where
    .is-ob[] → Cartesian-fibration
    .is-hom[] → is-fibred-functor
    .is-hom[]-id → Id'-fibred
    .is-hom[]-∘ → F∘'-fibred

```
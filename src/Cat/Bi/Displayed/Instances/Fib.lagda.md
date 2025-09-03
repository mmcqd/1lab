```agda

open import Cat.Prelude
open import Cat.Bi.Base
open import Cat.Bi.Displayed.Base
open import Cat.Bi.Displayed.Total
open import Cat.Bi.Displayed.Cartesian
open import Cat.Displayed.Base
open import Cat.Displayed.Functor
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Cartesian.Discrete
open import Cat.Displayed.Instances.FullSubcategory
open import Cat.Displayed.Instances.DisplayedFunctor
open import Cat.Displayed.Functor.Naturality
open import Cat.Bi.Displayed.Instances.FullSubBicategory renaming (Birestrict to FullSubBi)
open import Cat.Bi.Displayed.Instances.2FullSubBicategory renaming (Birestrict to 2FullSubBi)


import Cat.Displayed.Reasoning as DR

module Cat.Bi.Displayed.Instances.Fib where

module _ o ℓ o' ℓ' where

  open Bidisplayed
  open Displayed-functor
  open _=[_]=>_
  open make-natural-iso[_]
  open 2-full-sub-bicat

  private module Disp = Bidisplayed (Displayed-cat o ℓ o' ℓ')
```
*Fib*, the displayed bicategory of fibrations, is the 2-full sub-bicategory
of `Displayed-cat` which picks out the cartesian fibrations and 
the fibred functors between them.

```agda 

  Fib : Bidisplayed (Cat o ℓ ) _ _ _
  Fib = 2FullSubBi (Displayed-cat o ℓ o' ℓ') λ where
     .is-ob[] → Cartesian-fibration
     .is-hom[] → is-fibred-functor
     .is-hom[]-id → Id'-fibred
     .is-hom[]-∘ → F∘'-fibred

```

We can also define *DFib*, the displayed bicategory of *discrete* fibrations,
as a full sub-bicategory of `Displayed-cat`.

```agda

  DFib : Bidisplayed (Cat o ℓ) _ _ _
  DFib = FullSubBi (Displayed-cat o ℓ o' ℓ') is-discrete-cartesian-fibration

```
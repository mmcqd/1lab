<!--
```agda
open import Cat.Prelude
open import Cat.Bi.Base
open import Cat.Displayed.Instances.TotalProduct
open import Cat.Displayed.Functor.Naturality
open import Cat.Displayed.Instances.FullSubcategory
open import Cat.Displayed.Functor
open import Cat.Bi.Displayed.Base
```
-->
```agda
module Cat.Bi.Displayed.Instances.FullSubBicategory
  {o oh ℓh o' oh' ℓh'} 
  {B : Prebicategory o oh ℓh}
  (E : Bidisplayed B o' oh' ℓh') 
  where
```
# Full sub-bicategories

A *full sub-bicategory* of a bicategory $\bB$ chooses 
a subset of displayed objects and keeps all displayed 1-cells and 2-cells.

```agda
open Prebicategory B
open Bidisplayed E
open Displayed-functor
open make-natural-iso[_]
open _=[_]=>_

module _ {p} (P : ∀ {x} → Ob[ x ] → Type p) where
  
  Birestrict : Bidisplayed B _ _ _
  Birestrict .Bidisplayed.Ob[_] x = Σ Ob[ x ] P
  Birestrict .Bidisplayed.Hom[_,_] (A , _) (B , _) = Hom[ A , B ]
  Birestrict .Bidisplayed.↦id' = ↦id'
  Birestrict .Bidisplayed.compose' = compose'
  Birestrict .Bidisplayed.unitor-l' = unitor-l'
  Birestrict .Bidisplayed.unitor-r' = unitor-r'
  Birestrict .Bidisplayed.associator' = to-natural-iso' ni where
    ni : make-natural-iso[ _ ] _ _
    ni .eta' _ = α→' _ _ _
    ni .inv' _ = α←' _ _ _
    ni .eta∘inv' _ = associator'.invl' ηₚ' _
    ni .inv∘eta' _ = associator'.invr' ηₚ' _
    ni .natural' _ _ _ = α→nat' _ _ _
  Birestrict .Bidisplayed.triangle' = triangle'
  Birestrict .Bidisplayed.pentagon' = pentagon'

```

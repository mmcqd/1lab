
<!--
```agda
open import Cat.Prelude
open import Cat.Displayed.Base
open import Cat.Displayed.Cartesian

import Cat.Reasoning as CR
import Cat.Displayed.Reasoning as DR
import Cat.Displayed.Morphism as DM
```
-->

```agda 
module Cat.Displayed.Cartesian.Iso where
```

# Isofibrations

*Isofibrations* are a weaker notion of fibration than Cartesian fibrations.
An isofibration has lifts of all isomorphims, but not necessarily lifts of all morphisms.

<!--
```agda 
module _ {o ℓ o' ℓ'} {B : Precategory o ℓ} (E : Displayed B o' ℓ') where

  open CR B
  open DR E
  open DM E
```
-->

```agda
  record Iso-lift {x y} (i : x ≅ y) (y' : Ob[ y ]) : Type (o' ⊔ ℓ') where
    no-eta-equality
    field
      {x'} : Ob[ x ]
      lifting : x' ≅[ i ] y'

  Iso-fibration : Type _
  Iso-fibration = ∀ {x y} (i : x ≅ y) (y' : Ob[ y ]) → Iso-lift i y'
```

<!--
```agda
  module Iso-fibration (fib : Iso-fibration) where
    module _ {x y} (i : x ≅ y) (y' : Ob[ y ]) where
      open Iso-lift (fib i y')
        using ()
        renaming (x' to _^*_; lifting to π*)
        public
```
-->

Every cartesian fibration is an isofibration.

```agda
  Cartesian→Iso : Cartesian-fibration E → Iso-fibration
  Cartesian→Iso fib i y' .Iso-lift.x' = _
  Cartesian→Iso fib i y' .Iso-lift.lifting = invertible[]→iso[] (invertible+cartesian→invertible E (π* (i .to) y') π*.cartesian) 
    where open Cartesian-fibration E fib
```
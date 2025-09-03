---
description: |
  We define the displayed category of elements.
---
<!--
```agda
open import Cat.Displayed.Base
open import Cat.Prelude
```
-->

```agda
module Cat.Displayed.Instances.Elements.Covariant {o ℓ s} (B : Precategory o ℓ)
  (P : Functor B (Sets s)) where
```

<!--
```agda
open Precategory B
open Functor

private
  module P = Functor P
```
-->

```agda
∫ : Displayed B s s
∫ = with-thin-display record where
  Ob[_] X = P ʻ X 
  Hom[_] f P[X] P[Y] = P.₁ f P[X] ≡ P[Y]
  id' = happly P.F-id _
  _∘'_ {x = x} {y} {z} {f} {g} p q = 
    P.₁ (f ∘ g) x ≡⟨ happly (P.F-∘ f g) x ⟩ 
    P.₁ f (P.₁ g x)   ≡⟨ ap (P.₁ f) q ⟩ 
    P.₁ f y           ≡⟨ p ⟩
    z                 ∎ 
```

```agda

open import Cat.Prelude
open import Cat.Displayed.Base
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Total

import Cat.Reasoning as CR
import Cat.Displayed.Morphism as DM

module Cat.Displayed.Instances.FullSubcategory 
  {o ℓ o' ℓ'} 
  {B : Precategory o ℓ}
  (E : Displayed B o' ℓ')
  (let open Displayed E)
  {p} (P : ∀ {x} (x' : Ob[ x ]) → Type p)
  where

open CR B
open DM E

Restrict : Displayed B _ _
Restrict .Displayed.Ob[_] x = Σ Ob[ x ] P
Restrict .Displayed.Hom[_] f (x' , _) (y' , _) = Hom[ f ] x' y'
Restrict .Displayed.Hom[_]-set _ _ _ = hlevel 2
Restrict .Displayed.id' = id'
Restrict .Displayed._∘'_ = _∘'_
Restrict .Displayed.idr' = idr'
Restrict .Displayed.idl' = idl'
Restrict .Displayed.assoc' = assoc'
Restrict .Displayed.hom[_] = hom[_]
Restrict .Displayed.coh[_] = coh[_]

private module Restrict where
  open Displayed Restrict public
  open DM Restrict public


restrict-cartesian : ∀ {a b a' b'} {f : Hom a b} {f' : Restrict.Hom[ f ] a' b'} → is-cartesian E f f' → is-cartesian Restrict {a' = a'} {b' = b'} f f'
restrict-cartesian cart .is-cartesian.universal = cart .is-cartesian.universal
restrict-cartesian cart .is-cartesian.commutes = cart .is-cartesian.commutes
restrict-cartesian cart .is-cartesian.unique = cart .is-cartesian.unique

iso→restrict-iso : ∀ {a b a' b'} {i : a ≅ b} → (a' .fst) ≅[ i ] (b' .fst) →  a' Restrict.≅[ i ] b'
iso→restrict-iso i' = Restrict.make-iso[ _ ] (i' .DM.to') (i' .DM.from') (i' .DM.invl') (i' .DM.invr')

restrict-iso→iso : ∀ {a b a' b'} {i : a ≅ b} →  a' Restrict.≅[ i ] b' → (a' .fst) ≅[ i ] (b' .fst)
restrict-iso→iso i' = make-iso[ _ ] (i' .DM.to') (i' .DM.from') (i' .DM.invl') (i' .DM.invr')

module _ (E* : Cartesian-fibration E) where
  open Cartesian-fibration _ E*

  restrict-fibration : (∀ {x y y'} {f : Hom x y} → P y' → P (f ^* y')) → Cartesian-fibration Restrict
  restrict-fibration p f (y' , Py') .Cartesian-lift.x' = (f ^* y') , p Py'
  restrict-fibration p f (y' , _) .Cartesian-lift.lifting = π* f y'
  restrict-fibration p f (y' , _) .Cartesian-lift.cartesian = restrict-cartesian π*.cartesian

```
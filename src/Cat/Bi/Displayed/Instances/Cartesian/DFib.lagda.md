```agda

open import Cat.Prelude
open import Cat.Bi.Base
open import Cat.Displayed.Base
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Cartesian.Discrete
open import Cat.Displayed.Functor.Cartesian
open import Cat.Displayed.Instances.DisplayedFunctor
open import Cat.Displayed.Instances.TotalProduct
open import Cat.Bi.Displayed.Base
open import Cat.Bi.Displayed.Cartesian
open import Cat.Bi.Displayed.Cartesian.Discrete
open import Cat.Displayed.Base
open import Cat.Displayed.Functor
open import Cat.Displayed.Instances.Pullback
open import Cat.Bi.Displayed.Instances.DFib
open import Cat.Bi.Displayed.Instances.Cartesian.Fib

open import Cat.Displayed.Total hiding (∫ ; πᶠ)

open import Cat.Bi.Displayed.Cartesian.Discrete.Fibre

module Cat.Bi.Displayed.Instances.Cartesian.DFib where

open _=[_]=>_

module _ {o ℓ o' ℓ'} where
  private 
    module Cat = Prebicategory (Cat o ℓ)
    module DFib {o ℓ} = Bidisplayed (DFib o ℓ o' ℓ')

  DFib-2-cart 
    : {A B : Cat.Ob} (A' : DFib.Ob[ A ]) (B' : DFib.Ob[ B ])
    → is-discrete-cartesian-fibration DFib.Hom[ A' , B' ]
  DFib-2-cart A' B' = Disp[]-discrete (B' .snd) 

  open 1-cell (DFib o ℓ o' ℓ') DFib-2-cart
  open is-discrete-cartesian
  open discrete-cartesian-lift

  module _
    {A B}
    (f : A Cat.↦ B)
    (B' : DFib.Ob[ B ])
    where
    private 
      module B = Precategory B
  
      module B' where
        open Displayed (B' .fst) public
        open is-discrete-cartesian-fibration (B' .snd) public
      
    open Displayed-functor

    DFib-1-cart : discrete-cartesian-lift f B'
    DFib-1-cart .A' = Change-of-base f (B' .fst) , Change-of-base-discrete-fibration f (B' .fst) (B' .snd)
    DFib-1-cart .lifting = Change-of-base-functor f (B' .fst)
    DFib-1-cart .cartesian .universal¹ h g' = Factor f (B' .fst) h g'
    DFib-1-cart .cartesian .commutes¹ h g' = Displayed-functor-pathp _ (λ _ → refl) (λ _ → refl)
    DFib-1-cart .cartesian .unique¹ other p = Displayed-functor-pathp _ (λ x' → ap (λ z → z .F₀' x') p) λ _ → prop!
    DFib-1-cart .cartesian .universal² δ σ .η' x' = B'.hom[ B.idr _ ] (σ .η' x')
    DFib-1-cart .cartesian .universal² δ σ .is-natural' _ _ _ = prop!


  DFib-discrete-bifibration : is-discrete-cartesian-bifibration (DFib o ℓ o' ℓ')
  DFib-discrete-bifibration .is-discrete-cartesian-bifibration.2-cart = DFib-2-cart
  DFib-discrete-bifibration .is-discrete-cartesian-bifibration.1-cart = DFib-1-cart

  DFib-cartesian-bifibration : Cartesian-bifibration (DFib o ℓ o' ℓ')
  DFib-cartesian-bifibration = discrete→bifibration _ DFib-discrete-bifibration
``` 

The fibres of `DFib` have a nice property: their slices are are just further discrete fibrations!

One way to think about this is that a discrete fibration is _already_
a kind of slice category. That is, for a precategory A:

DFib A ≅ Cat[ A ^op , Sets ] ~≅∼ Sets / ?A ^op?

This last bit doesn't quite type check...

```agda
-- module _ {o ℓ o' ℓ'} where
  
--   import Cat.Displayed.Cartesian.Discrete.Reasoning as Dcr 
--   import Cat.Reasoning as Cr
--   open import Cat.Functor.Base

--   open Displayed-functor
  
--   -- We have to careful about universe levels here
--   -- DFibs on total categories of _other_ DFibs!
--   -- So the base categories have levels higher than just (o ℓ)
--   private 
--     module DFib {o ℓ} = Bidisplayed (DFib o ℓ o' ℓ')
--     module Disp {o ℓ} = Bidisplayed (Displayed-cat o ℓ o' ℓ')
--     module Cat o ℓ = Prebicategory-Hom-Reasoning (Cat o ℓ)

--   private module _ {o ℓ} {A B : Cat.Ob o ℓ} {A' : DFib.Ob[ A ]} {B' : DFib.Ob[ B ]} where
--     open is-discrete-cartesian-fibration (DFib-2-cart A' B') public
--     open Dcr (DFib-2-cart  A' B') public


--   module _ (A : Cat.Ob o ℓ) where
--     open Cr A

  
--     DSlices : Displayed (Fibre (DFib o ℓ o' ℓ') DFib-2-cart A) _ _
--     DSlices .Displayed.Ob[_] A' = DFib.Ob[ (∫ A') ] 
--     DSlices .Displayed.Hom[_] f a' b' = a' DFib.[ ∫ᶠ f ]↦ b'
--     DSlices .Displayed.Hom[_]-set f a' b' = Displayed-functor-is-set λ _ →  (b' .snd) .is-discrete-cartesian-fibration.fibre-set _ 
--     DSlices .Displayed.id' {a = a} {x = x} = ob[_] {A' = x} {B' = x} hom Disp.↦id' 
--       where
--         hom = Cat.Hom.from $ path→iso $ Functor-path (λ _ → refl) (λ _ → refl)
--     DSlices .Displayed._∘'_ {c = c} {x = x} {y = y} {z = z} f g = ob[_] {A' = x} {B' = z} hom (f Disp.⊗' g) 
--       where
--         module c = is-discrete-cartesian-fibration (c .snd)
--         hom = 
--           Cat.Hom.from $ 
--           path→iso $ 
--           Functor-path 
--             (λ x → refl ,ₚ sym (c.^*-id _)) 
--             (λ f → ∫Hom-pathp _ _ _ refl prop!)
--     DSlices .Displayed.idr' f' = {!   !}
--     DSlices .Displayed.idl' = {!   !}
--     DSlices .Displayed.assoc' = {!   !}
--     DSlices .Displayed.hom[_] = {!   !}
--     DSlices .Displayed.coh[_] = {!   !}
```
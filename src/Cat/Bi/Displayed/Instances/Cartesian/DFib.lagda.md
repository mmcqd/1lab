```agda

open import Cat.Prelude
open import Cat.Bi.Base
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Cartesian.Discrete
open import Cat.Displayed.Functor.Cartesian
open import Cat.Displayed.Instances.DisplayedFunctor
open import Cat.Displayed.Instances.TotalProduct
open import Cat.Bi.Displayed.Base
open import Cat.Bi.Displayed.Cartesian
open import Cat.Bi.Displayed.Discrete
open import Cat.Displayed.Base
open import Cat.Displayed.Functor
open import Cat.Displayed.Instances.Pullback
open import Cat.Bi.Displayed.Instances.Fib
open import Cat.Bi.Displayed.Instances.Cartesian.Fib

module Cat.Bi.Displayed.Instances.Cartesian.DFib {o ℓ o' ℓ'} where

open is-discrete-cartesian-bifibration
open is-discrete-cartesian-fibration
open 1-cell-pre-cartesian-lift
open 1-cell-cartesian-lift
open 1-cell-pre-cartesian
open _=[_]=>_

private 
  module Cat = Prebicategory (Cat o ℓ)
  module DFib = Bidisplayed (DFib o ℓ o' ℓ')

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

  DFib-1-cart : 1-cell-pre-cartesian-lift (DFib _ _ _ _) f B'
  DFib-1-cart .A' = Change-of-base f (B' .fst) , Change-of-base-discrete-fibration f (B' .fst) (B' .snd)
  DFib-1-cart .lifting = Change-of-base-functor f (B' .fst)
  DFib-1-cart .pre-cartesian .universal¹ m h' = Factor f (B' .fst) m h'
  DFib-1-cart .pre-cartesian .commutes¹ m h' = Factor-commutes f (B' .fst) m h'
  DFib-1-cart .pre-cartesian .universal² δ σ .η' x' = B'.hom[ B.idr _ ] (σ .η' x')
  DFib-1-cart .pre-cartesian .universal² δ σ .is-natural' _ _ _ = prop!


DFib-discrete-bifibration : is-discrete-cartesian-bifibration (DFib o ℓ o' ℓ')
DFib-discrete-bifibration .1-cart = DFib-1-cart
DFib-discrete-bifibration .2-cart = {!   !}


``` 
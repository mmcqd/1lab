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
open import Cat.Bi.Displayed.Cartesian.Discrete
open import Cat.Displayed.Base
open import Cat.Displayed.Functor
open import Cat.Displayed.Instances.Pullback
open import Cat.Bi.Displayed.Instances.DFib
open import Cat.Bi.Displayed.Instances.Cartesian.Fib

module Cat.Bi.Displayed.Instances.Cartesian.DFib {o ℓ o' ℓ'} where

open is-discrete-cartesian-bifibration
open is-discrete-cartesian-fibration
open _=[_]=>_


private 
  module Cat = Prebicategory (Cat o ℓ)
  module DFib = Bidisplayed (DFib o ℓ o' ℓ')

DFib-2-cart 
  : ∀ {A B} (A' : DFib.Ob[ A ]) (B' : DFib.Ob[ B ])
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
DFib-discrete-bifibration .2-cart = DFib-2-cart
DFib-discrete-bifibration .1-cart = DFib-1-cart

DFib-cartesian-bifibration : Cartesian-bifibration (DFib o ℓ o' ℓ')
DFib-cartesian-bifibration = discrete→bifibration _ DFib-discrete-bifibration
``` 
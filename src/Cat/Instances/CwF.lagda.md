```agda

open import Cat.Prelude
open import Cat.Functor.Adjoint
open import Cat.Displayed.Base 
open import Cat.Displayed.Total hiding (∫ ; πᶠ)
open import Cat.Displayed.Functor
open import Cat.Displayed.Composition
open import Cat.Bi.Base
open import Cat.Bi.Displayed.Base 
open import Cat.Bi.Displayed.Instances.DFib
open import Cat.Bi.Displayed.Instances.Cartesian.DFib
open import Cat.Bi.Displayed.Cartesian.Discrete 
open import Cat.Bi.Displayed.Cartesian.Discrete.Fibre
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Cartesian.Discrete 

import Cat.Displayed.Cartesian.Discrete.Reasoning as Dcr
import Cat.Bi.Displayed.Cartesian.Discrete.Properties as Dcp
import Cat.Displayed.Reasoning as Dr

module Cat.Instances.CwF where


module DFib-Ob {o ℓ o' ℓ'} {𝒮 : Precategory o ℓ} ((A , A*) : Σ (Displayed 𝒮 o' ℓ') is-discrete-cartesian-fibration) where
  open Dr A public
  open is-discrete-cartesian-fibration A* public
  open Dcr A* public


record CwF o ℓ : Type (lsuc (o ⊔ ℓ)) where
  open Dcp (DFib o ℓ o ℓ) DFib-2-cart  public
  open Prebicategory-Hom-Reasoning (Cat o ℓ) public
  open Bidisplayed-Hom[]-Reasoning (DFib o ℓ o ℓ)  renaming (Ob[_] to DFib[_]) public 
  open is-discrete-cartesian-bifibration (DFib-discrete-bifibration {o} {ℓ} {o} {ℓ}) public

  field
    𝒞 : Precategory o ℓ
    Tp : {!   !}
    -- Tp : DFib[ 𝒞 ]
    -- Chk : DFib[ ∫ Tp ] 
    -- Extension : is-representable Tp Chk


  
```
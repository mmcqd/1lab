open import Cat.Prelude
open import Cat.Bi.Base
open import Cat.Bi.Displayed.Base
open import Cat.Bi.Displayed.Cartesian
open import Cat.Bi.Displayed.Cartesian.Properties
open import Cat.Morphism hiding (Ob ; Hom ; id)

import Cat.Bi.Morphism as BM
import Cat.Bi.Displayed.Morphism as DBM

module Cat.Bi.Displayed.Cartesian.Properties2
  {o oh ℓh o' oh' ℓh'} {B : Prebicategory o oh ℓh} 
  (E : Bidisplayed B o' oh' ℓh')
  where

private module B = Prebicategory B
open Prebicategory B 
open Bidisplayed-Hom[]-Reasoning E
open BM B
open DBM E


module _
  {A B A₁ A₂ B'} {f : A ↦ B} {f₁ : A₁ [ f ]↦ B'} {f₂ : A₂ [ f ]↦ B'}
  (c1 : 1-cell-cartesian E f f₁)
  (c2 : 1-cell-cartesian E f f₂)
  where

  lemma : Hom[].is-invertible[ _ ] {!   !}
  lemma = inv-lift E c1 (record { inv = Hom.id ; inverses = record { invl = Hom.idl _ ; invr = Hom.idl _ } }) (record { inv' = {!   !} ; inverses' = record { invl' = {!   !} ; invr' = {!   !} } })
  -- 1-cell-cartesian-domain-unique = make-isoᵇ[ _ ] {!   !} {!   !} {!   !} {!   !}

-- cartesian-domain-unique
--   : ∀ {x y} {f : Hom x y}
--   → ∀ {x' x'' y'} {f' : Hom[ f ] x' y'} {f'' : Hom[ f ] x'' y'}
--   → is-cartesian f f'
--   → is-cartesian f f''
--   → x' ≅↓ x''


open import Cat.Prelude
open import Cat.Displayed.Base
open import Cat.Bi.Base
open import Cat.Bi.Displayed.Base
open import Cat.Displayed.Cartesian.Discrete
open import Cat.Displayed.Functor.Naturality
open import Cat.Displayed.Instances.DisplayedFunctor
open import Cat.Displayed.Morphism
open import Cat.Displayed.Functor

module Cat.Bi.Displayed.Instances.DFib where

open _=[_]=>_
open make-natural-iso[_]

module _ o ℓ o' ℓ' where

  module DCat = Bidisplayed (Displayed-cat o ℓ o' ℓ')

  DFib : Bidisplayed (Cat o ℓ) _ _ _
  DFib .Bidisplayed.Ob[_] C = Σ (Displayed C o' ℓ') is-discrete-cartesian-fibration
  DFib .Bidisplayed.Hom[_,_] (A , _) (B , _) = DCat.Hom[ A , B ]
  DFib .Bidisplayed.↦id' = DCat.↦id'
  DFib .Bidisplayed.compose' = DCat.compose'
  DFib .Bidisplayed.unitor-l' = DCat.unitor-l'
  DFib .Bidisplayed.unitor-r' = DCat.unitor-r'
  DFib .Bidisplayed.associator' = to-natural-iso' ni where
    -- no-eta-equality means we have to do some manual eta expansion
    ni : make-natural-iso[ _ ] _ _
    ni .eta' = DCat.associator' .to' .η'
    ni .inv' = DCat.associator' .from' .η'
    ni .eta∘inv' x' = apd (λ _ z → z .η' x') $ DCat.associator' .invl'
    ni .inv∘eta' x' = apd (λ _ z → z .η' x') $ DCat.associator' .invr'
    ni .natural' x' y' f' = DCat.associator' .to' .is-natural' x' y' f'
  DFib .Bidisplayed.triangle' f' g' = DCat.triangle' f' g'
  DFib .Bidisplayed.pentagon' f' g' h' i' = DCat.pentagon' f' g' h' i'


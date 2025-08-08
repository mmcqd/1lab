open import Cat.Prelude
open import Cat.Displayed.Base

module Cat.Displayed.Instances.Lift {o ℓ o' ℓ'} {B : Precategory o ℓ} (E : Displayed B o' ℓ') where

open Displayed E

LiftD : ∀ o'' ℓ'' → Displayed B (o' ⊔ o'') (ℓ' ⊔ ℓ'')
LiftD o'' ℓ'' .Displayed.Ob[_] x = Lift o'' Ob[ x ]
LiftD o'' ℓ'' .Displayed.Hom[_] f (lift x') (lift y') = Lift ℓ'' (Hom[ f ] x' y')
LiftD o'' ℓ'' .Displayed.Hom[_]-set _ _ _ = hlevel 2
LiftD o'' ℓ'' .Displayed.id' = lift id'
LiftD o'' ℓ'' .Displayed._∘'_ (lift f') (lift g') = lift (f' ∘' g')
LiftD o'' ℓ'' .Displayed.idr' (lift f') = apd (λ _ → lift) (idr' f')
LiftD o'' ℓ'' .Displayed.idl' (lift f') = apd (λ _ → lift) (idl' f')
LiftD o'' ℓ'' .Displayed.assoc' (lift f') (lift g') (lift h') = apd (λ _ → lift) (assoc' f' g' h')
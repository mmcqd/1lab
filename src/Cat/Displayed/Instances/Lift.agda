
open import Cat.Prelude
open import Cat.Displayed.Base

module Cat.Displayed.Instances.Lift
  {o ℓ o' ℓ'} {B : Precategory o ℓ}
  (E : Displayed B o' ℓ')
  o'' ℓ''
  where

private module E = Displayed E

Lift-disp : Displayed B (o' ⊔ o'') (ℓ' ⊔ ℓ'')
Lift-disp .Displayed.Ob[_] x = Lift (o' ⊔ o'') E.Ob[ x ]
Lift-disp .Displayed.Hom[_] f (lift x') (lift y') = Lift (ℓ' ⊔ ℓ'') (E.Hom[ f ] x' y')
Lift-disp .Displayed.Hom[_]-set _ _ _ = hlevel 2
Lift-disp .Displayed.id' = lift E.id'
Lift-disp .Displayed._∘'_ (lift f') (lift g') = lift (f' E.∘' g')
Lift-disp .Displayed.idr' _ = apd (λ _ → lift) (E.idr' _)
Lift-disp .Displayed.idl' _ = apd (λ _ → lift) (E.idl' _)
Lift-disp .Displayed.assoc' _ _ _ = apd (λ _ → lift) (E.assoc' _ _ _)
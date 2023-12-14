```agda

open import Cat.Prelude
open import Order.Base
open import Order.Cat
open import Data.Power
open import Cat.Functor.Subcategory
open import Cat.Instances.Lift
open import Cat.Functor.Equivalence
open import Cat.Functor.Equivalence.Path

module Order.Instances.Power {ℓ} (X : Type ℓ) where

Power : Poset _ _
Power .Poset.Ob = ℙ X
Power .Poset._≤_ A B = A ⊆ B
Power .Poset.≤-thin = hlevel!
Power .Poset.≤-refl a = λ z → z
Power .Poset.≤-trans f g _ a = g _ (f _ a)
Power .Poset.≤-antisym = ℙ-ext

import Cat.Reasoning (poset→category Power) as Powerℂ

Power-is-category : is-category (poset→category Power)
Power-is-category .to-path x = ℙ-ext (x .Powerℂ.to) (x .Powerℂ.from)
Power-is-category .to-path-over p = Powerℂ.≅-pathp refl _ $ funextP λ a → funextP λ b → path→ua-pathp _ refl

Invert : Monotone Power (Power ^opp)
Invert .hom A x = ¬Ω (A x)
Invert .pres-≤ f a a∉y a∈x = a∉y (f _ a∈x)

Invert⁻ : Monotone (Power ^opp) Power
Invert⁻ .hom A x = ¬Ω (A x)
Invert⁻ .pres-≤ f a a∉y a∈x = a∉y (f _ a∈x)
``` 

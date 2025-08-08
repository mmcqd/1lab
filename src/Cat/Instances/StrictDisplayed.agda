
open import Cat.Prelude
open import Cat.Displayed.Base
open import Cat.Displayed.Functor
open import Cat.Instances.Functor
open import Cat.Displayed.Total
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Reasoning as DR
open import Cat.Displayed.Instances.Pullback

module Cat.Instances.StrictDisplayed where

module _ {o ℓ o' ℓ'} {B : Precategory o ℓ} (D : Displayed B o' ℓ') (let module D = Displayed D) where
  is-strict-displayed : Type _
  is-strict-displayed = ∀ x → is-set D.Ob[ x ]

module _ {o ℓ} (B : Precategory o ℓ) o' ℓ' where


  Strict-disp : Precategory _ _
  Strict-disp .Precategory.Ob = Σ (Displayed B o' ℓ') is-strict-displayed
  Strict-disp .Precategory.Hom (D , _) (E , _) = Vertical-functor D E
  Strict-disp .Precategory.Hom-set _ (_ , Eₛ) = Vertical-functor-is-set Eₛ
  Strict-disp .Precategory.id = Id'
  Strict-disp .Precategory._∘_ = _∘V_
  Strict-disp .Precategory.idr _ = ∘V-idr _
  Strict-disp .Precategory.idl _ = ∘V-idl _
  Strict-disp .Precategory.assoc _ _ _ = ∘V-assoc _ _ _

  -- module _ o'' ℓ'' where

  --   Poly : Displayed Strict-disp _ _
  --   Poly .Displayed.Ob[_] (D , _) = Σ (Displayed (∫ D) o'' ℓ'') is-strict-displayed
  --   Poly .Displayed.Hom[_]  f (D , _) (E , _) = Displayed-functor (F∫ f) D E
  --   Poly .Displayed.Hom[_]-set _ _ (_ , E'ₛ) = Displayed-functor-is-set E'ₛ
  --   Poly .Displayed.id' = F∫Id'
  --   Poly .Displayed._∘'_ = _F∫∘V_
  --   Poly .Displayed.idr' _ = Displayed-functor-pathp _ (λ _ → refl) (λ _ → refl)
  --   Poly .Displayed.idl' _ = Displayed-functor-pathp _ (λ _ → refl) (λ _ → refl)
  --   Poly .Displayed.assoc' _ _ _ = Displayed-functor-pathp _ (λ _ → refl) (λ _ → refl)


-- module _ {o ℓ o' ℓ' o'' ℓ''} {B : Precategory o ℓ} where

--   open Cartesian-lift
--   open is-cartesian
--   open Functor
--   open Displayed-functor
  
--   Poly-cartesian : Cartesian-fibration (Poly B o' ℓ' o'' ℓ'')
--   Poly-cartesian f (y' , y'ₛ) .x' = Change-of-base (F∫ f) y' , λ z → y'ₛ (F₀ (F∫ f) z)
--   Poly-cartesian f (y' , _) .lifting = Change-of-base-functor (F∫ f) y'
--   Poly-cartesian f (y' , _) .cartesian .universal {u' = u' , _} g F' = F where
--     module F' = Displayed-functor F'
--     module y' where
--       open Displayed y' public
--       open DR y' public
--     module u' = Displayed u'

--     F : Displayed-functor (F∫ g) u' (Change-of-base (F∫ f) y')
--     F .F₀' = F'.F₀'
--     F .F₁' = F'.F₁'
--     F .F-id' = y'.cast[] $
--       F'.F₁' u'.id' y'.≡[]⟨ F'.F-id' ⟩
--       y'.id' y'.≡[]⟨ transport-filler _ _ ⟩
--       y'.hom[ sym ((F∫ f) .F-id) ] y'.id' ∎
--     F .F-∘' {f' = f'} {g' = g'} = y'.cast[] $
--       F'.F₁' (f' u'.∘' g') y'.≡[]⟨ F'.F-∘' ⟩
--       F'.F₁' f' y'.∘' F'.F₁' g' y'.≡[]⟨ transport-filler _ _ ⟩
--       y'.hom[ sym ((F∫ f) .F-∘ _ _) ] (F'.F₁' f' y'.∘' F'.F₁' g') ∎

--   Poly-cartesian f y' .cartesian .commutes _ _ = 
--     Displayed-functor-pathp refl (λ _ → refl) (λ _ → refl)
--   Poly-cartesian f y' .cartesian .unique _ p = 
--     Displayed-functor-pathp refl (λ x'' → ap (λ z → z .F₀' x'') p) (λ f' → apd (λ _ z → z .F₁' f') p)



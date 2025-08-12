
open import Cat.Prelude
open import Cat.Displayed.Base
open import Cat.Displayed.Functor
open import Cat.Displayed.Cartesian.Discrete

module Cat.Displayed.Instances.FullSubDisplayed where


module _     
    {o ℓ o' ℓ' ℓP} 
    {B : Precategory o ℓ} 
    (E : Displayed B o' ℓ')
    (let module E = Displayed E)
    (P : ∀ {x} → E.Ob[ x ] → Type ℓP) where
  private
    module B = Precategory B

  Restrict : Displayed B _ _
  Restrict .Displayed.Ob[_] x = Σ (E.Ob[ x ]) P
  Restrict .Displayed.Hom[_] f (x , _) (y , _) = E.Hom[ f ] x y
  Restrict .Displayed.Hom[_]-set _ _ _ = E.Hom[ _ ]-set _ _
  Restrict .Displayed.id' = E.id'
  Restrict .Displayed._∘'_ = E._∘'_
  Restrict .Displayed.idr' = E.idr'
  Restrict .Displayed.idl' = E.idl'
  Restrict .Displayed.assoc' = E.assoc'

module _ 
  {o ℓ o' ℓ' ℓP} 
  {B : Precategory o ℓ} 
  {E : Displayed B o' ℓ'}
  (let module E = Displayed E)
  {P : ∀ {x} → E.Ob[ x ] → Type ℓP}
  {E' : Displayed B o' ℓ'}
  (let module E' = Displayed E')
  where

  open Displayed-functor
  RestrictF : (F : Vertical-functor E E') → Vertical-functor (Restrict E P) E'
  RestrictF F .F₀' = F .F₀' ⊙ fst
  RestrictF F .F₁' = F .F₁'
  RestrictF F .F-id' = F .F-id'
  RestrictF F .F-∘' = F .F-∘'

  ExtendF : (F : Vertical-functor E' E) → (∀ {x} (x' : E'.Ob[ x ]) → P (F .F₀' x')) → Vertical-functor E' (Restrict E P)
  ExtendF F p .F₀' x' = F .F₀' x' , p x'
  ExtendF F p .F₁' = F .F₁'
  ExtendF F p .F-id' = F .F-id'
  ExtendF F p .F-∘' = F .F-∘'

module _ 
  {o ℓ o' ℓ' ℓP} 
  {B : Precategory o ℓ} 
  (let module B = Precategory B)
  {E : Displayed B o' ℓ'}
  (let module E = Displayed E)
  {P : ∀ {x} → E.Ob[ x ] → Type ℓP}
  (E* : is-discrete-cartesian-fibration E)
  (let module E* = is-discrete-cartesian-fibration E*)
  (Pprop : ∀ {x} (x' : E.Ob[ x ]) → is-prop (P x'))
  (pres : ∀ {x y} {f : B.Hom x y} {y' : E.Ob[ y ]} → P y' → P (f E*.^* y'))
  where

  open is-discrete-cartesian-fibration


  Restrict-discrete : is-discrete-cartesian-fibration (Restrict E P)
  Restrict-discrete .fibre-set x = Σ-is-hlevel 2 (hlevel 2) λ _ → is-prop→is-set (Pprop _)
  Restrict-discrete .cart-lift f (y' , Py') .centre .fst = (f E*.^* y') , pres Py'
  Restrict-discrete .cart-lift f y' .centre .snd = E*.π* _ _
  Restrict-discrete .cart-lift f y' .paths ((x' , p) , f') = 
    Σ-prop-path! ((E*.^*-lift f f') ,ₚ is-prop→pathp (λ i → Pprop (E*.^*-lift f f' i)) _ _)

    
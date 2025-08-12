open import Cat.Prelude
open import Cat.Displayed.Base
open import Cat.Displayed.Functor
open import Cat.Displayed.Cartesian.Discrete


module Cat.Displayed.Instances.Product where


module _ 
  {o₁ ℓ₁ o₂ ℓ₂ o₃ ℓ₃} 
  {B : Precategory o₁ ℓ₁}
  (D : Displayed B o₂ ℓ₂) (E : Displayed B o₃ ℓ₃) where
  private module E = Displayed E  
  private module D = Displayed D


  _D×_ : Displayed B (o₂ ⊔ o₃) (ℓ₂ ⊔ ℓ₃)
  _D×_ .Displayed.Ob[_] x = D.Ob[ x ] × E.Ob[ x ]
  _D×_ .Displayed.Hom[_] f (Dx , Ex) (Dy , Ey) = D.Hom[ f ] Dx Dy × E.Hom[ f ] Ex Ey
  _D×_ .Displayed.Hom[_]-set _ _ _ = hlevel 2
  _D×_ .Displayed.id' = D.id' , E.id'
  _D×_ .Displayed._∘'_ (Df' , Ef') (Dg' , Eg') = Df' D.∘' Dg' , Ef' E.∘' Eg'
  _D×_ .Displayed.idr' (Df' , Ef') = D.idr' Df' ,ₚ E.idr' Ef'
  _D×_ .Displayed.idl' (Df' , Ef') = D.idl' Df' ,ₚ E.idl' Ef'
  _D×_ .Displayed.assoc' (Df' , Ef') (Dg' , Eg') (Dh' , Eh') = D.assoc' Df' Dg' Dh' ,ₚ E.assoc' Ef' Eg' Eh'


module _ 
  {o₁ ℓ₁ o₂ ℓ₂ o₃ ℓ₃} 
  {B : Precategory o₁ ℓ₁}
  {D : Displayed B o₂ ℓ₂} {E : Displayed B o₃ ℓ₃} where
  private module D = Displayed D
  private module E = Displayed E  


  Pair' : ∀ {o' l'} {Q : Displayed B o' l'} (p1 : Vertical-functor Q D) (p2 : Vertical-functor Q E) → Vertical-functor Q (D D× E)
  Pair' p1 p2 = V where
    module p1 = Displayed-functor p1
    module p2 = Displayed-functor p2
    V : Vertical-functor _ _
    V .Displayed-functor.F₀' x' = p1.₀' x' , p2.₀' x'
    V .Displayed-functor.F₁' f' = p1.₁' f' , p2.₁' f'
    V .Displayed-functor.F-id' = p1.F-id' ,ₚ p2.F-id'
    V .Displayed-functor.F-∘' =  p1.F-∘' ,ₚ p2.F-∘'
  
  Fst' : Vertical-functor (D D× E) D
  Fst' .Displayed-functor.F₀' = fst
  Fst' .Displayed-functor.F₁' = fst
  Fst' .Displayed-functor.F-id' = refl
  Fst' .Displayed-functor.F-∘' = refl

  Snd' : Vertical-functor (D D× E) E
  Snd' .Displayed-functor.F₀' = snd
  Snd' .Displayed-functor.F₁' = snd
  Snd' .Displayed-functor.F-id' = refl
  Snd' .Displayed-functor.F-∘' = refl

    
  open is-discrete-cartesian-fibration
  D×-discrete : is-discrete-cartesian-fibration D → is-discrete-cartesian-fibration E → is-discrete-cartesian-fibration (D D× E)
  D×-discrete D* E* .fibre-set x = hlevel 2 where
    open is-discrete-cartesian-fibration D*
    open is-discrete-cartesian-fibration E*
  D×-discrete D* E* .cart-lift f (Dy' , Ey') = Equiv→is-hlevel 0 (Σ-swap-Σ e⁻¹) (Σ-is-hlevel 0 (D* .cart-lift f Dy') λ _ → E* .cart-lift f Ey')


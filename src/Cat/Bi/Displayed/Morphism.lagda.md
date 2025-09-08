```agda
open import Cat.Prelude
open import Cat.Displayed.Cartesian.Discrete
open import Cat.Bi.Base
open import Cat.Bi.Displayed.Base
open import Cat.Morphism using (is-invertible ; Inverses)
import Cat.Bi.Morphism
import Cat.Displayed.Morphism
import Cat.Reasoning 


module Cat.Bi.Displayed.Morphism {o oh ℓh o' oh' ℓh'} {X : Prebicategory o oh ℓh} (E : Bidisplayed X o' oh' ℓh') where

open Prebicategory-Hom-Reasoning X
open Bidisplayed-Hom[]-Reasoning E
open Cat.Bi.Morphism X


private variable
  A B C : Ob
  A' B' C' : Ob[ A ]
  f : A ↦ B
  g : B ↦ A


module _ 
  {A B C} {f g : A ↦ B} {α : f ⇒ g} {h : B ↦ C} 
  (inv : is-invertible (Hom _ _) α)
  where
  module inv = is-invertible inv
  ▶-inv : is-invertible (Hom _ _) (h ▶ α)
  ▶-inv .is-invertible.inv = h ▶ inv.inv
  ▶-inv .is-invertible.inverses .Inverses.invl = 
    sym (compose.F-∘ _ _) ∙∙ ap₂ (λ x y → x ◆ y) (Hom.idl _) inv.invl ∙∙ compose.F-id
  ▶-inv .is-invertible.inverses .Inverses.invr = 
    sym (compose.F-∘ _ _) ∙∙ ap₂ (λ x y → x ◆ y) (Hom.idl _) inv.invr ∙∙ compose.F-id



record Inversesᵇ[_] (i : Inversesᵇ f g) (f' : A' [ f ]↦ B') (g' : B' [ g ]↦ A') : Type ℓh' where
  open Inversesᵇ i
  field
    invl' : ↦id' Hom[].≅[ invl ] (f' ⊗' g')
    invr' : ↦id' Hom[].≅[ invr ] (g' ⊗' f')

record is-invertibleᵇ[_] (i : is-invertibleᵇ f) (f' : A' [ f ]↦ B') : Type (oh' ⊔ ℓh') where
  open is-invertibleᵇ i
  field
    inv' : B' [ inv ]↦ A'
    inverses' : Inversesᵇ[ inverses ] f' inv'

  open Inversesᵇ[_] inverses' public

  op' : is-invertibleᵇ[ op ] inv'
  op' .inv' = f'
  op' .inverses' .Inversesᵇ[_].invl' = invr'
  op' .inverses' .Inversesᵇ[_].invr' = invl'

record _≅ᵇ[_]_ (A' : Ob[ A ]) (i : A ≅ᵇ B)  (B' : Ob[ B ]) : Type (oh' ⊔ ℓh') where
  open _≅ᵇ_ i
  field
    to'       : A' [ to   ]↦ B'
    from'     : B' [ from ]↦ A'
    inverses' : Inversesᵇ[ inverses ] to' from'
  
  open Inversesᵇ[_] inverses' public

{-# INLINE _≅ᵇ[_]_.constructor #-}

_≅ᵇ↓_ : (A₁ A₂ : Ob[ A ]) → Type _
A₁ ≅ᵇ↓ A₂ = A₁ ≅ᵇ[ id-isoᵇ ] A₂

make-isoᵇ[_] 
  : (i : A ≅ᵇ B) (let module i = _≅ᵇ_ i)
  → (to' : A' [ i.to ]↦ B')
  → (from' : B' [ i.from ]↦ A')
  → ↦id' Hom[].≅[ i.invl ] (to' ⊗' from')
  → ↦id' Hom[].≅[ i.invr ] (from' ⊗' to')
  → A' ≅ᵇ[ i ] B'
{-# INLINE make-isoᵇ[_] #-}
make-isoᵇ[ i ] to' from' invl' invr' = record
  { to' = to'
  ; from' = from'
  ; inverses' = record { invl' = invl' ; invr' = invr' }
  }
```
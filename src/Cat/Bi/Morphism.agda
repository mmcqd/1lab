open import Cat.Prelude
open import Cat.Bi.Base
import Cat.Reasoning 

module Cat.Bi.Morphism {o oh ℓh} (X : Prebicategory o oh ℓh) where

open Prebicategory X

private variable
    A B C : Ob

record Inversesᵇ (f : A ↦ B) (g : B ↦ A) : Type ℓh where
  no-eta-equality
  field
    invl : id Hom.≅ (f ⊗ g)
    invr : id Hom.≅ (g ⊗ f)
  
record is-invertibleᵇ (f : A ↦ B) : Type (oh ⊔ ℓh) where
  no-eta-equality
  field
    inv : B ↦ A
    inverses : Inversesᵇ f inv
  
  open Inversesᵇ inverses public

  op : is-invertibleᵇ inv
  op .inv = f
  op .inverses .Inversesᵇ.invl = invr
  op .inverses .Inversesᵇ.invr = invl

record _≅ᵇ_ (A B : Ob) : Type (oh ⊔ ℓh) where
  no-eta-equality
  field
    to   : A ↦ B
    from : B ↦ A 
    inverses : Inversesᵇ to from

  open Inversesᵇ inverses public

{-# INLINE _≅ᵇ_.constructor #-}

make-isoᵇ : (to : A ↦ B) (from : B ↦ A) → id Hom.≅ (to ⊗ from) → id Hom.≅ (from ⊗ to) → A ≅ᵇ B
{-# INLINE make-isoᵇ #-}
make-isoᵇ to from invl invr = record { to = to ; from = from ; inverses = record { invl = invl ; invr = invr } }


id-isoᵇ : A ≅ᵇ A
id-isoᵇ ._≅ᵇ_.to = id
id-isoᵇ ._≅ᵇ_.from = id
id-isoᵇ ._≅ᵇ_.inverses .Inversesᵇ.invl = λ≅ id
id-isoᵇ ._≅ᵇ_.inverses .Inversesᵇ.invr = ρ≅ id
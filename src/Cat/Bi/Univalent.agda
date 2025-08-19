
open import Cat.Prelude
open import Cat.Bi.Base
import Cat.Bi.Morphism

module Cat.Bi.Univalent {o oh ℓh} (B : Prebicategory o oh ℓh) where

open Prebicategory B
open Cat.Bi.Morphism B

is-category-locally : Type _
is-category-locally = ∀ {a b} → is-category (Hom a b)

record is-bicategory : Type {!   !} where
  field
    locally-univalent  : is-category-locally
    globally-univalent : is-identity-system _≅ᵇ_ λ a → id-isoᵇ
    
-- is-bicategory : Type _
-- is-bicategory = is-identity-system _≅ᵇ_ λ a → id-isoᵇ

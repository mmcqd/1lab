<!--
```agda
open import Cat.Prelude

open import Order.Base
open import Data.Id.Base
open import Cat.Diagram.Coproduct.Indexed

import Order.Reasoning as Pr
open Indexed-coproduct
open is-indexed-coproduct

```
-->

```agda
module Order.Instances.Disjoint where
```

# Indexed coproducts of posets

The coproduct of a family $F$ of [[partially ordered sets]] $\prod_{i : I} P_i$ is a
poset, for any set $I$. Specifically it is the disjoint union of all the
posets in the family.

[partially ordered sets]: Order.Base.html

<!--
```agda
module _ {ℓ ℓₐ ℓᵣ} (I : Set ℓ) (F : ⌞ I ⌟ → Poset ℓₐ ℓᵣ) where
```
-->

```agda
  open module PrF {i : ⌞ I ⌟} = Pr (F i)
  
  _≤[_]'_ : {i j : ⌞ I ⌟} → ⌞ F i ⌟ → (i ≡ᵢ j) → ⌞ F j ⌟ → Type ℓᵣ
  (x ≤[ p ]' y) = substᵢ (λ e → ⌞ F e ⌟) p x ≤ y

  Disjoint : Poset (ℓ ⊔ ℓₐ) (ℓ ⊔ ℓᵣ)
  Disjoint = po module Disjoint where      
    po : Poset _ _
    po .Poset.Ob = Σ[ i ∈ ⌞ I ⌟ ] ⌞ F i ⌟
    po .Poset._≤_ (i , x) (j , y) = Σ[ p ∈ i ≡ᵢ j ] x ≤[ p ]' y
    po .Poset.≤-thin = hlevel!
    po .Poset.≤-refl = reflᵢ , ≤-refl
    po .Poset.≤-trans (reflᵢ , x≤y) (reflᵢ , y≤z) = reflᵢ , (≤-trans x≤y y≤z)
    po .Poset.≤-antisym {i , x} {.i , y} (reflᵢ , x≤y) (p , y≤x) = 
      Σ-pathp refl $ 
        ≤-antisym x≤y $
          ≤-trans (path→≤ $ substᵢ-filler-set hlevel! p y) y≤x

_≤[_]_ : ∀ {ℓ ℓₐ ℓᵣ} {I : Set ℓ} {F : ⌞ I ⌟ → Poset ℓₐ ℓᵣ} {i j : ⌞ I ⌟} → ⌞ F i ⌟ → (i ≡ᵢ j) → ⌞ F j ⌟ → Type ℓᵣ
_≤[_]_ {I = I} {F = F} x p y = _≤[_]'_ I F x p y


{-# DISPLAY _≤[_]'_ I F x p y = x ≤[ p ] y #-}
{-# DISPLAY Disjoint.po I F = Disjoint I F #-}
```

<!--
```agda
module _ {ℓ ℓₐ ℓᵣ} {I : Set ℓ} {F : ⌞ I ⌟ → Poset ℓₐ ℓᵣ} where
```
-->

```agda
  Injᵖ : (i : ⌞ I ⌟) → Monotone (F i) (Disjoint I F)
  Injᵖ i .hom x = (i , x)
  Injᵖ i .pres-≤ x≤y = reflᵢ , x≤y

  Matchᵖ : ∀ {o ℓ} {R : Poset o ℓ} → (∀ i → Monotone (F i) R) → Monotone (Disjoint I F) R
  Matchᵖ c .hom (i , x) = c i # x
  Matchᵖ c .pres-≤ {i , x} {.i , y} (reflᵢ , x≤y) = c i .pres-≤ x≤y

```

Using this, we can show that $\Pos$ has all $\Set$-indexed coproducts.

```agda

Posets-has-set-indexed-coproducts : ∀ {o ℓ κ} (I : Set κ) → has-coproducts-indexed-by (Posets (o ⊔ κ) (ℓ ⊔ κ)) ⌞ I ⌟
Posets-has-set-indexed-coproducts I F .ΣF = Disjoint I F
Posets-has-set-indexed-coproducts I F .ι = Injᵖ
Posets-has-set-indexed-coproducts I F .has-is-ic .match = Matchᵖ
Posets-has-set-indexed-coproducts I F .has-is-ic .commute = trivial!
Posets-has-set-indexed-coproducts I F .has-is-ic .unique f p = ext λ where
  (i , x) → happly (ap hom (p i)) x
  
```

## Binary coproducts are a special case of indexed coproducts

```agda

open import Data.Bool
open import Data.Sum
open import Order.Instances.Coproduct renaming (Matchᵖ to Match⊎ᵖ)
open import Order.Univalent

open import Cat.Morphism
open Inverses

⊎≡Disjoint-bool : ∀ {o ℓ} (P Q : Poset o ℓ) → P ⊎ᵖ Q ≡ Disjoint (el! Bool) (if_then P else Q)
⊎≡Disjoint-bool P Q = Poset-path λ where 
  .to → Match⊎ᵖ (Injᵖ true) (Injᵖ false)
  .from → Matchᵖ (Bool-elim _ Inlᵖ Inrᵖ)
  .inverses .invl → ext λ where 
    (true , x) → refl
    (false , x) → refl
  .inverses .invr → ext λ where 
    (inl x) → refl
    (inr x) → refl
``` 
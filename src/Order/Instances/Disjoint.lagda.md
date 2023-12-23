<!--
```agda
open import Cat.Prelude

open import Order.Base
open import Order.Displayed
open import Order.Instances.Discrete
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

The coproduct of a family $F$ of [[partially ordered sets]] $\prod_{i : I} F_i$ is a
poset, for any set $I$. Specifically it is the disjoint union of all the
posets in the family.

[partially ordered sets]: Order.Base.html

<!--
```agda
module _ {ℓ ℓₐ ℓᵣ} (I : Set ℓ) (F : ⌞ I ⌟ → Poset ℓₐ ℓᵣ) where
```
-->

```agda
  private
    open module F {i : ⌞ I ⌟} = Pr (F i)
    ⌞F⌟ : ⌞ I ⌟ → Type ℓₐ
    ⌞F⌟ e = ⌞ F e ⌟

  Substᵖ : ∀ {i j} → i ≡ j → Monotone (F i) (F j)
  Substᵖ p .hom x = subst ⌞F⌟ p x
  Substᵖ p .pres-≤ {x} {y} x≤y = 
    J (λ j p → subst ⌞F⌟ p x ≤ subst ⌞F⌟ p y) 
    (sym Regularity.reduce! ▶ x≤y ◀ sym Regularity.reduce!) p


  _≤[_]'_ : {i j : ⌞ I ⌟} → ⌞ F i ⌟ → (i ≡ j) → ⌞ F j ⌟ → Type ℓᵣ
  (x ≤[ p ]' y) = subst ⌞F⌟ p x ≤ y
  
  ≤[J] : ∀ {ℓ} {i} (P : ∀ j (p : i ≡ j) {x : ⌞F⌟ i} {y : ⌞F⌟ j} → x ≤[ p ]' y → Type ℓ) → (∀ {x y : ⌞F⌟ i} (x≤y : x ≤[ refl ]' y) → P i refl x≤y) → ∀ {j} (p : i ≡ j) {x : ⌞F⌟ i} {y : ⌞F⌟ j} (x≤y : x ≤[ p ]' y) → P j p x≤y
  ≤[J] {i = i} P r = J (λ j p → {x : ⌞F⌟ i} {y : ⌞F⌟ j} (x≤y : x ≤[ p ]' y) → P j p x≤y) r

  _≤∙_ : ∀ {i j k} {p : i ≡ j} {q : j ≡ k} {x : ⌞ F i ⌟} {y : ⌞ F j ⌟} {z : ⌞ F k ⌟} → x ≤[ p ]' y → y ≤[ q ]' z → x ≤[ p ∙ q ]' z
  _≤∙_ {p = p} {q = q} {x} {y} {z} x≤y y≤z =
    subst ⌞F⌟ (p ∙ q) x =⟨ subst-∙ ⌞F⌟ p q x ⟩ 
    subst ⌞F⌟ q (subst ⌞F⌟ p x) ≤⟨ Substᵖ q .pres-≤ x≤y ⟩ 
    subst ⌞F⌟ q y ≤⟨ y≤z ⟩ 
    z ≤∎

  Disjoint' : Displayed _ _ (Disc I)
  Disjoint' .Displayed.Ob[_] = ⌞F⌟
  Disjoint' .Displayed.Rel[_] p x y = x ≤[ p ]' y
  Disjoint' .Displayed.≤-refl' = path→≤ Regularity.reduce!
  Disjoint' .Displayed.≤-thin' p = hlevel!
  Disjoint' .Displayed.≤-trans' = _≤∙_
  Disjoint' .Displayed.≤-antisym' {x' = x'} {y' = y'} x≤y y≤x = 
    sym Regularity.reduce! ∙ (≤-antisym x≤y $
      Regularity.reduce! ▶ y≤x ◀ sym Regularity.reduce!
    )

  Disjoint : Poset _ _
  Disjoint = ∫ Disjoint'

  private
    module Disjoint = Poset Disjoint

  -- ≤[J] : ∀ {i} {x : ⌞F⌟ i} (p : i ≡ j) (x ≤[ refl ]' y) → (i , x) Disjoint.≤ (j , y)
  -- ≤[j] = ?


_≤[_]_ : ∀ {ℓ ℓₐ ℓᵣ} {I : Set ℓ} {F : ⌞ I ⌟ → Poset ℓₐ ℓᵣ} {i j : ⌞ I ⌟} → ⌞ F i ⌟ → (i ≡ j) → ⌞ F j ⌟ → Type ℓᵣ
_≤[_]_ {I = I} {F = F} x p y = _≤[_]'_ I F x p y


{-# DISPLAY _≤[_]'_ I F x p y = x ≤[ p ] y #-}
```

<!--
```agda
module _ {ℓ ℓₐ ℓᵣ} {I : Set ℓ} {F : ⌞ I ⌟ → Poset ℓₐ ℓᵣ} where
  private 
    
    open module F {i : ⌞ I ⌟} = Pr (F i)
    
    ⌞F⌟ : ⌞ I ⌟ → Type ℓₐ
    ⌞F⌟ e = ⌞ F e ⌟
```
-->

```agda
  Injᵖ : (i : ⌞ I ⌟) → Monotone (F i) (Disjoint I F)
  Injᵖ i .hom x = (i , x)
  Injᵖ i .pres-≤ x≤y = refl , sym Regularity.reduce! ▶ x≤y

  Matchᵖ : ∀ {o ℓ} {R : Poset o ℓ} → (∀ i → Monotone (F i) R) → Monotone (Disjoint I F) R
  Matchᵖ c .hom (i , x) = c i # x
  Matchᵖ {R = R} c .pres-≤ {i , x} {j , y} (p , x≤y) = lemma p x≤y
    where 
      module R = Pr R
      lemma : ∀ {i j} (p : i ≡ j) {x : ⌞ F i ⌟} {y : ⌞ F j ⌟} →  Disjoint' I F .Displayed.Rel[_] p x y → (c i # x) R.≤ (c j # y)
      lemma {i} {j} = J (λ j p → {x : ⌞ F i ⌟} {y : ⌞ F j ⌟} →  Disjoint' I F .Displayed.Rel[_] p x y → (c i # x) R.≤ (c j # y)) 
        λ x≤y → c i .pres-≤ (Regularity.reduce! ▶ x≤y)


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

<!--
```agda
open import Cat.Prelude

open import Cat.Functor.Subcategory
open import Order.DCPO
open import Order.Base
open import Order.Displayed
open import Cat.Diagram.Coproduct
open import Cat.Diagram.Coproduct.Indexed
open import Cat.Diagram.Initial
-- open import Order.Instances.Coproduct
open import Data.Sum

open import 1Lab.Reflection.Marker

open import Order.Instances.Disjoint hiding (_≤[_]_)

import Order.Diagram.Lub
import Order.Reasoning

open Indexed-coproduct
open is-indexed-coproduct
open Subcat-hom

```
-->


```agda
module Order.DCPO.Disjoint where
```

<!--
```agda
_ = DCPOs
``` 
-->

# Indexed coproducts of DCPOs

If $F_i$ is a family of [[DCPO]]s indexed by a [[set]] $I$,
then we can show that there is a universal way to form a [[DCPO]]
out of this family, by taking the underlying [[poset]] to be
the [[indexed coproduct]] of the underyling posets of the family.

[DCPOs]: Order.DCPO
[indexed coproduct]: Order.Instances.Disjoint

```agda
module _ {o ℓ κ} (I : Set κ) (F : ⌞ I ⌟ → DCPO (o ⊔ κ) (ℓ ⊔ κ)) where
  private

    Fᵖ = fst ⊙ F
    
    ⌞F⌟ = ⌞_⌟ ⊙ Fᵖ

    open is-dcpo
    open is-directed-family

    
    module F {i : ⌞ I ⌟} where
      open DCPO (F i) public
      open Order.Diagram.Lub poset public
      open Lub public
      open is-lub public

    _≤[_]_ : {i j : ⌞ I ⌟} → ⌞F⌟ i → i ≡ᵢ j → ⌞F⌟ j → Type _
    _≤[_]_ x p y = substᵢ ⌞F⌟ p x F.≤ y
    
    module ΣFᵖ where
      open Order.Reasoning (Disjoint I Fᵖ) public hiding (≤-refl')
      open Order.Diagram.Lub (Disjoint I Fᵖ) public
      open Indexed-coproduct (Posets-has-set-indexed-coproducts {o} {ℓ} I Fᵖ) public
      open Lub public
      open is-lub public
      open Displayed (Disjoint-over I Fᵖ) public

    open ΣDirected {o} {ℓ} {κ} I Fᵖ

    ΣFᵖ = Disjoint I Fᵖ



  Disjoint-Lub : {A : Type _} (s : A → ΣFᵖ.Ob) → is-directed-family ΣFᵖ s → A → restrict-Σ-directed s → ΣFᵖ.Lub s
  Disjoint-Lub s dir a (i , f , f-inj , f-dir) .ΣFᵖ.lub = i , F.⋃ f f-dir
  Disjoint-Lub s dir a (i , f , reflᵢ , f-dir) .ΣFᵖ.has-lub .ΣFᵖ.fam≤lub b = reflᵢ , F.fam≤⋃ f f-dir b
  Disjoint-Lub s dir a (i , f , reflᵢ , f-dir) .ΣFᵖ.has-lub .ΣFᵖ.least (j , y) le with le a
  ... | reflᵢ , fa≤y = reflᵢ , F.⋃-least f f-dir y λ b → substᵢ-filler-set ⌞F⌟ hlevel! _ _ F.▶ le b .snd

  ΣFᵖ-is-dcpo : is-dcpo ΣFᵖ
  ΣFᵖ-is-dcpo .directed-lubs s dir = ∥-∥-rec₂! (Disjoint-Lub s dir) (dir .elt) (Σ-directed→restricted s dir)

  DCPOs-has-set-indexed-coproducts : Indexed-coproduct (DCPOs (o ⊔ κ) (ℓ ⊔ κ)) F
  DCPOs-has-set-indexed-coproducts .ΣF = ΣFᵖ , ΣFᵖ-is-dcpo
  DCPOs-has-set-indexed-coproducts .ι i .Subcat-hom.hom = injᵖ i
  DCPOs-has-set-indexed-coproducts .ι i .witness {Ix = A} s dir lub is-lub = ∥-∥-rec! is-cont (dir .elt) where
    is-cont : A → ΣFᵖ.is-lub _ _
    is-cont a .ΣFᵖ.fam≤lub b = reflᵢ , is-lub .F.fam≤lub b
    is-cont a .ΣFᵖ.least (j , y) le with le a
    ... | reflᵢ , sa≤y = reflᵢ , is-lub .F.least y λ b → substᵢ-filler-set ⌞F⌟ hlevel! _ _ F.▶ le b .snd
  DCPOs-has-set-indexed-coproducts .has-is-ic .match cases .hom = matchᵖ (hom ⊙ cases)
  DCPOs-has-set-indexed-coproducts .has-is-ic .match {Y = Y} cases .witness {Ix = A} s dir = ∥-∥-rec₂! is-cont (dir .elt) (Σ-directed→restricted s dir) 
    where
      module Y where
        open DCPO Y public
        open Order.Diagram.Lub poset public
        open Lub public
        open is-lub public

      is-cont : A → restrict-Σ-directed s → (lub : ΣFᵖ.Ob) → ΣFᵖ.is-lub s lub → Y.is-lub _ _ 
      is-cont a (i , f , reflᵢ , f-dir) (j , y) is-lub with is-lub .ΣFᵖ.fam≤lub a
      ... | (reflᵢ , fa≤y) = cases i .witness f f-dir y λ where 
        .Y.fam≤lub b → substᵢ-filler-set ⌞F⌟ hlevel! _ _ F.▶ is-lub .ΣFᵖ.fam≤lub b .snd
        .Y.least ub' le → substᵢ-filler-set ⌞F⌟ hlevel! _ _ F.▶ is-lub .ΣFᵖ.least (i , ub') (λ b → reflᵢ , le b) .snd
        
  DCPOs-has-set-indexed-coproducts .has-is-ic .commute = trivial!
  DCPOs-has-set-indexed-coproducts .has-is-ic .unique f p = ext λ (i , y) → p i #ₚ y
```

 
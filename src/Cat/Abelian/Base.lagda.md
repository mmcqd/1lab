```agda
open import Algebra.Magma.Unital
open import Algebra.Group.Ab
open import Algebra.Prelude
open import Algebra.Monoid
open import Algebra.Group

open import Cat.Diagram.Equaliser.Kernel

import Algebra.Group.Cat.Base as Grp

module Cat.Abelian.Base where
```

# Abelian categories

This module defines the sequence of properties which "work up to"
abelian categories: Ab-enriched categories, pre-additive categories,
pre-abelian categories, and abelian categories. Each concept builds on
the last by adding a new categorical property on top of a precategory.

## Ab-enriched categories

An $\Ab$-enriched category is one where each $\hom$ set carries the
structure of an [Abelian group], such that the composition map is
_bilinear_, hence extending to an Abelian group homomorphism

$$
\hom(b, c) \otimes \hom(a, b) \to \hom(a, c)\text{,}
$$

where the term on the left is the [tensor product] of the corresponding
$\hom$-groups. As the name implies, every such category has a canonical
$\Ab$-enrichment (made monoidal using $- \otimes -$), but we do not use
the language of enriched category theory in our development of Abelian
categories.

[zero object]: Cat.Diagram.Zero.html
[Abelian group]: Algebra.Group.Ab.html
[tensor product]: Algebra.Group.Ab.html#the-tensor-product

```agda
record Ab-category {o ℓ} (C : Precategory o ℓ) : Type (o ⊔ lsuc ℓ) where
  open Cat C public
  field
    Group-on-hom : ∀ A B → Group-on (Hom A B)

  _+_ : ∀ {A B} (f g : Hom A B) → Hom A B
  f + g = Group-on-hom _ _ .Group-on._⋆_ f g

  0m : ∀ {A B} → Hom A B
  0m = Group-on-hom _ _ .Group-on.unit

  field
    Hom-grp-ab : ∀ A B (f g : Hom A B) → f + g ≡ g + f

  Hom-grp : ∀ A B → AbGroup ℓ
  Hom-grp A B = (Hom A B , Group-on-hom A B) , Hom-grp-ab A B

  field
    -- Composition is multilinear:
    ∘-linear-l
      : ∀ {A B C} (f g : Hom B C) (h : Hom A B)
      → (f ∘ h) + (g ∘ h) ≡ (f + g) ∘ h
    ∘-linear-r
      : ∀ {A B C} (f : Hom B C) (g h : Hom A B)
      → (f ∘ g) + (f ∘ h) ≡ f ∘ (g + h)

  ∘map : ∀ {A B C} → Ab.Hom (Hom-grp B C ⊗ Hom-grp A B) (Hom-grp A C)
  ∘map {A} {B} {C} =
    from-multilinear-map {A = Hom-grp B C} {B = Hom-grp A B} {C = Hom-grp A C}
      _∘_
      (λ f g h → sym (∘-linear-l _ _ _))
      (λ f g h → sym (∘-linear-r _ _ _))

  module Hom {A B} = AbGrp (Hom-grp A B)
  open Hom
    using (zero-diff)
    renaming (_—_ to _-_)
    public
```

Note that from multilinearity of composition, it follows that $0f = f0 =
0$:

```agda
  ∘-zero-r : ∀ {A B C} {f : Hom B C} → f ∘ 0m {A} {B} ≡ 0m
  ∘-zero-r {f = f} =
    f ∘ 0m                     ≡⟨ Hom.intror Hom.inverser ⟩
    f ∘ 0m + (f ∘ 0m - f ∘ 0m) ≡⟨ Hom.associative ⟩
    (f ∘ 0m + f ∘ 0m) - f ∘ 0m ≡⟨ ap (_- f ∘ 0m) (∘-linear-r _ _ _) ⟩
    (f ∘ (0m + 0m)) - f ∘ 0m   ≡⟨ ap ((_- f ∘ 0m) ⊙ (f ∘_)) Hom.idl ⟩
    (f ∘ 0m) - f ∘ 0m          ≡⟨ Hom.inverser ⟩
    0m                         ∎

  ∘-zero-l : ∀ {A B C} {f : Hom A B} → 0m ∘ f ≡ 0m {A} {C}
  ∘-zero-l {f = f} =
    0m ∘ f                                   ≡⟨ Hom.introl Hom.inversel ⟩
    (Hom.inverse (0m ∘ f) + 0m ∘ f) + 0m ∘ f ≡⟨ sym Hom.associative ⟩
    Hom.inverse (0m ∘ f) + (0m ∘ f + 0m ∘ f) ≡⟨ ap (Hom.inverse (0m ∘ f) +_) (∘-linear-l _ _ _) ⟩
    Hom.inverse (0m ∘ f) + ((0m + 0m) ∘ f)   ≡⟨ ap ((Hom.inverse (0m ∘ f) +_) ⊙ (_∘ f)) Hom.idl ⟩
    Hom.inverse (0m ∘ f) + (0m ∘ f)          ≡⟨ Hom.inversel ⟩
    0m                                       ∎
```

Before moving on, we note the following property of $\Ab$-categories: If
$A$ is an object s.t. $\id{id}_{A} = 0$, then $A$ is a zero object.

```agda
module _ {o ℓ} {C : Precategory o ℓ} (A : Ab-category C) where
  private module A = Ab-category A

  id-zero→zero : ∀ {A} → A.id {A} ≡ A.0m → A.is-zero A
  id-zero→zero idm .A.is-zero.has-is-initial B = contr A.0m λ h → sym $
    h                                ≡⟨ A.intror refl ⟩
    h A.∘ A.id                       ≡⟨ A.refl⟩∘⟨ idm ⟩
    h A.∘ A.0m                       ≡⟨ A.∘-zero-r ⟩
    A.0m                             ∎
  id-zero→zero idm .A.is-zero.has-is-terminal x = contr A.0m λ h → sym $
    h                              ≡⟨ A.introl refl ⟩
    A.id A.∘ h                     ≡⟨ idm A.⟩∘⟨refl ⟩
    A.0m A.∘ h                     ≡⟨ A.∘-zero-l ⟩
    A.0m                           ∎
```

Perhaps the simplest example of an $\Ab$-category is.. any ring! In the
same way that a monoid is a category with one object, and a group is a
groupoid with one object, a ring is a _ringoid_ with one object; Ringoid
being another word for $\Ab$-category, rather than a horizontal
categorification of the drummer for the Beatles. The next simplest
example is $\Ab$ itself:

```agda
module _ where
  open Ab-category
  Ab-ab-category : ∀ {ℓ} → Ab-category (Ab ℓ)
  Ab-ab-category .Group-on-hom A B = Hom-group A B .object .snd
  Ab-ab-category .Hom-grp-ab A B = Hom-group A B .witness
  Ab-ab-category .∘-linear-l f g h = Grp.Forget-is-faithful refl
  Ab-ab-category .∘-linear-r f g h = Grp.Forget-is-faithful $ funext λ x →
    sym (f .snd .Group-hom.pres-⋆ _ _)
```

# Additive categories

An $\Ab$-category is **additive** when its underlying category has a
terminal object and finite products; By the yoga above, this implies
that the terminal object is also a zero object, and the finite products
coincide with finite coproducts.

```agda
record is-additive {o ℓ} (C : Precategory o ℓ) : Type (o ⊔ lsuc ℓ) where
  field has-ab : Ab-category C
  open Ab-category has-ab public

  field
    has-terminal : Terminal
    has-prods    : ∀ A B → Product A B

  ∅ : Zero
  ∅ .Zero.∅ = has-terminal .Terminal.top
  ∅ .Zero.has-is-zero = id-zero→zero has-ab $
    is-contr→is-prop (has-terminal .Terminal.has⊤ _) _ _
  module ∅ = Zero ∅
```

Coincidence of finite products and finite coproducts leads to an object
commonly called a (finite) **biproduct**. The coproduct coprojections
are given by the pair of maps

$$
\begin{align*}
&(\id{id} \times 0) : A \to A \times B \\
&(0 \times \id{id}) : B \to A \times B\text{,}
\end{align*}
$$

respectively, and the comultiplication of $f$ and $g$ is given by
$f\pi_1 + g\pi_2$. We can calculate, for the first coprojection followed
by comultiplication,

$$
\begin{align*}
& (f\pi_1+g\pi_2)(\id{id}\times 0) \\
=& f\pi_1(\id{id}\times 0) + g\pi_2(\id{id}\times 0) \\
=& f\id{id} + g0 \\
=& f\times{,}
\end{align*}
$$

and analogously for the second coprojection followed by
comultiplication.

```agda
  has-coprods : ∀ A B → Coproduct A B
  has-coprods A B = coprod where
    open Coproduct
    open is-coproduct
    module Prod = Product (has-prods A B)
    coprod : Coproduct A B
    coprod .coapex = Prod.apex
    coprod .in₀ = Prod.⟨ id , 0m ⟩
    coprod .in₁ = Prod.⟨ 0m , id ⟩
    coprod .has-is-coproduct .[_,_] f g = f ∘ Prod.π₁ + g ∘ Prod.π₂
    coprod .has-is-coproduct .in₀∘factor {inj0 = inj0} {inj1} =
      (inj0 ∘ Prod.π₁ + inj1 ∘ Prod.π₂) ∘ Prod.⟨ id , 0m ⟩ ≡⟨ sym (∘-linear-l _ _ _) ⟩
      ((inj0 ∘ Prod.π₁) ∘ Prod.⟨ id , 0m ⟩ + _)            ≡⟨ Hom.elimr (pullr Prod.π₂∘factor ∙ ∘-zero-r) ⟩
      (inj0 ∘ Prod.π₁) ∘ Prod.⟨ id , 0m ⟩                  ≡⟨ cancelr Prod.π₁∘factor ⟩
      inj0                                                ∎
    coprod .has-is-coproduct .in₁∘factor {inj0 = inj0} {inj1} =
      (inj0 ∘ Prod.π₁ + inj1 ∘ Prod.π₂) ∘ Prod.⟨ 0m , id ⟩ ≡⟨ sym (∘-linear-l _ _ _) ⟩
      (_ + (inj1 ∘ Prod.π₂) ∘ Prod.⟨ 0m , id ⟩)            ≡⟨ Hom.eliml (pullr Prod.π₁∘factor ∙ ∘-zero-r) ⟩
      (inj1 ∘ Prod.π₂) ∘ Prod.⟨ 0m , id ⟩                  ≡⟨ cancelr Prod.π₂∘factor ⟩
      inj1                                                 ∎
```

For uniqueness, we use distributivity of composition over addition of
morphisms and the universal property of the product to establish the
desired equation. Check it out:

```agda
    coprod .has-is-coproduct .unique {inj0 = inj0} {inj1} other p q = sym $
      inj0 ∘ Prod.π₁ + inj1 ∘ Prod.π₂                                             ≡⟨ ap₂ _+_ (pushl (sym p)) (pushl (sym q)) ⟩
      (other ∘ Prod.⟨ id , 0m ⟩ ∘ Prod.π₁) + (other ∘ Prod.⟨ 0m , id ⟩ ∘ Prod.π₂) ≡⟨ ∘-linear-r _ _ _ ⟩
      other ∘ (Prod.⟨ id , 0m ⟩ ∘ Prod.π₁ + Prod.⟨ 0m , id ⟩ ∘ Prod.π₂)           ≡⟨ elimr lemma ⟩
      other                                                                       ∎
      where
        lemma : Prod.⟨ id , 0m ⟩ ∘ Prod.π₁ + Prod.⟨ 0m , id ⟩ ∘ Prod.π₂
              ≡ id
        lemma = Prod.unique₂ {pr1 = Prod.π₁} {pr2 = Prod.π₂}
          (sym (∘-linear-r _ _ _) ∙ ap₂ _+_ (cancell Prod.π₁∘factor) (pulll Prod.π₁∘factor ∙ ∘-zero-l) ∙ Hom.elimr refl)
          (sym (∘-linear-r _ _ _) ∙ ap₂ _+_ (pulll Prod.π₂∘factor ∙ ∘-zero-l) (cancell Prod.π₂∘factor) ∙ Hom.eliml refl)
          (elimr refl)
          (elimr refl)
```

# Pre-abelian & abelian categories

An additive category is **pre-abelian** when it additionally has
[kernels] and cokernels, hence binary [equalisers] and [coequalisers]
where one of the maps is zero.

[kernels]: Cat.Diagram.Kernel.html
[equalisers]: Cat.Diagram.Equaliser.html
[coequalisers]: Cat.Diagram.Coequaliser.html

```agda
record is-pre-abelian {o ℓ} (C : Precategory o ℓ) : Type (o ⊔ lsuc ℓ) where
  field has-additive : is-additive C
  open is-additive has-additive public
  field
    kernel   : ∀ {A B} (f : Hom A B) → Kernel C ∅ f
    cokernel : ∀ {A B} (f : Hom A B) → Coequaliser 0m f

  module Ker {A B} (f : Hom A B) = Kernel (kernel f)
  module Coker {A B} (f : Hom A B) = Coequaliser (cokernel f)
```

Every morphism $A \xto{f} B$ in a preabelian category admits a canonical
decomposition as

$$
A \xepi{p} \coker (\ker f) \xto{f'} \ker (\coker f) \xmono{i} B\text{,}
$$

where, as indicated, the map $p$ is an epimorphism (indeed a [regular
epimorphism], since it is a cokernel) and the map $i$ is a [regular
monomorphism].

[regular epimorphism]: Cat.Diagram.Coequaliser.RegularEpi.html
[regular monomorphism]: Cat.Diagram.Equaliser.RegularMono.html

```agda
  decompose
    : ∀ {A B} (f : Hom A B)
    → Σ[ f′ ∈ Hom (Coker.coapex (Ker.kernel f)) (Ker.ker (Coker.coeq f)) ]
       (f ≡ Ker.kernel (Coker.coeq f) ∘ f′ ∘ Coker.coeq (Ker.kernel f))
  decompose {A} {B} f = map , sym path
    where
      proj′ : Hom (Coker.coapex (Ker.kernel f)) B
      proj′ = Coker.coequalise (Ker.kernel f) {e′ = f} $ sym path
```

<!--
```agda
        where abstract
          path : f ∘ kernel f .Kernel.kernel ≡ f ∘ 0m
          path = Ker.equal f
            ·· ∅.zero-∘r _
            ·· ap₂ _∘_ (∅.has⊥ _ .paths 0m) refl
            ·· ∘-zero-l ·· sym ∘-zero-r
```
-->

```agda
      map : Hom (Coker.coapex (Ker.kernel f)) (Ker.ker (Coker.coeq f))
      map = Ker.limiting (Coker.coeq f) {e′ = proj′} $ sym path
```

The existence of the map $f'$, and indeed of the maps $p$ and $i$,
follow from the universal properties of kernels and cokernels. The map
$p$ is the canonical quotient map $A \to \coker(f)$, and the map $i$ is
the canonical subobject inclusion $\ker(f) \to B$.

<!--
```agda
        where abstract
          path : ∅.zero→ ∘ proj′ ≡ Coker.coeq f ∘ proj′
          path = Coker.unique₂ (Ker.kernel f)
            {e′ = 0m} {p = ∘-zero-r ∙ sym ∘-zero-l}
            (sym ( pushl (∅.zero-∘r _) ∙ pulll ( ap₂ _∘_ refl (∅.has⊤ _ .paths 0m)
                                               ∙ ∘-zero-r)
                 ∙ ∘-zero-l))
            (sym ( pullr (Coker.universal (Ker.kernel f)) ∙ sym (Coker.coequal _)
                 ∙ ∘-zero-r))

      path =
        Ker.kernel (Coker.coeq f) ∘ map ∘ Coker.coeq (Ker.kernel f) ≡⟨ pulll (Ker.universal _) ⟩
        proj′ ∘ Coker.coeq (Ker.kernel f)                           ≡⟨ Coker.universal _ ⟩
        f                                                           ∎
```
-->

A pre-abelian category is **abelian** when the map $f'$ in the above
decomposition is an isomorphism.

```agda
record is-abelian {o ℓ} (C : Precategory o ℓ) : Type (o ⊔ lsuc ℓ) where
  field has-is-preab : is-pre-abelian C
  open is-pre-abelian has-is-preab public
  field
    coker-ker≃ker-coker
      : ∀ {A B} (f : Hom A B) → is-invertible (decompose f .fst)
```
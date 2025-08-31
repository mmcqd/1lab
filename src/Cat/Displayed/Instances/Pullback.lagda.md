<!--
```agda
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Functor
open import Cat.Instances.Functor
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Reasoning as Cr
import Cat.Displayed.Reasoning as Dr
import Cat.Displayed.Morphism as Dm
import Cat.Displayed.Solver as Ds
```
-->

```agda
module
  Cat.Displayed.Instances.Pullback
    {o ℓ o' ℓ' o'' ℓ''}
    {X : Precategory o ℓ} {B : Precategory o' ℓ'}
    (F : Functor X B)
    (E : Displayed B o'' ℓ'')
  where
```

# Pullback of a displayed category {defines=pullback-fibration}

If we have a category $E$ [[displayed over|displayed category]] $B$,
then a functor $F : X \to B$ defines a (contravariant) "change-of-base"
action, resulting in a category $F^*(E)$ displayed over $X$.

<!--
```agda
private
  module X = Cr X
  module B = Cr B
  module E = Displayed E

open Functor F
open Dr E
open Dm E
```
-->

The reason for this contravariance is the following: A category
displayed over $X$ must have a $X$-indexed space of objects; But our
category $E$ has a $B$-indexed space of objects. Fortunately, $F$ gives
us a map $x \mapsto F_0(x)$ which allows us to convert our $X$-indices
to $B$-indices. The same goes for indexing the displayed $\hom$-sets.

```agda
Change-of-base : Displayed X o'' ℓ''
Change-of-base .Ob[_] x      = Ob[ F₀ x ]
Change-of-base .Hom[_] f x y = Hom[ F₁ f ] x y
Change-of-base .Hom[_]-set f = Hom[ F₁ f ]-set
Change-of-base .id'          = hom[ sym F-id ] id'
Change-of-base ._∘'_ f' g'   = hom[ sym (F-∘ _ _) ] (f' ∘' g')
```

Proving that the pullback $F^*(E)$ is indeed a displayed category is a
bit trickier than it might seem --- we must adjust the identity and
composites in $E$ by the paths witnessing functoriality of $F$, and this
really throws a spanner in the works --- but the handy [displayed
category reasoning combinators][dr] are here to help.

[dr]: Cat.Displayed.Reasoning.html

```agda
Change-of-base .idr' {f = f} f' = to-pathp[] $
  hom[] (hom[ F-∘ _ _ ]⁻ (f' ∘' hom[ F-id ]⁻ _)) ≡⟨ hom[]⟩⟨ smashr _ _ ⟩
  hom[] (hom[] (f' ∘' id'))                      ≡⟨ Ds.disp! E ⟩
  f'                                             ∎

Change-of-base .idl' f' = to-pathp[] $
  hom[] (hom[ F-∘ _ _ ]⁻ (hom[ F-id ]⁻ _ ∘' f')) ≡⟨ hom[]⟩⟨ smashl _ _ ⟩
  hom[] (hom[] (id' ∘' f'))                      ≡⟨ Ds.disp! E ⟩
  f'                                             ∎

Change-of-base .assoc' f' g' h' = to-pathp[] $
  hom[ ap F₁ _ ] (hom[ F-∘ _ _ ]⁻ (f' ∘' hom[ F-∘ _ _ ]⁻ (g' ∘' h')))   ≡⟨ hom[]⟩⟨ smashr _ _ ⟩
  hom[] (hom[] (f' ∘' g' ∘' h'))                                        ≡⟨ Ds.disp! E ⟩
  hom[ sym (F-∘ _ _) ] (hom[ sym (F-∘ _ _) ] (f' ∘' g') ∘' h')          ∎
```

<!--
```agda
Change-of-base .hom[_] p f' = hom[ ap F₁ p ] f'
Change-of-base .coh[_] p f' = coh[ ap F₁ p ] f'
```
-->

## As a fibration

If $\cE$ is a [[cartesian fibration]], then the base change of $\cE$
along $F$ is also cartesian. To prove this, observe that the object and
hom spaces of `Change-of-base`{.Agda} contain the same data as $\cE$,
just restricted to objects and morphisms in the image of $F$. This means
that we still have cartesian lifts of all morphisms in $\cX$: we
just have to perform the lifting of $F f$.

```agda
Change-of-base-fibration : Cartesian-fibration E → Cartesian-fibration Change-of-base
Change-of-base-fibration fib f FY' = f-cart-lift where
  open Cartesian-fibration E fib

  f-cart-lift : Cartesian-lift Change-of-base f FY'
  f-cart-lift .Cartesian-lift.x' = F₁ f ^* FY'
  f-cart-lift .Cartesian-lift.lifting = π* (F₁ f) FY'
  f-cart-lift .Cartesian-lift.cartesian .is-cartesian.universal m h' =
    π*.universal (F₁ m) (hom[ F-∘ f m ] h')
  f-cart-lift .Cartesian-lift.cartesian .is-cartesian.commutes m h' =
    hom[ F-∘ f m ]⁻ (π* (F₁ f) FY' ∘' π*.universal (F₁ m) (hom[ F-∘ f m ] h')) ≡⟨ ap hom[ F-∘ f m ]⁻ (π*.commutes _ _) ⟩
    hom[ F-∘ f m ]⁻ (hom[ F-∘ f m ] h')                                          ≡⟨ Ds.disp! E ⟩
    h'                                                                           ∎
  f-cart-lift .Cartesian-lift.cartesian .is-cartesian.unique {m = m} {h' = h'} m' p =
    π*.unique m' $
      π* (F₁ f) FY' ∘' m'                                    ≡⟨ Ds.disp! E ⟩
      hom[ F-∘ f m ] (hom[ F-∘ f m ]⁻ (π* (F₁ f) FY' ∘' m')) ≡⟨ ap hom[ F-∘ f m ] p ⟩
      hom[ F-∘ f m ] h'                                        ∎
```

<!--
```agda
module Change-of-base = Dm Change-of-base
```
-->

Change of base preserves displayed isomorphisms.

```agda
Change-of-base-iso[] : ∀ {a b a' b'} {i : a X.≅ b} → a' Change-of-base.≅[ i ] b' → a' ≅[ F-map-iso F i ] b'
Change-of-base-iso[] {i = i} i' = make-iso[ _ ] (i' .Dm.to') (i' .Dm.from') (wrap _ ∙[] i' .Dm.invl' ∙[] unwrap _) (wrap _ ∙[] i' .Dm.invr' ∙[] unwrap _)

Change-of-base-iso↓ : ∀ {a} {a₁ a₂ : Ob[ F₀ a ]} → a₁ Change-of-base.≅↓ a₂ → a₁ ≅↓ a₂
Change-of-base-iso↓ i' = iso[ ext F-id ] (Change-of-base-iso[] i')
```

Cartesian morphisms in $\cE$ can be pulled back to cartesian morphisms in the change of base.

```
Change-of-base-cartesian 
  : ∀ {a b a' b'} {f : X.Hom a b} {f' : Hom[ F₁ f ] a' b'}
  → is-cartesian E (F₁ f) f' → is-cartesian Change-of-base f f'
Change-of-base-cartesian {f = f} {f' = f'} cart = cb-cart
  where
    open is-cartesian cart
    cb-cart : is-cartesian _ _ _
    cb-cart .is-cartesian.universal m h' = universal' (sym $ F-∘ _ _) h'
    cb-cart .is-cartesian.commutes m h' = cast[] $ (unwrap _) ∙[] (commutesp (sym $ F-∘ _ _) h')
    cb-cart .is-cartesian.unique m' p = cast[] $ uniquep _ refl _ _ (to-pathp[] p)
```

We can define a displayed functor from $F^*E$ to E.

```agda

open Displayed-functor

Change-of-base-functor : Displayed-functor F Change-of-base E
Change-of-base-functor .F₀' x = x
Change-of-base-functor .F₁' f = f
Change-of-base-functor .F-id' = symP $ coh[ (sym F-id) ] _
Change-of-base-functor .F-∘' = symP $ coh[ (sym $ F-∘ _ _) ] _
```

If $\cE$ is a fibration, then this functor is *fibred*.

```agda 
module _ (E* : Cartesian-fibration E) where
  module E* = Cartesian-fibration _ E*
  module F^*E* = Cartesian-fibration _ (Change-of-base-fibration E*)

  Change-of-base-functor-fibred : is-fibred-functor Change-of-base-functor
  Change-of-base-functor-fibred .is-fibred-functor.F-cartesian {f' = f'} x = 
    domain-iso→cartesian E 
      (Change-of-base-iso↓ $ cartesian-domain-unique _ x F^*E*.π*.cartesian) 
      ((refl⟩∘'⟨ (unwrap _ ∙[] apd (λ _ → E*.π*.universal (F₁ X.id)) (hom[]-∙ _ _))) ∙[] E*.π*.commutesp (_ ∙∙ _ ∙∙ _) f') 
      E*.π*.cartesian


<!--
```agda
open import Cat.Prelude

open import Data.Id.Base
open import Data.Dec

import Cat.Reasoning
```
-->

```agda
module Cat.Instances.Discrete where
```

<!--
```agda
private variable
  ℓ ℓ' : Level
  X : Type ℓ
  C : Precategory ℓ ℓ'

open Precategory
open Functor
open _=>_
```
-->

# Discrete categories {defines="discrete-category"}

Given a groupoid $A$, we can build the category $\rm{Disc}(A)$ with
space of objects $A$ and a single morphism $x \to y$ whenever $x \equiv
y$.

```agda
Disc : (A : Type ℓ) → is-groupoid A → Precategory ℓ ℓ
Disc A A-grpd .Ob = A
Disc A A-grpd .Hom = _≡_
Disc A A-grpd .Hom-set = A-grpd
Disc A A-grpd .id = refl
Disc A A-grpd ._∘_ p q = q ∙ p
Disc A A-grpd .idr _ = ∙-idl _
Disc A A-grpd .idl _ = ∙-idr _
Disc A A-grpd .assoc _ _ _ = sym (∙-assoc _ _ _)

-- Disc' : Set ℓ → Precategory ℓ ℓ
-- Disc' A = Disc ∣ A ∣ h where abstract
--   h : is-groupoid ∣ A ∣
--   h = is-hlevel-suc 2 (A .is-tr)

Disc! : {T : Type ℓ} ⦃ _ : Underlying T ⦄ (A : T) {@(tactic hlevel-tactic-worker) A-grpd : is-groupoid ⌞ A ⌟} → Precategory _ _
Disc! A {A-grpd} = Disc ⌞ A ⌟ h where abstract
  h : is-groupoid ⌞ A ⌟
  h = A-grpd

-- open import Data.Bool

-- 𝟚 : ∀ ℓ → Set ℓ
-- 𝟚 ℓ = el! (Lift ℓ Bool)

-- test : ∀ {ℓ} → Disc! (𝟚 ℓ) {A-grpd = {!   !}} ≡ Disc! (𝟚 ℓ) {A-grpd = {!   !}}
-- test = refl

```

We can lift any function between the underlying types to a functor
between discrete categories. This is because every function
automatically respects equality in a functorial way.

```agda
lift-disc
  : {T₁ : Type ℓ} ⦃ _ : Underlying T₁ ⦄ {A : T₁} {@(tactic hlevel-tactic-worker) A-grpd : is-groupoid ⌞ A ⌟ } 
    {T₂ : Type ℓ'} ⦃ _ : Underlying T₂ ⦄ {B : T₂} {@(tactic hlevel-tactic-worker) B-grpd : is-groupoid ⌞ B ⌟}
  → (⌞ A ⌟ → ⌞ B ⌟)
  → Functor (Disc! A {A-grpd}) (Disc! B {B-grpd})
lift-disc f .F₀ = f
lift-disc f .F₁ = ap f
lift-disc f .F-id = refl
lift-disc f .F-∘ p q = ap-∙ f q p
```

<!--
```agda
Codisc' : ∀ {ℓ'} → Type ℓ → Precategory ℓ ℓ'
Codisc' x .Ob = x
Codisc' x .Hom _ _ = Lift _ ⊤
Codisc' x .Hom-set _ _ = is-prop→is-set (λ _ _ i → lift tt)
Codisc' x .id = lift tt
Codisc' x ._∘_ _ _ = lift tt
Codisc' x .idr _ = refl
Codisc' x .idl _ = refl
Codisc' x .assoc _ _ _ = refl
```
-->

## Diagrams in Disc(X)

If $X$ is a `discrete type`{.Agda ident=Discrete}, then it is in
particular in `Set`{.Agda}, and we can make diagrams of shape
$\rm{Disc}(X)$ in some category $\cC$, using the decidable
equality on $X$. We note that the decidable equality is _redundant_
information: The construction `Disc'`{.Agda} above extends into a [[left
adjoint]] to the `Ob`{.Agda} functor.

```agda
Disc-diagram
  : {T : Type ℓ} ⦃ _ : Underlying T ⦄ {X : T} {@(tactic hlevel-tactic-worker) X-grpd : is-groupoid ⌞ X ⌟} ⦃ _ : Discrete ⌞ X ⌟ ⦄
  → (⌞ X ⌟ → Ob C)
  → Functor (Disc! X {X-grpd}) C
Disc-diagram {C = C} {X = X} ⦃ d ⦄ f = F where
  module C = Precategory C

  P : ⌞ X ⌟ → ⌞ X ⌟ → Type _
  P x y = C.Hom (f x) (f y)

  go : ∀ {x y : ⌞ X ⌟} → x ≡ y → Dec (x ≡ᵢ y) → P x y
  go {x} {.x} p (yes reflᵢ) = C.id
  go {x} {y}  p (no ¬p)     = absurd (¬p (Id≃path.from p))
```

The object part of the functor is the provided $f : X \to
\rm{Ob}(\cC)$, and the decidable equality is used to prove that
$f$ respects equality. This is why it's redundant: $f$ automatically
respects equality, because it's a function! However, by using the
decision procedure, we get better computational behaviour: Very often,
$\rm{disc}(x,x)$ will be $\rm{yes}(\refl)$, and
substitution along $\refl$ is easy to deal with.

```agda
  F : Functor _ _
  F .F₀ = f
  F .F₁ {x} {y} p = go p (x ≡ᵢ? y)
```

Proving that our our $F_1$ is functorial involves a bunch of tedious
computations with equalities and a whole waterfall of absurd cases:

```agda
  F .F-id {x} = refl
  F .F-∘  {x} {y} {z} f g =
    J (λ y g → ∀ {z} (f : y ≡ z) → go (g ∙ f) (x ≡ᵢ? z) ≡ go f (y ≡ᵢ? z) C.∘ go g (x ≡ᵢ? y))
      (λ f → J (λ z f → go (refl ∙ f) (x ≡ᵢ? z) ≡ go f (x ≡ᵢ? z) C.∘ C.id) (sym (C.idr _)) f)
      g f
```

<!--
```
Disc-adjunct : 
  {T : Type ℓ} ⦃ _ : Underlying T ⦄ {X : T} {@(tactic hlevel-tactic-worker) X-grpd : is-groupoid ⌞ X ⌟}
  → (⌞ X ⌟ → C .Ob)
  → Functor (Disc! X {X-grpd}) C
Disc-adjunct {C = C} F .F₀ = F
Disc-adjunct {C = C} F .F₁ p = subst (C .Hom (F _) ⊙ F) p (C .id)
Disc-adjunct {C = C} F .F-id = transport-refl _
Disc-adjunct {C = C} {T = T} {X-grpd = X-grpd} F .F-∘ {x} {y} {z} f g = path where
  import Cat.Reasoning C as C
  go = Disc-adjunct {C = C} {T = T} {X-grpd = X-grpd} F .F₁
  abstract
    path : go (g ∙ f) ≡ C ._∘_ (go f) (go g)
    path =
      J' (λ y z f → ∀ {x} (g : x ≡ y) → go (g ∙ f) ≡ go f C.∘ go g)
        (λ x g → subst-∙ (C .Hom (F _) ⊙ F) _ _ _
              ·· transport-refl _
              ·· C.introl (transport-refl _))
        f {x} g
```
-->

<!--
```agda
Disc-natural
  : {T : Type ℓ} ⦃ _ : Underlying T ⦄ {X : T} {@(tactic hlevel-tactic-worker) X-grpd : is-groupoid ⌞ X ⌟}
  → {F G : Functor (Disc! X {X-grpd}) C}
  → (∀ x → C .Hom (F .F₀ x) (G .F₀ x))
  → F => G
Disc-natural fam .η = fam
Disc-natural {C = C} {F = F} {G = G} fam .is-natural x y f =
  J (λ y p → fam y C.∘ F .F₁ p ≡ (G .F₁ p C.∘ fam x))
    (C.elimr (F .F-id) ∙ C.introl (G .F-id))
    f
  where module C = Cat.Reasoning C
```
-->

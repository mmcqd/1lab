<!--
```
open import 1Lab.Path.IdentitySystem
open import 1Lab.HLevel.Retracts
open import 1Lab.HLevel
open import 1Lab.Path
open import 1Lab.Type

open import Data.Dec.Base
open import Data.Bool
```
-->

```agda
module Data.Nat.Base where
```

<!--
```agda
open import Prim.Data.Nat hiding (_<_) public
```
-->

# Natural numbers {defines="natural-number"}

The natural numbers are the inductive type generated by `zero`{.Agda}
and closed under taking `suc`{.Agda}cessors. Thus, they satisfy the
following induction principle, which is familiar:

```agda
Nat-elim : ∀ {ℓ} (P : Nat → Type ℓ)
         → P 0
         → ({n : Nat} → P n → P (suc n))
         → (n : Nat) → P n
Nat-elim P pz ps zero    = pz
Nat-elim P pz ps (suc n) = Nat-elim (λ z → P (suc z)) (ps pz) ps n

iter : ∀ {ℓ} {A : Type ℓ} → Nat → (A → A) → A → A
iter zero f = id
iter (suc n) f = f ∘ iter n f
```

Translating from type theoretic notation to mathematical English, the
type of `Nat-elim`{.Agda} says that if a predicate `P` holds of
`zero`{.Agda}, and the truth of `P(suc n)` follows from `P(n)`, then `P`
is true for every natural number.

## Discreteness

An interesting property of the natural numbers, type-theoretically, is
that they are `discrete`{.Agda}: given any pair of natural numbers,
there is an algorithm that can tell you whether or not they are equal.
First, observe that we can `distinguish`{.Agda} zero from successor:

```agda
zero≠suc : {n : Nat} → ¬ zero ≡ suc n
zero≠suc path = subst distinguish path tt where
  distinguish : Nat → Type
  distinguish zero = ⊤
  distinguish (suc x) = ⊥
```

<!--
```agda
suc≠zero : {n : Nat} → ¬ suc n ≡ zero
suc≠zero = zero≠suc ∘ sym
```
-->

The idea behind this proof is that we can write a predicate which is
`true`{.Agda ident=⊤} for zero, and `false`{.Agda ident=⊥} for any
successor. Since we know that `⊤`{.Agda} is inhabited (by `tt`{.Agda}),
we can transport that along the claimed path to get an inhabitant of
`⊥`{.Agda}, i.e., a contradiction.

```agda
pred : Nat → Nat
pred 0 = 0
pred (suc n) = n

suc-inj : {x y : Nat} → suc x ≡ suc y → x ≡ y
suc-inj = ap pred
```

Furthermore, observe that the `successor`{.Agda} operation is injective,
i.e., we can “cancel” it on paths. Putting these together, we get a
proof that equality for the natural numbers is decidable:

<!--
```agda
private module _ where private
```
-->

```agda
  Discrete-Nat : Discrete Nat
  Discrete-Nat {zero} {zero}  = yes refl
  Discrete-Nat {zero} {suc y} = no λ zero≡suc → absurd (zero≠suc zero≡suc)
  Discrete-Nat {suc x} {zero} = no λ suc≡zero → absurd (suc≠zero suc≡zero)
  Discrete-Nat {suc x} {suc y} with Discrete-Nat {x} {y}
  ... | yes x≡y = yes (ap suc x≡y)
  ... | no ¬x≡y = no λ sucx≡sucy → ¬x≡y (suc-inj sucx≡sucy)
```

<!--
```agda
is-equal→path : ∀ {x y} → (x == y) ≡ true → x ≡ y
is-equal→path {zero}  {zero}  p = refl
is-equal→path {zero}  {suc y} p = absurd (true≠false (sym p))
is-equal→path {suc x} {zero}  p = absurd (true≠false (sym p))
is-equal→path {suc x} {suc y} p = ap suc (is-equal→path p)

is-not-equal→not-path : ∀ {x y} → (x == y) ≡ false → ¬ (x ≡ y)
is-not-equal→not-path {zero}  {zero}  p q = absurd (true≠false p)
is-not-equal→not-path {zero}  {suc y} p q = absurd (zero≠suc q)
is-not-equal→not-path {suc x} {zero}  p q = absurd (zero≠suc (sym q))
is-not-equal→not-path {suc x} {suc y} p q = is-not-equal→not-path p (suc-inj q)

instance
  Discrete-Nat : Discrete Nat
  Discrete-Nat {x} {y} with inspect (x == y)
  ... | true  , p = yes (is-equal→path p)
  ... | false , p = no  (is-not-equal→not-path p)
```
-->

[[Hedberg's theorem]] implies that `Nat`{.Agda} is a [[set]], i.e., it only
has trivial paths.

```agda
opaque
  Nat-is-set : is-set Nat
  Nat-is-set = Discrete→is-set Discrete-Nat

instance
  H-Level-Nat : ∀ {n} → H-Level Nat (2 + n)
  H-Level-Nat = basic-instance 2 Nat-is-set
```

## Arithmetic

::: warning
**Heads up!** The arithmetic properties of operations on the natural
numbers are in the module [`Data.Nat.Properties`].
:::

[`Data.Nat.Properties`]: Data.Nat.Properties.html

Agda already comes with definitions for addition and multiplication of
natural numbers. They are reproduced below, using different names, for
the sake of completeness:

```agda
plus : Nat → Nat → Nat
plus zero y = y
plus (suc x) y = suc (plus x y)

times : Nat → Nat → Nat
times zero y = zero
times (suc x) y = y + times x y
```

These match up with the built-in definitions of `_+_`{.Agda} and
`_*_`{.Agda}:

```agda
plus≡+ : plus ≡ _+_
plus≡+ i zero y = y
plus≡+ i (suc x) y = suc (plus≡+ i x y)

times≡* : times ≡ _*_
times≡* i zero y = zero
times≡* i (suc x) y = y + (times≡* i x y)
```

The exponentiation operator `^`{.Agda} is defined by recursion on the
exponent.

```agda
_^_ : Nat → Nat → Nat
x ^ zero = 1
x ^ suc y = x * (x ^ y)

infixr 8 _^_
```

## Ordering

We define the order relation `_≤_`{.Agda} on the natural numbers as an
inductive predicate. We could also define the relation by recursion on
the numbers to be compared, but the inductive version has much better
properties when it comes to type inference.

```agda
data _≤_ : Nat → Nat → Type where
  instance
    0≤x : ∀ {x} → 0 ≤ x
  s≤s : ∀ {x y} → x ≤ y → suc x ≤ suc y
```

<!--
```agda
instance
  s≤s' : ∀ {x y} → ⦃ x ≤ y ⦄ → suc x ≤ suc y
  s≤s' ⦃ x ⦄ = s≤s x

Positive : Nat → Type
Positive zero    = ⊥
Positive (suc n) = ⊤
```
-->

We define the strict ordering on `Nat`{.Agda} as well,
re-using the definition of `_≤_`{.Agda}.

```agda
_<_ : Nat → Nat → Type
m < n = suc m ≤ n
infix 3 _<_ _≤_
```

As an "ordering combinator", we can define the _maximum_ of two natural
numbers by recursion: The maximum of zero and a successor (on either
side) is the successor, and the maximum of successors is the successor of
their maximum.

```agda
max : Nat → Nat → Nat
max zero zero = zero
max zero (suc y) = suc y
max (suc x) zero = suc x
max (suc x) (suc y) = suc (max x y)
```

Similarly, we can define the minimum of two numbers:

```agda
min : Nat → Nat → Nat
min zero zero = zero
min zero (suc y) = zero
min (suc x) zero = zero
min (suc x) (suc y) = suc (min x y)
```

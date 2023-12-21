<!--
```agda
open import Cat.Prelude

open import Order.Base
```
-->

```agda
module Order.Reasoning {ℓ ℓ'} (P : Poset ℓ ℓ') where
```

# Partial order syntax

This module defines a syntax for reasoning with transitivity in a
[[partial order]]. Simply speaking, it lets us write chains like

$$
a \le b \le c
$$

to mean something like "$a \le c$ through the intermediate step $b$". In
the syntax, we intersperse the justification for _why_ $a \le b$ and $b
\le c$. We also allow equality steps, so chains like $a \le b = b' \le
c$ are supported, too.

```agda
open Poset P public

private variable
  a b c d : ⌞ P ⌟

_≤⟨_⟩_ : (a : ⌞ P ⌟) → a ≤ b → b ≤ c → a ≤ c
_=⟨_⟩_ : (a : ⌞ P ⌟) → a ≡ b → b ≤ c → a ≤ c
_=˘⟨_⟩_ : (a : ⌞ P ⌟) → b ≡ a → b ≤ c → a ≤ c
_≤∎    : (a : ⌞ P ⌟) → a ≤ a

path→≤ : ∀ {x y} → x ≡ y → x ≤ y
path→≤ p = subst (_≤ _) (sym p) ≤-refl

path→≥ : ∀ {x y} → x ≡ y → y ≤ x
path→≥ p = subst (_≤ _) p ≤-refl

f ≤⟨ p ⟩ q = ≤-trans p q
f =⟨ p ⟩ q = subst (_≤ _) (sym p) q
f =˘⟨ p ⟩ q = subst (_≤ _) p q
f ≤∎ = ≤-refl

infixr 2 _=⟨_⟩_ _=˘⟨_⟩_ _≤⟨_⟩_
infix  3 _≤∎

-- Whiskering on the left of _≤_
_▶_ : b ≡ a → b ≤ c → a ≤ c
p ▶ l = subst (_≤ _) p l

-- Whiskering on the right of _≤_
_◀_ : b ≤ c → c ≡ d → b ≤ d
l ◀ p = subst (_ ≤_) p l


_▶_◀_ : b ≡ a → b ≤ c → c ≡ d → a ≤ d
p ▶ l ◀ q = (p ▶ l) ◀ q
```

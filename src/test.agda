open import 1Lab.Prelude
-- open import Data.Bool
-- open import Data.Nat

module test where



-- data Vec (A : Type) : Nat → Type where
--     nil : Vec A 0
--     cons : ∀ {n} → A → Vec A n → Vec A (suc n)

-- concat : ∀ {A n m} → Vec A n → Vec A m → Vec A (n + m)
-- concat nil ys = ys
-- concat (cons x xs) ys = cons x (concat xs ys)



data Bit : Type where
    t : Bit
    f : Bit

data Equal {A : Type} (x : A) : A → Type where
    rfl : Equal x x



p : Equal t t
p = rfl

not : Bit → Bit
not t = f
not f = t


not-not : (x : Bit) → Equal (not (not x)) x
not-not t = rfl
not-not f = rfl


data ℕ : Type where
    zero : ℕ
    suc : ℕ → ℕ

plus : ℕ → ℕ → ℕ
plus zero m = m
plus (suc n) m = suc (plus n m)




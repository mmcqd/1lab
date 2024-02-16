

open import Cat.Prelude
open import Cat.Functor.Adjoint
open import Cat.Instances.Shape.Terminal
open import Cat.Instances.Product
open import Cat.Instances.Comma
open import Cat.Diagram.Initial
open import Data.Sum

open Precategory
open Functor
open _=>_
open _⊣_

module test where

Sets² : ∀ κ → Precategory _ _ 
Sets² κ = Sets κ ×ᶜ Sets κ

module A κ where
  Forget = !F

  Cofree : Functor ⊤Cat (Sets κ)
  Cofree .F₀ _ = el! (Lift _ ⊤)
  Cofree .F₁ _ _ = lift tt
  Cofree .F-id = refl
  Cofree .F-∘ _ _ = refl

  Forget⊣Cofree : Forget ⊣ Cofree
  Forget⊣Cofree .unit .η _ _ = lift tt
  Forget⊣Cofree .unit .is-natural _ _ _ = refl
  Forget⊣Cofree .counit .η _ = tt
  Forget⊣Cofree .counit .is-natural _ _ _ = refl
  Forget⊣Cofree .zig = refl
  Forget⊣Cofree .zag = refl

  Free : Functor ⊤Cat (Sets κ)
  Free .F₀ _ = el! (Lift _ ⊥) 
  Free .F₁ _ x = x
  Free .F-id = refl
  Free .F-∘ _ _ = refl 

  Free⊣Forget : Free ⊣ Forget
  Free⊣Forget .unit .η _ = tt
  Free⊣Forget .unit .is-natural _ _ _ = refl
  Free⊣Forget .counit .η _ ()
  Free⊣Forget .counit .is-natural _ _ _ = ext λ ()
  Free⊣Forget .zig = ext λ ()
  Free⊣Forget .zag = refl

module B κ where
  Forget : Functor (Sets² κ) (Sets κ)
  Forget = Fst

  Cofree : Functor (Sets κ) (Sets² κ)
  Cofree .F₀ A = A , (el! (Lift _ ⊤))
  Cofree .F₁ f = f , (λ x → x)
  Cofree .F-id = refl
  Cofree .F-∘ f g = refl

  Forget⊣Cofree : Forget ⊣ Cofree
  Forget⊣Cofree .unit .η (A , B) = (λ x → x) , (λ _ → lift tt)
  Forget⊣Cofree .unit .is-natural _ _ (f , g) = refl
  Forget⊣Cofree .counit .η _ = λ x → x 
  Forget⊣Cofree .counit .is-natural _ _ _ = refl
  Forget⊣Cofree .zig = refl
  Forget⊣Cofree .zag = refl

  Free : Functor (Sets κ) (Sets² κ)
  Free .F₀ A = A , (el! (Lift _ ⊥))
  Free .F₁ f = f , (λ x → x)
  Free .F-id = refl
  Free .F-∘ _ _ = refl

  Free⊣Forget : Free ⊣ Forget
  Free⊣Forget .unit .η _ = λ x → x
  Free⊣Forget .unit .is-natural _ _ _ = refl
  Free⊣Forget .counit .η (A , B) = (λ z → z) , (λ ())
  Free⊣Forget .counit .is-natural _ _ _ = ext ((λ _ → refl) , λ ())
  Free⊣Forget .zig = ext ((λ _ → refl) , λ ())
  Free⊣Forget .zag = refl

module C κ where

  Mult : Functor (Sets² κ) (Sets κ)
  Mult .F₀ (A , B) = el! (⌞ A ⌟ × ⌞ B ⌟) 
  Mult .F₁ (f , g) (x , y) = f x , g y
  Mult .F-id = refl
  Mult .F-∘ f g = refl

  Δ : Functor (Sets κ) (Sets² κ)
  Δ .F₀ A = A , A
  Δ .F₁ f = f , f
  Δ .F-id = refl
  Δ .F-∘ f g = refl

  Δ⊣Mult : Δ ⊣ Mult
  Δ⊣Mult .unit .η A x = x , x
  Δ⊣Mult .unit .is-natural A B f = refl
  Δ⊣Mult .counit .η (A , B) = fst , snd
  Δ⊣Mult .counit .is-natural _ _ f = refl
  Δ⊣Mult .zig = refl
  Δ⊣Mult .zag = refl
  

  -- Intuitively, a right adjoint to Mult would be a "divison" functor,
  -- which turns a set A into (A₁ , A₂), such that A₁ × A₂ ≡ A.
  -- And in particular, such that (A × B)₁ ≡ A and (A × B)₂ ≡ B.
  -- This lets us *differentiate* between (⊤ × ⊥), (⊥ × ⊤), because
  -- (⊤ × ⊥)₁ ≡ ⊤ and (⊥ × ⊤)₁ ≡ ⊥, but (⊤ × ⊥) and (⊥ × ⊤) are equal!
  ¬Mult⊣ : (R : Functor (Sets κ) (Sets² κ)) → ¬ (Mult ⊣ R)
  ¬Mult⊣ R adj = Adj.counit.ε (el! (Lift _ ⊥)) (left-half , right-half) .Lift.lower where
    module Adj = _⊣_ adj
    module R = Functor R
    
    lemma₁ : ⌞ R.₀ (el! (Lift κ ⊤ × Lift κ ⊥)) .fst ⌟
    lemma₁ = Adj.unit.η (el! (Lift κ ⊤) , el! (Lift κ ⊥)) .fst (lift tt)

    lemma₂ :  ⌞ R.₀ (el! (Lift κ ⊥ × Lift κ ⊤)) .snd ⌟
    lemma₂ = Adj.unit.η (el! (Lift κ ⊥) , el! (Lift κ ⊤)) .snd (lift tt)

    left-half : ⌞ R.₀ (el! (Lift κ ⊥)) .fst ⌟
    left-half = subst (λ A → ⌞ R.₀ A .fst ⌟) (n-ua ((λ ()) , (record { is-eqv = λ () }))) lemma₁

    right-half : ⌞ R.₀ (el! (Lift κ ⊥)) .snd ⌟
    right-half = subst (λ A → ⌞ R.₀ A .snd ⌟) (n-ua ((λ ()) , (record { is-eqv = λ () }))) lemma₂

-- module D κ where
  
--   Sum : Functor (Sets² κ) (Sets κ)
--   Sum .F₀ (A , B) = el! (⌞ A ⌟ ⊎ ⌞ B ⌟)
--   Sum .F₁ (f , g) = [ inl ⊙ f , inr ⊙ g ]
--   Sum .F-id = ext (λ where (inl x) → λ _ → inl x
--                            (inr x) → λ _ → inr x)
--   Sum .F-∘ (f , f') (g , g') = ext (λ where (inl x) → λ _ → inl (f (g x))
--                                             (inr x) → λ _ → inr (f' (g' x)))
    
--   Δ : Functor (Sets κ) (Sets² κ)
--   Δ .F₀ A = A , A
--   Δ .F₁ f = f , f
--   Δ .F-id = refl
--   Δ .F-∘ f g = refl

--   Sum⊣Δ : Sum ⊣ Δ
--   Sum⊣Δ .unit .η (A , B) = inl , inr
--   Sum⊣Δ .unit .is-natural _ _ _ = refl
--   Sum⊣Δ .counit .η A = [ (λ x → x) , (λ x → x) ]
--   Sum⊣Δ .counit .is-natural _ _ f = ext (λ where (inl x) → refl
--                                                  (inr x) → refl)
--   Sum⊣Δ .zig = ext (λ where (inl x) → refl
--                             (inr x) → refl)
--   Sum⊣Δ .zag = refl


--   ¬⊣Sum : (L : Functor (Sets κ) (Sets² κ)) → ¬ (L ⊣ Sum)
--   ¬⊣Sum L adj = bad .fst {!   !} .Lift.lower where
--     module Adj = _⊣_ adj
--     module L = Functor L
    
--     lemma₁ : ⌞ L.₀ (el! (Lift κ ⊥ ⊎ Lift κ ⊤)) .fst ⌟ ⊎ ⌞ L.₀ (el! (Lift κ ⊥ ⊎ Lift κ ⊤)) .snd ⌟
--     lemma₁ = Adj.unit.η (el! ((Lift κ ⊥ ⊎ Lift κ ⊤))) (inr (lift tt))
    
--     bad : (⌞ L.₀ (el! (Lift κ ⊥ ⊎ Lift κ ⊤)) .fst ⌟ → Lift κ ⊥) × (⌞ L.₀ (el! (Lift κ ⊥ ⊎ Lift κ ⊤)) .snd ⌟ → Lift κ ⊤)
--     bad = Adj.counit.ε (el! (Lift κ ⊥) , el! (Lift κ ⊤))
    
--     foo : ⌞ L.₀ (el! (Lift κ ⊥ ⊎ Lift κ ⊤)) .fst ⌟ ⊎ ⌞ L.₀ (el! (Lift κ ⊥ ⊎ Lift κ ⊤)) .snd ⌟ → ⌞ L.₀ (el! (Lift κ ⊥ ⊎ Lift κ ⊤)) .fst ⌟
--     foo (inl x) = x
--     foo (inr x) = {!   !}＝


open import Data.Nat
open import Data.List
open import Data.Dec

data Fiber {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) : B → Type (ℓ ⊔ ℓ') where
  fiber : (x : A) → Fiber f (f x)

variable
  ℓ : Level
  A : Type ℓ
  n : Nat

Vec : (A : Type ℓ) → Nat → Type ℓ
Vec A n = Fiber (length {A = A}) n

vnil : Vec A 0
vnil = fiber []

vcons : A → Vec A n → Vec A (suc n)
vcons x (fiber xs) = fiber (x ∷ xs)

vec-elim : (P : ∀ {n} → Vec A n → Type ℓ) → P vnil → (∀ {n} {x : A} {xs : Vec A n} → P xs → P (vcons x xs)) → ∀ {n} (xs : Vec A n) → P xs
vec-elim P n c (fiber []) = n
vec-elim P n c (fiber (x ∷ xs)) = c (vec-elim P n c (fiber xs))

Eq : {A : Type ℓ} → A → A → Type ℓ
Eq {A = A} x y = Fiber (λ (_ : ⊤) → x) y

eq-refl : {x : A} → Eq x x
eq-refl = fiber tt

eq-sym : {x y : A} → Eq x y → Eq y x
eq-sym (fiber tt) = eq-refl

data Ty : Type where
  `nat : Ty
  _`×_ : Ty → Ty → Ty

data Expr : Type where
  `z : Expr
  `s : Expr → Expr
  _`+_ : Expr → Expr → Expr
  `pair : Expr → Expr → Expr
  `fst : Expr → Expr
  `snd : Expr → Expr

open import Data.Maybe

infer-ty : Expr → Maybe Ty
infer-ty `z = just `nat
infer-ty (`s x) = do
  `nat ← infer-ty x
    where _ → nothing
  just `nat
infer-ty (x `+ y) = do
  `nat ← infer-ty x
    where _ → nothing
  `nat ← infer-ty y
    where _ → nothing
  just `nat
infer-ty (`pair x y) = do
  A ← infer-ty x
  B ← infer-ty y
  just (A `× B)
infer-ty (`fst x) = do
  A `× B ← infer-ty x
    where _ → nothing
  just A
infer-ty (`snd x) = do
  A `× B ← infer-ty x
    where _ → nothing
  just B

ExprI : Ty → Type
ExprI A = Fiber infer-ty (just A)


data UPair (A : Type ℓ) : Type ℓ where
  ⟨_,_⟩ : A → A → UPair A
  swap : (x y : A) → ⟨ x , y ⟩ ≡ ⟨ y , x ⟩

{-# TERMINATING #-}
plus' : UPair Nat → Nat
plus'-zero : ∀ x → plus' ⟨ x , zero ⟩ ≡ x
plus'-suc : ∀ x y → plus' ⟨ x , suc y ⟩ ≡ suc (plus' ⟨ x , y ⟩)

plus' ⟨ zero , y ⟩ = y
plus' ⟨ suc x , y ⟩ = suc (plus' ⟨ x , y ⟩)
plus' (swap zero y i) = plus'-zero y (~ i)
plus' (swap (suc x) y i) = {!   !}

plus'-zero zero = refl
plus'-zero (suc x) = ap suc (plus'-zero x)

plus'-suc zero y = refl
plus'-suc (suc x) y = ap suc (plus'-suc x y)


{-


    A type
----------------
  UPair A type

  x : A       y : A
---------------------
   {x , y} : UPair A

---------------------------
{x , y} ≡ {y , x} : UPair A

x : A , y : A ⊢ r : B  r[x
------------------------------
upair-rec r b : B

P : UPair A → Type  r : (x y : A) → P {x , y} 
------------------------
upair-elim P r b

-}


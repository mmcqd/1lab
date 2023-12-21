{-# OPTIONS -vtactic.absurd-goal:20 #-}

module 1Lab.Reflection.Absurd-goal where

open import 1Lab.Path
open import 1Lab.Type
open import 1Lab.Reflection renaming (absurd to absurd-pat)
open import Data.String.Show
open import Meta.Append
open import Data.Reflection.Name
open import Data.List
open import Meta.Foldable

{-# TERMINATING #-}
find-absurd : Term → Maybe Term
find-absurd-args : List (Arg Term) → Maybe Term

find-absurd (var x args) = find-absurd-args args
find-absurd (con c args) = find-absurd-args args
find-absurd (def (quote absurd) (_ ∷ _ ∷ bad ∷ _)) = just (def (quote absurd) (unknown h∷ unknown h∷ bad ∷ []))
find-absurd (def f args) = find-absurd-args args
find-absurd (lam v t) = nothing
find-absurd (pat-lam cs args) = nothing
find-absurd (pi (arg _ a) b) = find-absurd a
find-absurd (agda-sort s) = nothing
find-absurd (lit l) = nothing
find-absurd (meta x args) = find-absurd-args args
find-absurd unknown = nothing 

find-absurd-args args = nondet _ args λ (arg _ x) → find-absurd x


decompose-goal : Term → Term × (Term → Term)
decompose-goal (pi (arg as at) (abs vn cd)) = 
  let (goal , build-lam) = decompose-goal cd in
  goal , λ t → lam (ArgInfo.arg-vis as) (abs vn (build-lam t))
decompose-goal tm = tm , λ x → x

solve-absurd-goal : Term → TC ⊤
solve-absurd-goal goal = do
  goal-ty ← withReconstructed true $ withNormalisation true $ infer-type goal
  debugPrint "tactic.absurd-goal" 10 [ "normalised absurd-goal type: " , termErr goal-ty ]
  let (goal-ty , build-lam) = decompose-goal goal-ty
  (just bad) ← pure $ build-lam <$> find-absurd goal-ty
    where nothing → typeError [ "No use of absurd found in goal: " , termErr goal-ty ]
  debugPrint "tactic.absurd-goal" 10 [ "Found absurd: " , termErr bad ]
  unify goal bad


macro
  absurd-goal! : Term → TC ⊤
  absurd-goal! goal = solve-absurd-goal goal


-- Examples
private module _ {ℓ} {A : Type ℓ} where
  _ : {x : ⊥} {y : A} → absurd x ≡ y
  _ = absurd-goal! 

  _ : {x : ⊥} {y : A} → (y , y , y) ≡ (absurd x , absurd (absurd x) , y)
  _ = absurd-goal!

  _ : {n : Nat} (f : (A → Nat) → A → ⊥) {m : Nat} (x : A) → m + 1 + absurd (f (λ _ → m) x) ≡ n
  _ = absurd-goal!

  _ : (B : A → Type ℓ) (x : ⊥) → B (absurd x)
  _ = absurd-goal!

  _ : (R : A → A → Type ℓ) (x y : A) (f : A → A → ⊥) → R x (absurd (f x y))
  _ = absurd-goal!

  _ : (x y : ⊥) → absurd {A = A} x ≡ absurd y
  _ = absurd-goal!
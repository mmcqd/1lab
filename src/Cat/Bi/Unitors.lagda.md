```agda

open import Cat.Prelude
open import Cat.Bi.Base

import Cat.Reasoning as Cr

module Cat.Bi.Unitors {o oh ℓh} (B : Prebicategory o oh ℓh) where

open Prebicategory B hiding (module Hom)
private module Hom {A B} = Cr (Hom A B)
-- Lemma runitor_rwhisker_rwhisker {a b c d: C} (f : C⟦a, b⟧)
--       (g : C⟦b, c⟧) (h : C⟦c, d⟧)
--   : (rassociator f g (identity c) ▹ h) • ((f ◃ runitor g) ▹ h) =
--     runitor (f · g) ▹ h.
-- Proof.


lemma 
  : ∀ {A B C D : Ob} 
  → {!   !} Hom.≅ {!   !}
  -- → (f : C ↦ D) (g : B ↦ C) (h : A ↦ B)
  -- → (f ▶ α← g h id) ∘ f ▶ {!   !} ≡ f ▶ ρ→ (g ⊗ h)
lemma = {!   !}

```
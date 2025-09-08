```agda
open import Cat.Prelude
open import Cat.Bi.Base

module Cat.Bi.coherence {o oh ℓh} (B : Prebicategory o oh ℓh) where

open Prebicategory-Hom-Reasoning B

variable
  a b c d : Ob
  f g h k : a ↦ b


infixr 20 _`⊗_
data _`↦_ : Ob → Ob → Type (o ⊔ oh) where
  `_    : a ↦ b → a `↦ b
  `id   : a `↦ a
  _`⊗_  : b `↦ c → a `↦ b → a `↦ c

variable
  `f `g `h `k `f₁ `g₁ `h₁ `f₂ `g₂ `h₂ : a `↦ b
  


sem-↦ : a `↦ b → a ↦ b
sem-↦ (` f) = f
sem-↦ `id = id
sem-↦ (f `⊗ g) = sem-↦ f ⊗ sem-↦ g 

instance
  Brackets-`↦ : ⟦⟧-notation (a `↦ b)
  Brackets-`↦ .⟦⟧-notation.lvl = _
  Brackets-`↦ {a = a} {b = b} .⟦⟧-notation.Sem = a ↦ b
  Brackets-`↦ .⟦⟧-notation.⟦_⟧ = sem-↦

module 1-cell where
  data Value : Ob → Ob → Type (o ⊔ oh) where
    `id  : Value a a
    _`∘_ : b ↦ c → Value a b → Value a c

  eval : a `↦ b → Value a b
  do-⊗ : Value b c → Value a b → Value a c

  eval (` f) = f `∘ `id
  eval `id = `id
  eval (`f `⊗ `g) = do-⊗ (eval `f) (eval `g)

  do-⊗ `id vg = vg
  do-⊗ (f `∘ vf) vg = f `∘ do-⊗ vf vg

  `quote : Value a b → a ↦ b
  `quote `id = id
  `quote (f `∘ vf) = f ⊗ `quote vf

  quote-⊗ : (vf : Value b c) (vg : Value a b) → `quote (do-⊗ vf vg) Hom.≅ `quote vf ⊗ `quote vg
  quote-⊗ `id vg = λ≅ _
  quote-⊗ (f `∘ vf) vg = ▶-iso B f (quote-⊗ vf vg) Hom.∙Iso α≅.op _ _ _

  eval-sound : (`f : a `↦ b) → `quote (eval `f) Hom.≅ ⟦ `f ⟧
  eval-sound (` f) = ρ≅.op f
  eval-sound `id = Hom.id-iso
  eval-sound (`f `⊗ `g) = 
    `quote (do-⊗ (eval `f) (eval `g))   Hom.≅⟨ quote-⊗ (eval `f) (eval `g) ⟩ 
    `quote (eval `f) ⊗ `quote (eval `g) Hom.≅⟨ ◆-iso B (eval-sound `f) (eval-sound `g) ⟩
    ⟦ `f ⟧ ⊗ ⟦ `g ⟧ Hom.≅∎


  




infixr 10 _`⇒_


data _`⇒_ : (`f `g : a `↦ b) → Type (o ⊔ oh ⊔ ℓh) where
  `_ : ⟦ `f ⟧ ⇒ ⟦ `g ⟧ → `f `⇒ `g
  `id : `f `⇒ `f 
  _`∘_ : `g `⇒ `h → `f `⇒ `g  → `f `⇒ `h
  _`◆_ : (`f `⇒ `g) → (`h `⇒ `k) → (`f `⊗ `h) `⇒ (`g `⊗ `k)
  `λ← : (`f : a `↦ b) → `id `⊗ `f `⇒ `f
  `λ→ : (`f : a `↦ b) → `f `⇒ `id `⊗ `f
  `ρ← : (`f : a `↦ b) → `f `⊗ `id `⇒ `f
  `ρ→ : (`f : a `↦ b) → `f `⇒ `f `⊗ `id
  `α→ : (`f : c `↦ d) (`g : b `↦ c) (`h : a `↦ b)
      → (`f `⊗ `g) `⊗ `h `⇒ `f `⊗ (`g `⊗ `h)
  `α← : (`f : c `↦ d) (`g : b `↦ c) (`h : a `↦ b)
      → `f `⊗ (`g `⊗ `h) `⇒ (`f `⊗ `g) `⊗ `h

sem-⇒ :  `f `⇒ `g → ⟦ `f ⟧ ⇒ ⟦ `g ⟧
sem-⇒ (` β) = β
sem-⇒ `id = Hom.id
sem-⇒ (β `∘ γ) = sem-⇒ β ∘ sem-⇒ γ
sem-⇒ (β `◆ γ) = sem-⇒ β ◆ sem-⇒ γ
sem-⇒ (`λ← `f) = λ← ⟦ `f ⟧
sem-⇒ (`λ→ `f) = λ→ ⟦ `f ⟧
sem-⇒ (`ρ← `f) = ρ← ⟦ `f ⟧
sem-⇒ (`ρ→ `f) = ρ→ ⟦ `f ⟧
sem-⇒ (`α→ `f `g `h) = α→ ⟦ `f ⟧ ⟦ `g ⟧ ⟦ `h ⟧
sem-⇒ (`α← `f `g `h) = α← ⟦ `f ⟧ ⟦ `g ⟧ ⟦ `h ⟧

instance
  Brackets-`⇒ : ⟦⟧-notation (`f `⇒ `g)
  Brackets-`⇒ .⟦⟧-notation.lvl = _
  Brackets-`⇒ {`f = `f} {`g = `g} .⟦⟧-notation.Sem = ⟦ `f ⟧ ⇒ ⟦ `g ⟧
  Brackets-`⇒ .⟦⟧-notation.⟦_⟧ = sem-⇒


-- (f ∘ g) ◆ (h ∘ k) ≡ (f ◆ h) ∘ (g ◆ k)

-- ideas...
-- We want some kinda list again
-- Use naturality to get all the unitors/associators together on one side of the list
-- Then some wackiness to relate the unitors/associators
-- We want a "disjunctive normal form" type of sitaution
-- Turn everything into (β ◆ ... ◆ γ) ∘ ... ∘ (φ ◆ ... ◆ ψ)
-- Ok actually maybe we want (f ∘ ... ∘ g) ◆ ... ◆ (h ∘ ... ∘ k) 


infixr 20 _∘∷_

-- data VValue : (`f `g : a `↦ b) → Type (o ⊔ oh ⊔ ℓh) where
--   `id : VValue `f `f
--   _∘∷_ : ⟦ `g ⟧ ⇒ ⟦ `h ⟧ → VValue `f `g → VValue `f `h 

-- infixr 10 _◆∷_
-- data HValue : (`f `g : a `↦ b) → Type (o ⊔ oh ⊔ ℓh) where
--   `id : HValue `f `f
--   _◆∷_ : VValue `f `g → HValue `h `k → HValue (`f `⊗ `h) (`g `⊗ `k)
  -- α→◆∷_ : HValue ((`f₁ `⊗ `g₁) `⊗ `h₁) ((`f₂ `⊗ `g₂) `⊗ `h₂) → HValue (`f₁ `⊗ `g₁ `⊗ `h₁) (`f₂ `⊗ `g₂ `⊗ `h₂)
  -- α←◆∷_ : HValue (`f₁ `⊗ `g₁ `⊗ `h₁) (`f₂ `⊗ `g₂ `⊗ `h₂) →  HValue ((`f₁ `⊗ `g₁) `⊗ `h₁) ((`f₂ `⊗ `g₂) `⊗ `h₂)

-- Need:
-- HValue ((`f `⊗ `h) `⊗ `h₁) ((`g `⊗ `k) `⊗ `k₁) -> HValue (`f `⊗ (`h `⊗ `h₁)) (`g `⊗ (`k `⊗ `k₁))


-- do-◀ : HValue `f `g → (`h : a `↦ b) → HValue (`f `⊗ `h) (`g `⊗ `h)
-- do-◀ `id `h = `id
-- do-◀ (β ◆∷ βs) `h = α←◆∷ (β ◆∷ do-◀ βs `h)
-- do-◀ (α→◆∷ βs) `h = {! do-◀ βs `h  !}
-- do-◀ (α←◆∷ βs) `h = {!   !} 

-- do-◆ : HValue `f `g → HValue `h `k → HValue (`f `⊗ `h) (`g `⊗ `k)
-- do-◆ `id γs = `id ◆∷ γs
-- do-◆ (β ◆∷ βs) γs = α←◆∷ (β ◆∷ do-◆ βs γs)
-- do-◆ (α→◆∷ βs) γs = {!  do-◆ βs γs !}
-- do-◆ (α←◆∷ βs) γs = {! do-◆ βs γs  !}


-- -- "Horizontal" value
data HValue : (`f `g : a `↦ b) → Type (o ⊔ oh ⊔ ℓh) where
  `id : HValue `f `f
  `_ : ⟦ `f ⟧ ⇒ ⟦ `g ⟧ → HValue `f `g
  _◆∷_ : ⟦ `f ⟧ ⇒ ⟦ `g ⟧ → HValue `h `k → HValue (`f `⊗ `h) (`g `⊗ `k)

data Value : (`f `g : a `↦ b) → Type (o ⊔ oh ⊔ ℓh) where
  `id : Value `f `f
  _∘∷_ : HValue `g `h → Value `f `g → Value `f `h 

foo : Value (` compose.F₀ (id ⊗ id , id)) (` compose.F₀ (id , id ⊗ id))
foo = (` (α→ id id id)) ∘∷ `id

-- do-∘ : Value `g `h → Value `f `g → Value `f `h
-- do-∘ `id ys = ys
-- do-∘ (x ∘∷ xs) ys = x ∘∷ do-∘ xs ys

-- do-◆ : HValue `f `g → HValue `h `k → Value (`f `⊗ `h) (`g `⊗ `k)
-- do-◆ `id ys = (Hom.id ◆∷ ys) ∘∷ `id
-- do-◆ (` x) ys = (x ◆∷ ys) ∘∷ `id
-- do-◆ (x ◆∷ xs) ys = {! ? ∘∷ do-◆ xs ys  !}  

-- -- First we get things into these nice lists
-- eval : `f `⇒ `g → Value `f `g
-- eval (` β) = (` β) ∘∷ `id
-- eval `id = `id
-- eval (β `∘ γ) = do-∘ (eval β) (eval γ)
-- -- Functoriality of ◆
-- eval ((β `∘ γ) `◆ (δ `∘ σ)) = {!   !} -- eval ((β `◆ δ) `∘ (γ `◆ σ))
-- eval (β `◆ γ) = {!   !}
-- eval (`λ← `f) = {!   !}
-- eval (`λ→ `f) = {!   !}
-- eval (`ρ← `f) = {!   !}
-- eval (`ρ→ `f) = {!   !}
-- eval (`α→ `f `g `h) = {!   !}
-- eval (`α← `f `g `h) = {!   !} 


-- data _`⇒_ : (f g : a ↦ b) → Type (o ⊔ oh ⊔ ℓh) where
--   _`∘_ : g `⇒ h → f `⇒ g → f `⇒ h
--   _`▶_ : (f : a ↦ b) → g `⇒ h → (f ⊗ g) `⇒ (f ⊗ h)
--   _`◀_ : g `⇒ h → (f : a ↦ b) → (g ⊗ f) `⇒ (h ⊗ f) 
--   `λ← : (f : a ↦ b) → id ⊗ f `⇒ f
--   `λ→ : (f : a ↦ b) → f `⇒ id ⊗ f
--   `ρ← : (f : a ↦ b) → f ⊗ id `⇒ f
--   `ρ→ : (f : a ↦ b) → f `⇒ f ⊗ id
--   `α← : (f : c ↦ d) (g : b ↦ c) (h : a ↦ b)
--       → f ⊗ (g ⊗ h) `⇒ (f ⊗ g) ⊗ h 
--   `α→ : (f : c ↦ d) (g : b ↦ c) (h : a ↦ b)
--       → (f ⊗ g) ⊗ h `⇒ f ⊗ (g ⊗ h)

  

-- data Value : (f g : a ↦ b) → Type (o ⊔ oh ⊔ ℓh) where
--   []   : Value f g
--   _∘∷_ : (g ⇒ h) → Value f g → Value f h
--   _

  -- data _`⇒_ : (`f `g : a `↦ b) → Type (o ⊔ oh ⊔ ℓh) where
  -- `_  : ⟦ `f ⟧ ⇒ ⟦ `g ⟧ → `f `⇒ `g
  -- `id : `f `⇒ `f 
  -- _`∘_ : `g `⇒ `h → `f `⇒ `g  → `f `⇒ `h
  -- _`◆_ : `f `⇒ `g → `h `⇒ `k → (`f `⊗ `h) `⇒ (`g `⊗ `k)
  -- `λ← : (`f : a `↦ b) → `id `⊗ `f `⇒ `f
  -- `λ→ : (`f : a `↦ b) → `f `⇒ `id `⊗ `f
  -- `ρ← : (`f : a `↦ b) → `f `⊗ `id `⇒ `f
  -- `ρ→ : (`f : a `↦ b) → `f `⇒ `f `⊗ `id
  -- `α→ : (`f : c `↦ d) (`g : b `↦ c) (`h : a `↦ b)
  --     → (`f `⊗ `g) `⊗ `h `⇒ `f `⊗ (`g `⊗ `h)
  -- `α← : (`f : c `↦ d) (`g : b `↦ c) (`h : a `↦ b)
  --     → `f `⊗ (`g `⊗ `h) `⇒ (`f `⊗ `g) `⊗ `h

  
  -- data Value : (`f `g : a `↦ b) → Type (o ⊔ oh ⊔ ℓh) where
  --   `id : Value `f `f
  --   _`∘_ : 



 


```
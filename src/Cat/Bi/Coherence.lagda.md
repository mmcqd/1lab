```agda
open import Cat.Prelude hiding (pure ; _>>=_)
open import Cat.Bi.Base
open import Data.Dec

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


-- pure 
--   : ∀ {ℓa ℓb} {A : Type ℓa} {B : A → Type ℓb}
--   → (a : A) ⦃ _ : B a ⦄ → Σ A B
-- pure a ⦃ b ⦄ = (a , b)

-- _>>=_
--   : ∀ {ℓa ℓb ℓc} {A : Type ℓa} {B : A → Type ℓb} {C : Type ℓc}
--   → (p : Σ A B) → ((a : A) ⦃ b : B a ⦄ → C) → C
-- _>>=_ {B = B} (a , b) f = f a ⦃ b ⦄ 



module 1-cell where
  Value : Ob → Ob → Type _
  Value b c = ∀ {a} → a ↦ b → a ↦ c

  eval : (`f : a `↦ b) → Value a b
  eval (` f) g = f ⊗ g
  eval `id = {!   !}
  eval (`f `⊗ `f₁) = {!   !}
--   data Value : Ob → Ob → Type (o ⊔ oh) where
--     `id  : Value a a
--     _`⊗_ : b ↦ c → Value a b → Value a c

--   variable
--     vf vg vh vk : Value a b

--   data Eval : a `↦ b → Value a b → Type (o ⊔ oh) 
--   data Do-⊗ : Value b c → Value a b → Value a c → Type (o ⊔ oh) 

--   data Eval where
--     instance
--       val↓  : Eval (` f) (f `⊗ `id)
--       `id↓  : Eval (`id {a}) `id
--       `⊗↓ : ⦃ evf : Eval `f vf ⦄ ⦃ evg : Eval `g vg ⦄ ⦃ ev⊗ : Do-⊗ vf vg vh ⦄ → Eval (`f `⊗ `g) vh

--   data Do-⊗ where
--     instance
--       `id↓  : Do-⊗ `id vg vg
--       `⊗↓ : ⦃ ev⊗ : Do-⊗ vf vg vh ⦄ → Do-⊗ (f `⊗ vf) vg (f `⊗ vh) 

--   data Reflect : Value a b → a ↦ b → Type (o ⊔ oh) where
--     instance
--       `id↑ : Reflect (`id {a}) id
--       `⊗↑  : ⦃ rg : Reflect vg g ⦄ → Reflect (f `⊗ vg) (f ⊗ g)


--   record Nf (`f : a `↦ b) (f : a ↦ b) : Type (o ⊔ oh) where
--     instance constructor nf
--     field
--       {val}  : Value a b 
--       ⦃ ev ⦄ : Eval `f val
--       ⦃ rf ⦄ : Reflect val f



--   do-⊗ : (vf : Value b c) (vg : Value a b) → Σ (Value a c) (Do-⊗ vf vg)
--   do-⊗ `id vg = pure vg
--   do-⊗ {c = c} {a = a} (f' `⊗ vf) vg = do
--     vh ← do-⊗ vf vg
--     pure (f' `⊗ vh)

--   eval : (`f : a `↦ b) → Σ (Value a b) (Eval `f)
--   eval (` f) = pure (f `⊗ `id)
--   eval `id = pure `id
--   eval (`f `⊗ `g) = do
--     vf ← eval `f
--     vg ← eval `g
--     vh ← do-⊗ vf vg
--     pure vh

--   reflect : (vf : Value a b) → Σ (a ↦ b) (Reflect vf)
--   reflect `id = pure id 
--   reflect (f `⊗ vg) = do 
--     g ← reflect vg 
--     pure $ f ⊗ g

--   nm : (`f : a `↦ b) → Σ (a ↦ b) (Nf `f)
--   nm `f = do 
--     vf ← eval `f
--     f  ← reflect vf 
--     pure f

--   instance
--     eval-any : Eval `f (eval `f .fst)
--     eval-any {`f = `f} = eval `f .snd

--     reflect-any : Reflect vf (reflect vf .fst)
--     reflect-any {vf = vf} = reflect vf .snd

--     do-⊗-any : Do-⊗ vf vg (do-⊗ vf vg .fst)
--     do-⊗-any {vf = vf} {vg = vg} = do-⊗ vf vg .snd 

--     nf-any : Nf `f (nm `f .fst)
--     nf-any {`f = `f} = nm `f .snd

--     {-# INCOHERENT reflect-any eval-any do-⊗-any  #-}

--   reflect-unique : ⦃ _ : Reflect vf g ⦄ ⦃ _ : Reflect vf h ⦄ → g Hom.≅ h
--   reflect-unique  ⦃ `id↑ ⦄ ⦃ `id↑ ⦄ = Hom.id-iso
--   reflect-unique  ⦃ `⊗↑  ⦄ ⦃ `⊗↑  ⦄ = ▶-iso B _ reflect-unique

--   do-⊗-reflect : ⦃ _ : Do-⊗ vf vg vh ⦄ ⦃ _ : Reflect vf f ⦄ ⦃ _ : Reflect vg g ⦄ ⦃ _ : Reflect vh h ⦄ → f ⊗ g Hom.≅ h
--   do-⊗-reflect ⦃ `id↓ ⦄ ⦃ `id↑ ⦄ ⦃ rg ⦄ ⦃ rh  ⦄ = (λ≅.op _) Hom.∙Iso reflect-unique
--   do-⊗-reflect ⦃ `⊗↓  ⦄ ⦃ `⊗↑  ⦄ ⦃ rg ⦄ ⦃ `⊗↑ ⦄ = α≅ _ _ _ Hom.∙Iso (▶-iso B _ $ do-⊗-reflect)

--   nf-sound : {`f : a `↦ b} {f : a ↦ b} → Nf `f f → ⟦ `f ⟧ Hom.≅ f
--   nf-sound (nf {val} ⦃ val↓ ⦄ ⦃ `⊗↑ ⦃ rg = `id↑ ⦄ ⦄) = ρ≅ _
--   nf-sound (nf {val} ⦃ `id↓ ⦄ ⦃ `id↑ ⦄) = Hom.id-iso
--   nf-sound (nf {val} ⦃ `⊗↓ {vf = vf} {vg = vg} ⦄ ⦃ rf  ⦄) = 
--     ◆-iso B (nf-sound (nf {val = vf})) (nf-sound (nf {val = vg})) Hom.∙Iso do-⊗-reflect


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

-- variable
--   vf vg vh vk : 1-cell.Value a b

-- infixr 20 _◆::_
-- data HValue : (vf vg : 1-cell.Value a b) → Type (o ⊔ oh ⊔ ℓh) where
--   `id   : HValue vf vf
--   val   : ⦃ _ : 1-cell.Reflect vf f ⦄ ⦃ _ : 1-cell.Reflect vg g ⦄ → (f ⇒ g) → HValue vf vg
--   _◆::_ 
--     : ∀ {vf⊗h vg⊗k}
--     → ⦃ _ : 1-cell.Reflect vf f ⦄ ⦃ _ : 1-cell.Reflect vg g ⦄ 
--     → ⦃ _ : 1-cell.Do-⊗ vf vh vf⊗h ⦄ ⦃ _ : 1-cell.Do-⊗ vg vk vg⊗k ⦄
--     → (f ⇒ g)
--     → HValue vh vk 
--     → HValue vf⊗h vg⊗k

-- infixr 10 _∘::_
-- data VValue : (vf vg : 1-cell.Value a b) → Type (o ⊔ oh ⊔ ℓh) where
--   `id : VValue vf vf
--   _∘::_ : HValue vg vh → VValue vf vg → VValue vf vh

-- eval : ⦃ _ : 1-cell.Eval `f vf ⦄ ⦃ _ : 1-cell.Eval `g vg ⦄ → `f `⇒ `g → VValue vf vg
-- eval (` x) = val {! x  !} ∘:: {!   !}
-- eval `id = {!   !}
-- eval (β `∘ β₁) = {!   !}
-- eval (β `◆ β₁) = {!   !}
-- eval (`λ← `f) = {!   !}
-- eval (`λ→ `f) = {!   !}
-- eval (`ρ← `f) = {!   !}
-- eval (`ρ→ `f) = {!   !}
-- eval (`α→ `f `g `h) = {!   !}
-- eval (`α← `f `g `h) = {!   !}


```
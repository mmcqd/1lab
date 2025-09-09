```agda

open import Cat.Prelude
open import Cat.Displayed.Cartesian.Discrete
open import Cat.Bi.Base
open import Cat.Bi.Instances.Opposite
open import Cat.Bi.Displayed.Base
open import Cat.Bi.Displayed.Cartesian
open import Cat.Bi.Displayed.Cartesian.Discrete

import Cat.Displayed.Cartesian.Discrete.Reasoning as Dcr 
import Cat.Bi.Unitors as Bu

module Cat.Bi.Displayed.Cartesian.Discrete.Fibre 
  {o oh ℓh o' oh' ℓh'}
  {B : Prebicategory o oh ℓh}
  (E : Bidisplayed B o' oh' ℓh')
  (E* : is-locally-discrete E)
  where

open Prebicategory-Hom-Reasoning B
open Bu B
open Bidisplayed-Hom[]-Reasoning E

private
  module B^op = Prebicategory (B ^Op)
  module B^co = Prebicategory (B ^Co)
  module B^coop = Prebicategory (B ^Coop)


private module _ {A B} {A' : Ob[ A ]} {B' : Ob[ B ]} where
  open is-discrete-cartesian-fibration (E* A' B') public
  open Dcr (E* A' B') public


^*-⊗' 
  : ∀ {A B C A' B' C'} {f₁ : B ↦ C} {f₂ : A ↦ B} {g : B ↦ C} {h : A ↦ B} 
  → {α : f₁ ⇒ g} {β : f₂ ⇒ h} 
  → {g' : B' [ g ]↦ C'} {h' : A' [ h ]↦ B'}
  → ob[ α ◆ β ] (g' ⊗' h') ≡ (ob[ α ] g') ⊗' (ob[ β ] h')
^*-⊗' {α = α} {β = β} {g' = g'} {h' = h'} = 
   ^*-lift _ (π* α g' ◆' π* β h')

Fibre : Ob → Precategory _ _
Fibre X .Precategory.Ob = Ob[ X ]
Fibre X .Precategory.Hom a b = a [ id ]↦ b
Fibre X .Precategory.Hom-set _ _ = hlevel 2
Fibre X .Precategory.id = ↦id'
Fibre X .Precategory._∘_ f g = ob[ λ→ id ] (f ⊗' g)
Fibre X .Precategory.idr f = ^*-lift _ (Hom[].hom[ λ→≡ρ→ ]⁻ (ρ→' f))
Fibre X .Precategory.idl f = ^*-lift _ (λ→' f)
Fibre X .Precategory.assoc f g h = sym $ ^*-lift _ $
  Hom[].hom[ coh ] $
  ob[ λ→ id ] (f ⊗' g) ⊗' h               ≡[]ob⟨ (ob-coh[ λ≅.op _ ]⁻ _) ◀' h ⟩ 
  (f ⊗' g) ⊗' h                           ≡[]ob⟨ α←' _ _ _ ⟩
  f ⊗' (g ⊗' h)                           ≡[]ob⟨ f ▶' (ob-coh[ λ≅.op _ ] _) ⟩
  f ⊗' ob[ λ→ id ] (g ⊗' h)               ≡[]ob⟨ ob-coh[ λ≅.op _ ] _ ⟩
  ob[ λ→ id ] (f ⊗' ob[ λ→ id ] (g ⊗' h)) ∎ob
  where
    coh : (λ← _ ◀ id ∘ α← _ _ _ ∘ id ▶ λ→ _ ∘ λ→ _ ∘ Hom.id) ≡ λ→ _
    coh = 
      λ← _ ◀ id ∘ α← _ _ _ ∘ id ▶ λ→ _ ∘ ⌜ λ→ _ ∘ Hom.id ⌝           ≡⟨ ap! (Hom.idr _) ⟩
      λ← id ◀ id ∘ α← _ _ _ ∘ ⌜ id ▶ λ→ id ⌝ ∘ λ→ id                 ≡˘⟨ ap¡ (B^co.triangle _ _) ⟩
      λ← id ◀ id ∘ ⌜ α← id id id ∘ (α→ _ _ _ ∘ ρ→ id ◀ id) ∘ λ→ id ⌝ ≡⟨ ap! (Hom.pulll (Hom.cancell (α≅.invr _ _ _))) ⟩
      λ← id ◀ id ∘ ⌜ ρ→ id ⌝ ◀ id ∘ λ→ id                            ≡˘⟨ ap¡ λ→≡ρ→ ⟩
      λ← id ◀ id ∘ λ→ id ◀ id ∘ λ→ id                                ≡⟨ Hom.cancell (Hom.invl (◀-iso B id (λ≅.op _))) ⟩
      λ→ id ∎

-- rebase : ∀ {x y y' y''} → (f : x ↦ y)
--           → y' [ id ]↦ y''
--           → (f ^*1 y') [ id ]↦ (f ^*1 y'')
-- rebase f vert = π*1.universal' ((λ→ f) ∘ (ρ← f)) (vert ⊗' π*1 f _)

-- module _ {a b} (f : a ↦ b) where
--   open Functor


--   base-change : Functor (Fibre b) (Fibre a) 
--   base-change .F₀ g = f ^*1 g
--   base-change .F₁ α = rebase f α
--   base-change .F-id = sym $ π*1.unique¹ _ $ sym $ ^*-lift _ $ (λ→' _) ∘' (ρ←' _)
--   base-change .F-∘ {x = x} {y} {z} h k = sym $ 
--     ^*-lift _ $
--     π*1.uniquep¹ 
--       (α≅.op _ _ _ Hom.∙Iso ◀-iso B _ Hom.id-iso Hom.∙Iso ◀-iso B _ (ρ≅.op _ Hom.∙Iso λ≅ _) Hom.∙Iso {!   !}) -- ((((λ≅ _) Hom.∘Iso (ρ≅.op _)) Hom.∘Iso (ρ≅.op _)) Hom.∘Iso (α≅.op _ _ _)) 
--       (λ≅.op _) 
--       _ 
--       {!   !} -- (Hom.insertr3 coh)
--       _ $
--       π*1 f z ⊗' rebase f h ⊗' rebase f k            ≡[]ob⟨ α→' _ _ _ ⟩ 
--       (π*1 f z ⊗' rebase f h) ⊗' rebase f k          ≡[]ob⟨ ≡→≡[]ob (π*1.commutes¹ _ _) ◀' _ ⟩
--       ob[ λ→ f ∘ ρ← f ] (h ⊗' π*1 f y) ⊗' rebase f k ≡[]ob⟨ ob-coh[ λ≅.op _ Hom.∙Iso ρ≅ _ ]⁻ _ ◀' _ ⟩ 
--       (h ⊗' π*1 f y) ⊗' rebase f k                   ≡[]ob⟨ α←' _ _ _ ⟩
--       h ⊗' (π*1 f y ⊗' rebase f k)                   ≡[]ob⟨ h ▶' ≡→≡[]ob (π*1.commutes¹ _ _) ⟩
--       h ⊗' ob[ λ→ f ∘ ρ← f ] (k ⊗' π*1 f x)          ≡[]ob⟨ h ▶' ob-coh[ λ≅.op _ Hom.∙Iso ρ≅ _ ]⁻ _ ⟩
--       h ⊗' (k ⊗' π*1 f x)                            ≡[]ob⟨ α→' _ _ _ ⟩
--       (h ⊗' k) ⊗' π*1 f x                            ≡[]ob⟨ ob-coh[ λ≅.op _ ] _ ◀' π*1 f x ⟩
--       ob[ λ→ id ] (h ⊗' k) ⊗' π*1 f x ∎ob
--     -- where
--       -- coh : ρ← _ ∘ α← _ _ _ ∘ f ▶ λ→ _ ≡ Hom.id
--       -- coh = 
--       --   ρ← _ ∘ ⌜ α← _ _ _ ∘ f ▶ λ→ _ ⌝ ≡⟨ ap! (B^coop.triangle _ _) ⟩
--       --   ⌜ ρ← _ ⌝ ∘ ρ→ _ ◀ id           ≡˘⟨ ap¡ ρ←◀ ⟩
--       --   ρ← f ◀ id ∘ ρ→ f ◀ id          ≡˘⟨ preaction B id .F-∘ _ _ ⟩
--       --   ⌜ ρ← f ∘ ρ→ f ⌝ ◀ id           ≡⟨ ap! (ρ≅.invr _) ⟩ 
--       --   Hom.id ◀ id                    ≡⟨ compose.F-id ⟩ 
--       --   Hom.id                         ∎

 
--       --   sym $ π*.uniquep _ _ _ _ $
--       -- Fib.pulllf (π*.commutesp id-comm _)
--       -- ∙[] pullr[] _ (π*.commutesp id-comm _)
--       -- ∙[] pulll[] _ Fib.to-fibre
```
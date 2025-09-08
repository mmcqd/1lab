```agda

open import Cat.Prelude
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
  {E : Bidisplayed B o' oh' ℓh'}
  (E* : is-discrete-cartesian-bifibration E)
  where

open Prebicategory-Hom-Reasoning B
open Bu B
open Bidisplayed-Hom[]-Reasoning E

private
  module B^op = Prebicategory (B ^Op)
  module B^co = Prebicategory (B ^Co)
  module B^coop = Prebicategory (B ^Coop)


open is-discrete-cartesian-bifibration E*
private module _ {A B} {A' : Ob[ A ]} {B' : Ob[ B ]} where
  open Dcr (2-cart A' B') public


^*-⊗' 
  : ∀ {A B C A' B' C'} {f₁ : B ↦ C} {f₂ : A ↦ B} {g : B ↦ C} {h : A ↦ B} 
  → {α : f₁ ⇒ g} {β : f₂ ⇒ h} 
  → {g' : B' [ g ]↦ C'} {h' : A' [ h ]↦ B'}
  → ob[ α ◆ β ] (g' ⊗' h') ≡ (ob[ α ] g') ⊗' (ob[ β ] h')
^*-⊗' {α = α} {β = β} {g' = g'} {h' = h'} = ^*-lift _ 
  (π*2 α g' ◆' π*2 β h')

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

rebase : ∀ {x y y' y''} → (f : x ↦ y)
          → y' [ id ]↦ y''
          → (f ^*1 y') [ id ]↦ (f ^*1 y'')
rebase f vert = π*1.universal' ((λ→ f) ∘ (ρ← f)) (vert ⊗' π*1 f _)

module _ {a b} (f : a ↦ b) where
  open Functor


  base-change : Functor (Fibre b) (Fibre a) 
  base-change .F₀ g = f ^*1 g
  base-change .F₁ α = rebase f α
  base-change .F-id = sym $ π*1.unique¹ _ $ sym $ ^*-lift _ $ (λ→' _) ∘' (ρ←' _)
  base-change .F-∘ f g = sym $ 
    {!   !}
```
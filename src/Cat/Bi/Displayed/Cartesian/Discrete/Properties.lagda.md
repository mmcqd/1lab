```agda

open import Cat.Prelude
open import Cat.Bi.Base
open import Cat.Bi.Instances.Opposite
open import Cat.Bi.Displayed.Base
open import Cat.Bi.Displayed.Cartesian
open import Cat.Bi.Displayed.Cartesian.Discrete
open import Cat.Displayed.Base
open import Cat.Functor.Base
open import Cat.Displayed.Functor
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Cartesian.Discrete
open import Cat.Displayed.Univalence.Reasoning
open import Cat.Displayed.Instances.TotalProduct

import Cat.Reasoning as Cr
import Cat.Bi.Morphism as Cbm
import Cat.Displayed.Cartesian.Discrete.Reasoning as Dcr 
import Cat.Bi.Displayed.Cartesian.Discrete.Fibre


module Cat.Bi.Displayed.Cartesian.Discrete.Properties 
  {o oh ℓh o' oh' ℓh'} 
  {B : Prebicategory o oh ℓh} 
  (E : Bidisplayed B o' oh' ℓh') 
  (let open Bidisplayed-Hom[]-Reasoning E)
  (E* : is-locally-discrete E) 
  where

open Cat.Bi.Displayed.Cartesian.Discrete.Fibre E E*
open Prebicategory-Hom-Reasoning B 
module B^co = Prebicategory (B ^Co)
open Cbm B
open 1-cell E E* public

private module _ {A B} {A' : Ob[ A ]} {B' : Ob[ B ]} where
  open is-discrete-cartesian-fibration (E* A' B') public
  open Dcr (E* A' B') public



-- is-monicᵇ : ∀ {A B} → (A ↦ B) → Type _
-- is-monicᵇ {A} f = 
--   ∀ {C} (g h : C ↦ A) 
--   → (p : f ⊗ g Hom.≅ f ⊗ h)
--   → Σ[ q ∈ g Hom.≅ h ] (▶-iso B f q ≡ p)

-- is-monic[_]ᵇ : ∀ {A B} {f : A ↦ B} {A' : Ob[ A ]} {B' : Ob[ B ]} → is-monicᵇ f → (A' [ f ]↦ B') → Type _
-- is-monic[_]ᵇ {A = A} {f = f} {A' = A'} {B' = B'} mono f' = 
--   ∀ {C C'} {g h : C ↦ A}
--   → (g' : C' [ g ]↦ A') (h' : C' [ h ]↦ A')
--   → Σ (f ⊗ g Hom.≅ f ⊗ h) ((f' ⊗' g') ≡[_]ob (f' ⊗' h'))
--   → Σ (g Hom.≅ h) (g' ≡[_]ob h')

-- discrete-cartesian→monic[_]ᵇ
--   : ∀ {x y x' y'} {f : x ↦ y}
--   → {f' : x' [ f ]↦ y'}
--   → (mono : is-monicᵇ f)
--   → is-discrete-cartesian f f'
--   → is-monic[ mono ]ᵇ f'
-- discrete-cartesian→monic[_]ᵇ {f = f} mono f-cart g' h' (p , p') = 
--   mono _ _ p .fst , uniquep₂¹ p (mono _ _ p .fst) Hom.id-iso (sym ((ap (p .Hom.to ∘_) (ap Hom.from $ mono _ _ p .snd)) ∙ p .Hom.invl)) g' h' p' Hom[].id'
--   where 
--     open is-discrete-cartesian f-cart

-- is-weak-monicᵇ : ∀ {A B} {f : A ↦ B} {A' : Ob[ A ]} {B' : Ob[ B ]} → (A' [ f ]↦ B') → Type _
-- is-weak-monicᵇ {A = A} {f = f} {A' = A'} {B' = B'} f' = 
--   ∀ {C C'} {g h : C ↦ A}
--   → (g' : C' [ g ]↦ A') (h' : C' [ h ]↦ A')
--   → (p : g Hom.≅ h)
--   → (f' ⊗' g') ≡[ ▶-iso B f p ]ob (f' ⊗' h')
--   → g' ≡[ p ]ob h'

-- discrete-cartesian→weak-monic
--   : ∀ {x y x' y'} {f : x ↦ y}
--   → {f' : x' [ f ]↦ y'}
--   → is-discrete-cartesian f f'
--   → is-weak-monicᵇ f'
-- discrete-cartesian→weak-monic {f = f} f-cart g' g'' p w = 
--   uniquep₂¹ (▶-iso B f p) p Hom.id-iso (sym $ ▶-iso B f p .Hom.invl) g' g'' w Hom[].id'
--   where 
--     open is-discrete-cartesian f-cart




-- record _≅ᵇ↓_ {A} (A' : Ob[ A ]) (B' : Ob[ A ]) : Type (oh' ⊔ ℓh') where
--   field
--     to'       : A' [ id   ]↦ B'
--     from'     : B' [ id ]↦ A'
--     invl'     : to' ⊗' from' ≡[ λ≅ _ Hom.Iso⁻¹ ]ob ↦id'
--     invr'     : from' ⊗' to' ≡[ λ≅ _ Hom.Iso⁻¹ ]ob ↦id'

-- discrete-cartesian→domain-unique
--   : ∀ {x y} {f : x ↦ y}
--   → ∀ {x' x'' y'} {f' : x' [ f ]↦ y'} {f'' : x'' [ f ]↦ y'}
--   → is-discrete-cartesian f f'
--   → is-discrete-cartesian f f''
--   → x' ≅ᵇ↓ x''
-- discrete-cartesian→domain-unique {f = f} {f' = f'} {f'' = f''} f'-cart f''-cart =
--   record { to' = to* ; from' = from* ; invl' = invl* ; invr' = invr* } 
--   where
--     module f' = is-discrete-cartesian f'-cart
--     module f'' = is-discrete-cartesian f''-cart
    
--     to* = f''.universal¹ id (f' ⊗' ↦id')
--     from* = f'.universal¹ id (f'' ⊗' ↦id')
    

--     coh : α→ f id id ∘ (Hom.id ◆ Hom.id) ∘ (ρ→ f ◀ id) ∘ Hom.id ∘ Hom.id ≡ f ▶ λ→ id
--     coh = 
--       α→ f id id ∘ (Hom.id ◆ Hom.id) ∘ (ρ→ f ◀ id) ∘ Hom.id ∘ Hom.id ≡⟨ Hom.pulll (Hom.elimr compose.F-id) ⟩
--       α→ f id id ∘ ⌜ ρ→ f ◀ id ∘ Hom.id ∘ Hom.id ⌝                   ≡⟨ ap! (Hom.elimr (Hom.idl _)) ⟩
--       α→ f id id ∘ ρ→ f ◀ id                                         ≡⟨ B^co.triangle _ _ ⟩
--       f ▶ λ→ id                                                      ∎

--     invl* : (to* ⊗' from*) ≡[ λ≅ _ Hom.Iso⁻¹ ]ob ↦id'
--     invl* = 
--       discrete-cartesian→weak-monic f''-cart (to* ⊗' from*) ↦id' (λ≅ _ Hom.Iso⁻¹) $
--       Hom[].hom[ coh ] $
--       f'' ⊗' to* ⊗' from*   ≡[]ob⟨ α→' _ _ _ ⟩
--       (f'' ⊗' to*) ⊗' from* ≡[]ob⟨ ≡→≡[]ob (f''.commutes¹ _ _) ◀' from* ⟩
--       (f' ⊗' ↦id') ⊗' from* ≡[]ob⟨ (ρ→' _) ◀' from* ⟩
--       f' ⊗' from*           ≡[]ob⟨ ≡→≡[]ob (f'.commutes¹ _ _) ⟩
--       f'' ⊗' ↦id'           ∎ob

--     invr* : (from* ⊗' to*) ≡[ λ≅ _ Hom.Iso⁻¹ ]ob ↦id'
--     invr* = 
--       discrete-cartesian→weak-monic f'-cart (from* ⊗' to*) ↦id' (λ≅ _ Hom.Iso⁻¹) $
--       Hom[].hom[ coh ] $ 
--       f' ⊗' from* ⊗' to*   ≡[]ob⟨ α→' _ _ _ ⟩
--       (f' ⊗' from*) ⊗' to* ≡[]ob⟨ ≡→≡[]ob (f'.commutes¹ _ _) ◀' to* ⟩
--       (f'' ⊗' ↦id') ⊗' to* ≡[]ob⟨ (ρ→' _) ◀' to* ⟩
--       f'' ⊗' to*           ≡[]ob⟨ ≡→≡[]ob (f''.commutes¹ _ _) ⟩
--       f' ⊗' ↦id'           ∎ob
```
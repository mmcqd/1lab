{-# OPTIONS --cubical --postfix-projections #-}
module Awodey.Chapter1 where
  
open import 1Lab.Prelude
open import Cat.Prelude
open import Cat.Functor.Base

Rel : ∀ o → Precategory _ _
Rel o .Precategory.Ob = Set o
Rel o .Precategory.Hom A B = ∣ A ∣ → ∣ B ∣ → Prop o
Rel o .Precategory.Hom-set = hlevel!
Rel o .Precategory.id a b = el! (a ≡ b)
Rel o .Precategory._∘_ _R₁_ _R₂_ a c = el! (∃[ b ∈ _ ] (∣ a R₂ b ∣ × ∣ b R₁ c ∣))
Rel o .Precategory.idr _R_ = ext λ a c → n-ua (prop-ext! (∥-∥-rec! λ (b , p , r) → subst _ (sym p) r) λ r → inc (a , refl , r))
Rel o .Precategory.idl _R_ = ext λ a c → n-ua (prop-ext! (∥-∥-rec! (λ (b , r , p) → subst _ p r)) λ r → inc (c , r , refl))
Rel o .Precategory.assoc _R₁_ _R₂_ _R₃_ = ext λ a c → 
  n-ua $ prop-ext! 
    (∥-∥-rec! λ (b , w , r₁) → ∥-∥-rec! (λ (b' , r₃ , r₂) → inc (_ , (r₃ , inc (_ , (r₂ , r₁))))) w) 
    (∥-∥-rec! λ (b , r₃ , w) → ∥-∥-rec! (λ (b' , r₂ , r₁) → inc (_ , inc (_ , (r₃ , r₂)) , r₁)) w)

Sets→Rel : ∀ {o} → Functor (Sets o) (Rel o)
Sets→Rel .Functor.F₀ A = A
Sets→Rel .Functor.F₁ f x y = el! (f x ≡ y)
Sets→Rel .Functor.F-id = refl
Sets→Rel .Functor.F-∘ f g = ext λ a c → n-ua (prop-ext! (λ p → inc (_ , refl , p)) (∥-∥-rec! (λ (b , p , q) → ap f p ∙ q)))

Rel^op→Rel : ∀ {o} → Functor (Rel o ^op) (Rel o)
Rel^op→Rel .Functor.F₀ A = A
Rel^op→Rel .Functor.F₁ _R_ a c = c R a
Rel^op→Rel .Functor.F-id = ext λ a c → n-ua (prop-ext! sym sym)
Rel^op→Rel .Functor.F-∘ _R₁_ _R₂_ = ext λ a c → 
  n-ua $ 
    prop-ext! 
      (∥-∥-rec! λ (b , r₁ , r₂) → inc (_ , r₂ , r₁)) 
      (∥-∥-rec! λ (b , r₂ , r₁) → inc (_ , r₁ , r₂))

open import Cat.Functor.Equivalence
open import Cat.Functor.Equivalence.Path

Rel^op≅Rel : ∀ {o} → Rel o ^op ≡ Rel o
Rel^op≅Rel = Precategory-path Rel^op→Rel λ where 
  .is-precat-iso.has-is-ff → is-iso→is-equiv λ where 
    .is-iso.inv _R_ a c → c R a
    .is-iso.rinv _ → refl
    .is-iso.linv _ → refl
  .is-precat-iso.has-is-iso → id-equiv



open import Cat.Instances.Sets.Counterexamples.SelfDual

_ : ∀ {o} → ¬ (Sets o ≡ Sets o ^op)
_ = Sets≠Sets^op



-- Power X ≡ Power X ^opp is true only if DNE/LEM holds!

-- open import Data.Power
-- open import Order.Base
-- open import Order.Instances.Power 
-- open import Order.Univalent


-- module _ {ℓ} (X : Type ℓ) where

  -- Power≡Power^opp : Power X ≡ Power X ^opp
  -- Power≡Power^opp = Poset-path λ where 
  --   .to → Invert _
  --   .from → Invert⁻ _
  --   .inverses .Inverses.invl → ext λ f a → Ω-ua {!   !} {!   !}
  --   .inverses .Inverses.invr → {!   !}
  --     where
  --       open import Cat.Morphism
   
open import Cat.Instances.Comma
open import Cat.Instances.Slice

Arrow : ∀ {o h} (C : Precategory o h) → Precategory _ _
Arrow C = Id {C = C} ↓ Id

module _ {o h} (C : Precategory o h) (c : C .Precategory.Ob) where

  SliceU : Functor (Slice C c) C
  SliceU .Functor.F₀ = /-Obj.domain
  SliceU .Functor.F₁ = /-Hom.map
  SliceU .Functor.F-id = refl
  SliceU .Functor.F-∘ _ _ = refl

  SliceF : Functor (Slice C c) (Arrow C)
  SliceF .Functor.F₀ x = ↓obj (x ./-Obj.map)
  SliceF .Functor.F₁ f .↓Hom.α = f ./-Hom.map
  SliceF .Functor.F₁ f .↓Hom.β = C .Precategory.id
  SliceF .Functor.F₁ f .↓Hom.sq = (f ./-Hom.commutes) ∙ (sym $ C .Precategory.idl _)
  SliceF .Functor.F-id = ↓Hom-path _ _ refl refl
  SliceF .Functor.F-∘ f g = ↓Hom-path _ _ refl (sym $ C .Precategory.idl _)

  slice→arrow→dom : Dom _ _ F∘ SliceF ≡ SliceU
  slice→arrow→dom = Functor-path (λ _ → refl) (λ f → refl)
 

-- open import Cat.Instances.Product
-- open import Cat.Instances.Discrete
-- open import Cat.Instances.Sets
-- open import Cat.Functor.Univalence
-- open import Data.Bool



-- 𝟚 : ∀ ℓ → Set ℓ
-- 𝟚 ℓ = el! (Lift ℓ Bool)

-- Total-Path : ∀ {ℓ} → Cat[ _ , Sets ℓ ] ≡ Slice (Sets ℓ) (𝟚 ℓ)
-- Total-Path {ℓ} = path where 
--   path : Cat[ _ , Sets ℓ ] ≡ Slice (Sets ℓ) (𝟚 ℓ)
--   path = Precategory-path (Total-space {I = 𝟚 ℓ}) $
--     is-equivalence→is-precat-iso _ (ff+split-eso→is-equivalence (Total-space-is-ff {I = 𝟚 ℓ}) (Total-space-is-eso {I = 𝟚 ℓ})) (Functor-is-category Sets-is-category) (slice-is-category Sets-is-category)

-- 𝟚-Path : ∀ {ℓ} → Cat[ Disc! (𝟚 ℓ) , Sets ℓ ] ≡ Sets ℓ ×ᶜ Sets ℓ
-- 𝟚-Path {ℓ} = Precategory-path 𝔽 precat-iso
--   where
--     𝔽 : Functor (Cat[ Disc! (𝟚 ℓ) , Sets ℓ ]) (Sets ℓ ×ᶜ Sets ℓ)
--     𝔽 .Functor.F₀ f = (f .Functor.F₀ (lift true)) , f .Functor.F₀ (lift false)
--     𝔽 .Functor.F₁ nt = nt ._=>_.η (lift true) , nt ._=>_.η (lift false)
--     𝔽 .Functor.F-id = refl
--     𝔽 .Functor.F-∘ f g = refl

--     homF : ∀ {x y} {a b : Set ℓ}  → Disc! (𝟚 ℓ) .Precategory.Hom x y → ∣ if x .Lift.lower then a else b ∣ → ∣ if y .Lift.lower then a else b ∣
--     homF {lift true} {lift true} p z = z
--     homF {lift false} {lift false} p z = z
--     homF {lift true} {lift false} p = absurd (true≠false (lift-inj p))
--     homF {lift false} {lift true} p = absurd (true≠false (lift-inj (sym p)))

--     precat-iso : is-precat-iso 𝔽
--     precat-iso .is-precat-iso.has-is-ff {x} {y} = is-iso→is-equiv the-iso
--       where
--         the-iso : is-iso (𝔽 .Functor.F₁ {x} {y})
--         the-iso .is-iso.inv (f , g) ._=>_.η (lift true) = f
--         the-iso .is-iso.inv (f , g) ._=>_.η (lift false) = g
--         the-iso .is-iso.inv (f , g) ._=>_.is-natural (lift true) (lift true) h =
--             f ⊙ (x .Functor.F₁ h) ≡⟨ ap (λ h → f ⊙ (x .Functor.F₁ h)) prop! ⟩ 
--             f ⊙ (x .Functor.F₁ refl) ≡⟨ ap (f ⊙_) (x .Functor.F-id) ⟩
--             f ≡˘⟨ ap (_⊙ f) (y .Functor.F-id) ⟩ 
--             (y .Functor.F₁ refl) ⊙ f ≡⟨ ap (λ h → y .Functor.F₁ h ⊙ f) prop! ⟩ 
--             (y .Functor.F₁ h) ⊙ f ∎
--         the-iso .is-iso.inv (f , g) ._=>_.is-natural (lift false) (lift false) h =
--             g ⊙ (x .Functor.F₁ h) ≡⟨ ap (λ h → g ⊙ (x .Functor.F₁ h)) prop! ⟩ 
--             g ⊙ (x .Functor.F₁ refl) ≡⟨ ap (g ⊙_) (x .Functor.F-id) ⟩
--             g ≡˘⟨ ap (_⊙ g) (y .Functor.F-id) ⟩ 
--             (y .Functor.F₁ refl) ⊙ g ≡⟨ ap (λ h → y .Functor.F₁ h ⊙ g) prop! ⟩ 
--             (y .Functor.F₁ h) ⊙ g ∎
--         the-iso .is-iso.inv (f , g) ._=>_.is-natural (lift true) (lift false) h = absurd (true≠false (lift-inj h))
--         the-iso .is-iso.inv (f , g) ._=>_.is-natural (lift false) (lift true) h = absurd (true≠false (sym (lift-inj h)))
--         the-iso .is-iso.rinv _ = refl
--         the-iso .is-iso.linv F = Nat-path λ where 
--             (lift true) → refl
--             (lift false) → refl
--     precat-iso .is-precat-iso.has-is-iso = is-iso→is-equiv the-iso
--       where
--         the-iso : is-iso (𝔽 .Functor.F₀)
--         the-iso .is-iso.inv (a , b) .Functor.F₀ = λ (lift x) → if x then a else b
--         the-iso .is-iso.inv (a , b) .Functor.F₁ = homF
--         the-iso .is-iso.inv (a , b) .Functor.F-id {lift true} = refl
--         the-iso .is-iso.inv (a , b) .Functor.F-id {lift false} = refl
--         the-iso .is-iso.inv (a , b) .Functor.F-∘ {lift true} {lift true} {lift true} f g = refl
--         the-iso .is-iso.inv (a , b) .Functor.F-∘ {lift false} {lift false} {lift false} f g = refl
--         the-iso .is-iso.inv (a , b) .Functor.F-∘ {lift true} {lift true} {lift false} f g = absurd (true≠false (lift-inj f))
--         the-iso .is-iso.inv (a , b) .Functor.F-∘ {lift true} {lift false} {lift true} f g = absurd (true≠false (sym $ lift-inj f))
--         the-iso .is-iso.inv (a , b) .Functor.F-∘ {lift true} {lift false} {lift false} f g = absurd (true≠false (lift-inj g))
--         the-iso .is-iso.inv (a , b) .Functor.F-∘ {lift false} {lift true} {lift true} f g = absurd (true≠false (sym $ lift-inj g))
--         the-iso .is-iso.inv (a , b) .Functor.F-∘ {lift false} {lift true} {lift false} f g = absurd (true≠false (lift-inj f))
--         the-iso .is-iso.inv (a , b) .Functor.F-∘ {lift false} {lift false} {lift true} f g = absurd (true≠false (sym $ lift-inj f))
--         the-iso .is-iso.rinv _ = refl
--         the-iso .is-iso.linv f = Functor-path path₁ path₂
--           where
--             path₁ : (x : Lift ℓ Bool) → (if x .Lift.lower then f .Functor.F₀ (lift true) else f .Functor.F₀ (lift false)) ≡ Functor.F₀ f x
--             path₁ (lift true) = refl
--             path₁ (lift false) = refl

--             path₂ : {x y : Disc! (𝟚 ℓ) .Precategory.Ob} (g : Disc! (𝟚 ℓ) .Precategory.Hom x y) → PathP (λ i → ∣ path₁ x i ∣ → ∣ path₁ y i ∣) (homF g) (f .Functor.F₁ g)
--             path₂ {lift true} {lift true} g = sym (ap (f .Functor.F₁) prop! ∙ (f .Functor.F-id))
--             path₂ {lift false} {lift false} g = sym (ap (f .Functor.F₁) prop! ∙ (f .Functor.F-id))
--             path₂ {lift true} {lift false} g = absurd (true≠false (lift-inj g))
--             path₂ {lift false} {lift true} g = absurd (true≠false (sym (lift-inj g)))


-- /2≡Pair-Ob : ∀ {ℓ} → Slice (Sets ℓ) (𝟚 ℓ) ≡ (Sets ℓ ×ᶜ Sets ℓ)
-- /2≡Pair-Ob {ℓ} = 
--   Slice (Sets ℓ) (𝟚 ℓ) ≡˘⟨ Total-Path ⟩ 
--   Cat[ _ , Sets ℓ ] ≡⟨ {!   !} ⟩ 
--   Cat[ Disc! (𝟚 ℓ) , Sets ℓ ] ≡⟨ 𝟚-Path ⟩
--   Sets ℓ ×ᶜ Sets ℓ ∎

-- /2→Pair : ∀ {ℓ} → Functor (Slice (Sets ℓ) (el! $ Lift ℓ Bool)) (Sets ℓ ×ᶜ Sets ℓ)
-- /2→Pair .Functor.F₀ (cut f) = (el! (fibre f (lift true))) , (el! (fibre f (lift false)))
-- /2→Pair .Functor.F₁ h = (λ (fib , p) → h ./-Hom.map fib , ap (_$ fib) (h ./-Hom.commutes) ∙ p) , (λ (fib , p) → h ./-Hom.map fib , ap (_$ fib) (h ./-Hom.commutes) ∙ p)
-- /2→Pair .Functor.F-id = ext ((λ x → Σ-prop-path! refl) , (λ x → Σ-prop-path! refl))
-- /2→Pair .Functor.F-∘ f g = ext ((λ x → Σ-prop-path! refl) , (λ x → Σ-prop-path! refl))
 
-- ^2≡Pair-is-iso : ∀ {ℓ} → is-precat-iso (^2≡Pair {ℓ})
-- ^2≡Pair-is-iso {ℓ} .is-precat-iso.has-is-ff {x} {y} = is-iso→is-equiv the-iso
--   where
--     the-iso : is-iso _
--     the-iso .is-iso.inv (f , g) ./-Hom.map a with inspect (x ./-Obj.map a)
--     ... | lift true , p = f (a , p) .fst
--     ... | lift false , p = g (a , p) .fst
--     the-iso .is-iso.inv (f , g) ./-Hom.commutes i a with inspect (x ./-Obj.map a)
--     ... | lift true , p with f (a , p)
--     ... | w = (w .snd ∙ sym p) i
--     the-iso .is-iso.inv (f , g) ./-Hom.commutes i a | lift false , p with g (a , p)
--     ... | w = (w .snd ∙ sym p) i
--     the-iso .is-iso.rinv (f , g) = ext ((λ a → Σ-prop-path! (help₁ a)) , (λ a → Σ-prop-path! (help₂ a)))
--       where
--         help₁ : (a : fibre (x ./-Obj.map) (lift true)) → (the-iso .is-iso.inv (f , g) ./-Hom.map (fst a)) ≡ f a .fst
--         help₁ a with inspect (x ./-Obj.map (a .fst)) 
--         ... | lift true , p = ap (λ x → f (a .fst , x) .fst) prop!
--         ... | lift false , p = absurd (true≠false (lift-inj ((sym $ a .snd) ∙ p)))

--         help₂ : (a : fibre (x ./-Obj.map) (lift false)) → (the-iso .is-iso.inv (f , g) ./-Hom.map (fst a)) ≡ g a .fst
--         help₂ a with inspect (x ./-Obj.map (a .fst))
--         ... | lift true , p = absurd (true≠false (lift-inj (sym p ∙ a .snd)))
--         ... | lift false , p = ap (λ x → g (a .fst , x) .fst) prop!
        
--     the-iso .is-iso.linv h = /-Hom-path (funext help)
--       where
--         help : _
--         help a with inspect (x ./-Obj.map a)
--         ... | lift true , p = refl
--         ... | lift false , p = refl
        
-- ^2≡Pair-is-iso .is-precat-iso.has-is-iso = is-iso→is-equiv the-iso
--   where
--     the-iso : is-iso _
--     the-iso .is-iso.inv (x , y) = {!   !}
--     the-iso .is-iso.rinv = {!   !}
--     the-iso .is-iso.linv = {!   !}
        
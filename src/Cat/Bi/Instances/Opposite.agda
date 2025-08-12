
open import Cat.Prelude
open import Cat.Bi.Base
open import Cat.Instances.Product
open import Cat.Functor.Naturality
open import Cat.Functor.Base
open import Cat.Functor.Bifunctor
open import Cat.Reasoning
open import Cat.Morphism.Duality

-- Taken from https://agda.github.io/agda-categories/Categories.Bicategory.Opposite.html
module Cat.Bi.Instances.Opposite {o ℓ ℓ'} (B : Prebicategory o ℓ ℓ') where


module B = Prebicategory B

open Prebicategory
open make-natural-iso
open _=>_
open _≅_
open Inverses
open is-invertible



-- Co : Prebicategory o ℓ ℓ'
-- Co .Ob = B.Ob
-- Co .Hom A B = B.Hom A B ^op
-- Co .id = B.id
-- Co .compose = Op B.compose
-- Co .unitor-l = iso→isoⁿ (λ x → iso→co-iso _ (_Iso⁻¹ _ (B.λ≅ x))) B.λ←nat 
-- Co .unitor-r = iso→isoⁿ (λ x → iso→co-iso _ (_Iso⁻¹ _ (B.ρ≅ x))) B.ρ←nat 
-- Co .associator = iso→isoⁿ (λ x → iso→co-iso _ (_Iso⁻¹ _ (B.α≅ _ _ _))) λ f → B.α←nat _ _ _
-- Co .triangle f g = ?
-- -- post-invr.to (B.Hom _ _) (record { inv = B.ρ← f B.◆ B.Hom.id ; inverses = {!   !} }) {!   !}
--   -- post-invl.to (B.Hom _ _) (iso→invertible _ (B.α≅ _ _ _)) {! B.triangle  !} 
--   -- B.α→ f B.id g B.∘ (B.ρ→ f) B.◀ g ≡⟨ conjugate-to (B.Hom _ _) {!  B.α≅  !} {!   !} {!   !} ⟩ 
--   -- {!   !} 
-- -- B.associator.to .η (f , B.id , g) B.Hom.∘
-- --       B.compose.F₁ (Cat.Morphism._≅_.to B.unitor-r .η f , B.Hom.id)
-- --       ≡ B.compose.F₁ (B.Hom.id , Cat.Morphism._≅_.to B.unitor-l .η g)
-- Co .pentagon = {!   !}


Op : Prebicategory o ℓ ℓ'
Op .Ob = B.Ob
Op .Hom A B = B.Hom B A
Op .id = B.id
Op .compose = B.compose F∘ Swap
Op .unitor-l = iso→isoⁿ B.ρ≅ λ f → sym (B.ρ→nat f)
Op .unitor-r = iso→isoⁿ B.λ≅ λ f → sym (B.λ→nat f)
Op .associator = iso→isoⁿ (λ (f , g , h) → _Iso⁻¹ _ (B.α≅ h g f)) (λ (a , b , c) → sym (B.α←nat c b a))
Op .triangle {A = A} {B} {C} f g = post-invr.to _ (iso→invertible _ (B.α≅ _ _ _)) (sym (B.triangle g f))
Op .pentagon f g h i = 
  
  {!  !}

  --post-invr.to (B.Hom _ _) (iso→invertible _ (B.α≅ _ _ _)) {!   !}
  -- (B.α→ i h (g B.⊗ f)) B.Hom.∘ (B.α→ (i B.⊗ h) g f)

  -- (i B.▶ B.α→ h g f ) B.∘ (B.α→ i (h B.⊗ g) f) B.∘ (B.α→ i h g B.◀ f) ≡⟨ B.Hom.assoc _ _ _ ⟩
  -- ((i B.▶ B.α→ h g f ) B.∘ (B.α→ i (h B.⊗ g) f)) B.∘ (B.α→ i h g B.◀ f) ≡⟨ {! sym (B.pentagon i h g f)!} ⟩
  -- (B.α→ i h (g B.⊗ f)) B.Hom.∘ (B.α→ (i B.⊗ h) g f) ∎


-- Want
-- (i B.▶ B.α→ h g f ) B.Hom.∘ (B.α→ i (h B.⊗ g) f) B.Hom.∘ (B.α→ i h g B.◀ f)
--                      ≡
-- (B.α→ i h (g B.⊗ f)) B.Hom.∘ (B.α→ (i B.⊗ h) g f)

-- Have
-- (B.α← i h g B.◀ f) B.∘ (B.α← i (h B.⊗ g) f) B.∘ (i B.▶ B.α← h g f)
--                      ≡
-- (B.α← (i B.⊗ h) g f) B.∘ (B.α← i h (g B.⊗ f))
--               



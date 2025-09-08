```agda
open import Cat.Prelude
open import Cat.Bi.Base
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Functor.Cartesian
open import Cat.Displayed.Instances.DisplayedFunctor
open import Cat.Displayed.Instances.TotalProduct
open import Cat.Bi.Displayed.Base
open import Cat.Bi.Displayed.Cartesian
open import Cat.Displayed.Base
open import Cat.Bi.Displayed.Instances.Fib
open import Cat.Displayed.Instances.FullSubcategory
open import Cat.Displayed.Instances.Pullback
open import Cat.Displayed.Functor
open import Cat.Displayed.Functor.Naturality
open import Cat.Displayed.Univalence.Reasoning

import Cat.Reasoning as CR
import Cat.Displayed.Reasoning as DR
import Cat.Displayed.Morphism as DM
import Cat.Displayed.Solver as DS

module Cat.Bi.Displayed.Instances.Cartesian.Fib where

module _ o ℓ o' ℓ' where
  open Cartesian-bifibration
  open 1-cell-cartesian-lift
  open 1-cell-cartesian
  open Functor
  open Displayed-functor
  open make-natural-iso[_]
  open _=>_
  open _=[_]=>_
  open Cartesian-lift
  open is-cartesian
  open is-fibred-functor

  private
    module Cat = Prebicategory-Hom-Reasoning (Cat o ℓ)
    module Fib = Bidisplayed-Hom[]-Reasoning (Fib o ℓ o' ℓ')
    module Disp = Bidisplayed-Hom[]-Reasoning (Displayed-cat o ℓ o' ℓ')

  module _ {A B : Cat.Ob} (f : A Cat.↦ B) (E : Fib.Ob[ B ]) where
    
    private
      module E = DR (E .fst)
      module B = Precategory B

    Fib-1-cart : 1-cell-cartesian-lift (Fib o ℓ o' ℓ') f E
    Fib-1-cart .A' = Change-of-base f (E .fst) , Change-of-base-fibration f _ (E .snd)
    Fib-1-cart .lifting = Change-of-base-functor f (E .fst) , Change-of-base-functor-fibred f _ (E .snd)
    Fib-1-cart .cartesian .universal¹ h g' = Factor f (E .fst) _ (g' .fst) , Factor-fibred f (E .fst) _ (g' .fst) (g' .snd)
    Fib-1-cart .cartesian .commutes¹ h g' = path→vertical-iso _ (Displayed-functor-pathp _ (λ _ → refl) (λ _ → refl) ,ₚ prop!)
    Fib-1-cart .cartesian .universal² {U' = U'} {h₁' = h₁' , _} {h₂' = h₂' , _} {g₁' = g₁' , _} {g₂' = g₂' , _} i₁ i₂ σ' = 
      NT' (λ x' → E.hom[ B.idl _ ∙∙ B.idr _ ∙∙ B.idr _ ] (γ' .η' x')) λ x' y' f → 
        E.cast[] $
          E.hom[] (E.hom[] (γ' .η' _) E.∘' h₁' .F₁' f) E.≡[]⟨ E.unwrap _ E.∙[] E.unwrapl _  ⟩
          γ' .η' _ E.∘' h₁' .F₁' f                      ∙∙[]⟨ γ' .is-natural' _ _ _ ⟩
          h₂' .F₁' f E.∘' γ' .η' _                     E.≡[]⟨ E.wrapr _ E.∙[] E.wrap _ ⟩
          E.hom[] (h₂' .F₁' f E.∘' E.hom[] (γ' .η' _)) ∎
      where
        module i₁ = Fib.Hom[]._≅[_]_ {A' = U'} {B' = E} i₁
        module i₂ = Fib.Hom[]._≅[_]_ {A' = U'} {B' = E} i₂
        γ' = i₂.from' Disp.∘' σ' Disp.∘' i₁.to' 

    Fib-1-cart .cartesian .commutes² {U' = U'} i₁ i₂ σ' = 
      Nat'-path λ {x} x' → 
        E.cast[] $ E.unwrapl _ E.∙[] E.idr' _

    Fib-1-cart .cartesian .unique² other p = 
      Nat'-path λ {x} x' → 
        E.cast[] $ (symP $ E.idr' _) E.∙∙[] p ηₚ' x' ∙∙[] E.wrap _

  module _ 
    {A B} {A' : Fib.Ob[ A ]} {B' : Fib.Ob[ B ]}
    where      
    
    private module B' where
        open DR (B' .fst) public
        open Cartesian-fibration _ (B' .snd) public

    Fib-2-cart : Cartesian-fibration Fib.Hom[ A' , B' ]
    Fib-2-cart = restrict-fibration _ _ (Disp[]-fibration (B' .snd)) λ {f = α} fib → is-fibred λ cart → 
      cartesian-cancell _ B'.π*.cartesian $
      subst₂ (is-cartesian _) (sym $ α .is-natural _ _ _) (symP $ B'.π*.commutesp _ _) $
      cartesian-∘ _ (fib .F-cartesian cart) B'.π*.cartesian

  
  module _ 
    {A B A' B'}
    {f g : A Cat.↦ B} {α : f Cat.⇒ g} 
    {f' : A' Fib.[ f ]↦ B'} {g' : A' Fib.[ g ]↦ B'} 
    {α' : (f' .fst) Disp.[ α ]⇒ (g' .fst)}  
    where

    private 
      module A' where
        open DR (A' .fst) public
        open DM (A' .fst) public

      module B' where
        open Cartesian-fibration _ (B' .snd) public
        open DR (B' .fst) public
        open DM (B' .fst) public

      module Fib[] where
        open DR Fib.Hom[ A' , B' ] public
        open DM Fib.Hom[ A' , B' ] public 
        open Cartesian-fibration _ (Fib-2-cart {A' = A'} {B' = B'}) public
      

    -- We already proved this for Disp[_,_]
    -- But because Fib[_,_] has more data than Disp[_,_] 
    -- we can't turn a Fib[] cartesian morphism into a Disp[] cartesian morphsim
    -- So we re-prove it here
    η'-cartesian-fib : is-cartesian Fib.Hom[ A' , B' ] {a' = f'} {b' = g'} α α' → ∀ {x} x' → is-cartesian (B' .fst) (α .η x) (α' .η' x')
    η'-cartesian-fib cart x' =
      cartesian-iso-stable _ 
        (iso[]ⁿ→iso _ (restrict-iso→iso _ _ $ cartesian-domain-unique _ cart Fib[].π*.cartesian) x')
        (B'.π*.commutesp (B .Precategory.idr _) _) 
        B'.π*.cartesian


  compose-fibred : ∀ {A B C A' B' C'} → is-fibred-functor (Fib.compose' {A} {B} {C} {A'} {B'} {C'})
  compose-fibred {A' = A'} {B'} {C'} .F-cartesian  {a' = F , G} {b' = H , K} {f = α , β} {f' = α' , β'} cart = 
    restrict-cartesian _ _ $ Disp[]-cartesian λ {x} x' →
      cartesian-∘ _ 
        (H .snd .F-cartesian (η'-cartesian-fib {A' = A'} {B' = B'} β'-cart x'))
        (η'-cartesian-fib {A' = B'} {B' = C'} α'-cart _)
    where
      α'-cart : is-cartesian Fib.Hom[ B' , C' ] α α'
      α'-cart = ×ᵀᴰ-cartesian _ _ cart .fst

      β'-cart : is-cartesian Fib.Hom[ A' , B' ] β β'
      β'-cart = ×ᵀᴰ-cartesian _ _ cart .snd


  Fib-bifibration : Cartesian-bifibration (Fib o ℓ o' ℓ')
  Fib-bifibration .1-cart = Fib-1-cart 
  Fib-bifibration .2-cart {A' = A'} {B' = B'} = Fib-2-cart {A' = A'} {B' = B'}
  Fib-bifibration .is-fibred-compose' {A' = A'} {B'} {C'} = compose-fibred {A' = A'} {B'} {C'}


```
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
    module Cat = Prebicategory (Cat o ℓ)
    module Fib = Bidisplayed (Fib o ℓ o' ℓ')
    module Disp = Bidisplayed (Displayed-cat o ℓ o' ℓ')


          

  module _ {A B : Cat.Ob} (f : A Cat.↦ B) ((E , E*) : Fib.Ob[ B ]) where
    
    private
      module E = DR E
      module B = Precategory B

    private
      univ : ∀ {U U'} (m : U Cat.↦ A) (h' : U' Fib.[ f Cat.⊗ m ]↦ (E , E*)) → Displayed-functor m (U' .fst) (Change-of-base f E)
      univ m h' .F₀' = h' .fst .F₀'
      univ m h' .F₁' = h' .fst .F₁'
      univ m h' .F-id' = E.cast[] $ h' .fst .F-id' E.∙[] E.wrap _
      univ m h' .F-∘' = E.cast[] $ h' .fst .F-∘' E.∙[] E.wrap _

      univ-fibred : ∀ {U U'} (m : U Cat.↦ A) (h' : U' Fib.[ f Cat.⊗ m ]↦ (E , E*)) → is-fibred-functor (univ {U} {U'} m h')
      univ-fibred m h' .F-cartesian cart = Change-of-base-cartesian _ _ (h' .snd .F-cartesian cart)

    Fib-1-cart : 1-cell-cartesian-lift (Fib o ℓ o' ℓ') f (E , E*)
    Fib-1-cart .A' = Change-of-base f E , Change-of-base-fibration f E E*
    Fib-1-cart .lifting = Change-of-base-functor f E , Change-of-base-functor-fibred _ _ E*
    Fib-1-cart .cartesian .universal¹ {U} {U'} m h' = univ {U} {U'} m h' , univ-fibred {U} {U'} m h'
    Fib-1-cart .cartesian .commutes¹ m h' = iso→restrict-iso _ _ $ to-natural-iso' ni where
      ni : make-natural-iso[ _ ] _ _
      ni .eta' _ = E.id'
      ni .inv' _ = E.id'
      ni .eta∘inv' _ = E.idl' _
      ni .inv∘eta' _ = E.idl' _
      ni .natural' x' y' f' = E.id-comm-sym[]
    Fib-1-cart .cartesian .universal² δ σ = NT' (λ x' → E.hom[ B.idr _ ] (σ .η' x')) λ x' y' f → 
      E.cast[] $ (E.unwrap _) E.∙∙[] (E.unwrapl _) E.∙∙[] σ .is-natural' _ _ _ ∙∙[] E.wrapr _ ∙∙[] E.wrap _
    Fib-1-cart .cartesian .commutes² δ σ = Nat'-path λ x' → E.cast[] $ (E.unwrap _ E.⟩∘'⟨refl) E.∙[] (symP $ E.idl' _)
    Fib-1-cart .cartesian .unique² σ δ' p = Nat'-path λ x' → E.from-pathp[]⁻ $ E.cast[] $ ((symP $ E.idr' _) E.∙∙[] (p ηₚ' x') ∙∙[] (E.idl' _ E.∙[] E.idr' _))

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
    -- But because Fib[_,_] has more data than Disp[_,_], 
    -- we can't turn a Fib[] cartesian morphism into a Disp[] cartesian morphsim
    -- So we re-prove it here
    η'-cartesian-fib : is-cartesian Fib.Hom[ A' , B' ] {a' = f'} {b' = g'} α α' → ∀ {x} x' → is-cartesian (B' .fst) (α .η x) (α' .η' x')
    η'-cartesian-fib cart x' =
      domain-iso→cartesian _ 
        (iso[]ⁿ→iso _ (restrict-iso→iso _ _ $ cartesian-domain-unique _ cart Fib[].π*.cartesian) x')
        (B'.π*.commutesp (B .Precategory.idr _) _) 
        B'.π*.cartesian


  compose-fibred : ∀ {A B C A' B' C'} → is-fibred-functor (Fib.compose' {A} {B} {C} {A'} {B'} {C'})
  compose-fibred {A} {B} {C} {A'} {B'} {C'} .F-cartesian  {a' = F , G} {b' = H , K} {f = α , β} {f' = α' , β'} cart = ◆'-cart where
      
    α'-cart : is-cartesian Fib.Hom[ B' , C' ] α α'
    α'-cart = ×ᵀᴰ-cartesian _ _ cart .fst

    β'-cart : is-cartesian Fib.Hom[ A' , B' ] β β'
    β'-cart = ×ᵀᴰ-cartesian _ _ cart .snd

    ◆'-cart : is-cartesian _ _ _
    ◆'-cart = restrict-cartesian _ _ $ Disp[]-cartesian λ {x} x' →
      cartesian-∘ _ 
        (H .snd .F-cartesian (η'-cartesian-fib {A' = A'} {B' = B'} β'-cart x'))
        (η'-cartesian-fib {A' = B'} {B' = C'} α'-cart _)

  Fib-bifibration : Cartesian-bifibration (Fib o ℓ o' ℓ')
  Fib-bifibration .1-cart = Fib-1-cart 
  Fib-bifibration .2-cart {A' = A'} {B' = B'} = Fib-2-cart {A' = A'} {B' = B'}
  Fib-bifibration .is-fibred-compose' {A' = A'} {B'} {C'} = compose-fibred {A' = A'} {B'} {C'}

```
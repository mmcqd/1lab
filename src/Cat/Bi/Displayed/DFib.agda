open import Cat.Prelude
open import Cat.Bi.Base
open import Cat.Bi.Displayed.Base
open import Cat.Displayed.Base
open import Cat.Displayed.Functor
open import Cat.Displayed.Functor.Naturality
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Cartesian.Discrete
open import Cat.Bi.Displayed.Cartesian
open import Cat.Displayed.Instances.Pullback
open import Cat.Displayed.Instances.Identity
open import Cat.Displayed.Composition
open import Cat.Displayed.Functor
open import Cat.Displayed.Total renaming (∫ to ∫' ; πᶠ to πᶠ' ; ∫ᶠ to ∫ᶠ')
open import Cat.Functor.Adjoint
import Cat.Reasoning as CR
import Cat.Displayed.Reasoning as DR

module Cat.Bi.Displayed.DFib where

module _ o ℓ o' ℓ' where

  private
    module Cat = Prebicategory (Cat o ℓ)
    module Disp = Bidisplayed (Displayed-cat o ℓ o' ℓ')

  open _=>_
  open _=[_]=>_
  open Functor

  DFib : Bidisplayed (Cat o ℓ) _ _ _
  DFib .Bidisplayed.Ob[_] C = Σ Disp.Ob[ C ] is-discrete-cartesian-fibration
  DFib .Bidisplayed.Hom[_,_] (A , _) (B , _) = Disp.Hom[ A , B ]
  DFib .Bidisplayed.↦id' = Disp.↦id'
  DFib .Bidisplayed.compose' = Disp.compose'
  DFib .Bidisplayed.unitor-l' = Disp.unitor-l'
  DFib .Bidisplayed.unitor-r' = Disp.unitor-r'
  DFib .Bidisplayed.associator' = to-natural-iso' ni where
    -- We have to do some manual eta expansion to make the types work out
    ni : make-natural-iso[ _ ] _ _
    ni .make-natural-iso[_].eta' = Disp.associator'.to' .η'
    ni .make-natural-iso[_].inv' = Disp.associator'.from' .η'
    ni .make-natural-iso[_].eta∘inv' x' = apd (λ _ z → z .η' x') Disp.associator'.invl'
    ni .make-natural-iso[_].inv∘eta' x' = apd (λ _ z → z .η' x') Disp.associator'.invr'
    ni .make-natural-iso[_].natural' x' y' f' = Disp.associator'.to' .is-natural' x' y' f'
  DFib .Bidisplayed.triangle' = Disp.triangle'
  DFib .Bidisplayed.pentagon' = Disp.pentagon'
  
  private module DFib = Bidisplayed DFib


  open Bicartesian-fibration
  open 1-cell-cartesian
  open Bicartesian-lift
  open Cartesian-lift
  open is-cartesian
  open Cartesian-morphism
  open Cartesian-lift
  open Displayed-functor
  open make-natural-iso[_]

  module _ 
    {A B}
    (f : A Cat.↦ B) 
    ((B' , B'*) : DFib.Ob[ B ]) 
    where 
    private
      module B = CR B
      module B' where
        open Displayed B' public
        open is-discrete-cartesian-fibration B'* public
        open DR B' public

    
    private
      univ : ∀ {U U'} (m : U Cat.↦ A) (h' : U' DFib.[ f Cat.⊗ m ]↦ (B' , B'*)) → U' DFib.[ m ]↦ (Change-of-base f B' , Change-of-base-discrete-fibration f B' B'*)
      univ m h' .F₀' = h' .F₀'
      univ m h' .F₁' = h' .F₁'
      univ m h' .F-id' = is-prop→pathp (λ _ → hlevel 1) _ _
      univ m h' .F-∘' = is-prop→pathp (λ _ → hlevel 1) _ _

    DFib-1-cart : Bicartesian-lift DFib f (B' , B'*)
    DFib-1-cart .A' = Change-of-base f B' , Change-of-base-discrete-fibration f _ B'*
    DFib-1-cart .lifting = Change-of-base-functor f B'
    DFib-1-cart .cartesian .universal¹ {U} {U'} = univ {U} {U'}
    DFib-1-cart .cartesian .commutes¹ m h' = to-natural-iso' ni where
      ni : make-natural-iso[ _ ] _ _
      ni .eta' _ = B'.id'
      ni .inv' _ = B'.id'
      ni .eta∘inv' _ = B'.idl' _ 
      ni .inv∘eta' _ = B'.idl' _ 
      ni .natural' x' y' f' = B'.id-comm-sym[]
    DFib-1-cart .cartesian .universal² δ σ .η' x' = B'.hom[ B.idr _ ] (σ .η' x')
    DFib-1-cart .cartesian .universal² δ σ .is-natural' x' y' f' = is-prop→pathp (λ _ → hlevel 1) _ _
    DFib-1-cart .cartesian .commutes² δ σ = Nat'-path λ _ → is-prop→pathp (λ _ → hlevel 1) _ _
    DFib-1-cart .cartesian .unique² σ δ' x = Nat'-path λ _ → is-prop→pathp (λ _ → hlevel 1) _ _

  module _ 
    {A B} {A' : DFib.Ob[ A ]} {B' : DFib.Ob[ B ]}
    {f g : A Cat.↦ B}
    (α : f Cat.⇒ g)
    (g' : A' DFib.[ g ]↦ B') 
    where
    private
      module f = Functor f
      module g = Functor g
      module g' = Displayed-functor g'
      module α = _=>_ α
      module B = CR B
      module B' where
        open Displayed (B' .fst) public
        open is-discrete-cartesian-fibration (B' .snd) public
        open DR (B' .fst) public

    private
      α^*g' : Displayed-functor f (A' .fst) (B' .fst)
      α^*g' .F₀' {x} x' = (α.η x) B'.^* (g'.₀' x')
      α^*g' .F₁' {a} {b} {f = h} {a'} {b'} h' = B'.^*-hom _ $ 
        f.₁ h B'.^* (α.η b B'.^* g'.₀' b')    ≡˘⟨ B'.^*-∘ _ _ _ ⟩
        ⌜ α.η b B.∘ f.₁ h ⌝ B'.^* g'.₀' b'    ≡⟨ ap! (α.is-natural _ _ _) ⟩
        (g.₁ h B.∘ α.η a) B'.^* g'.₀' b'      ≡⟨ B'.^*-∘ _ _ _ ⟩
        α.η a B'.^* ⌜ g.₁ h B'.^* g'.₀' b' ⌝  ≡⟨ ap! (B'.^*-lift _ (g'.₁' h')) ⟩ 
        α.η a B'.^* g'.F₀' a'                 ∎ 
      α^*g' .F-id' = is-prop→pathp (λ _ → hlevel 1) _ _
      α^*g' .F-∘' = is-prop→pathp (λ _ → hlevel 1) _ _
      
    DFib-2-cart : Cartesian-lift DFib.Hom[ A' , B' ] α g'
    DFib-2-cart .x' = α^*g'
    DFib-2-cart .lifting .η' {x} x' = B'.π* (α.η x) (g'.₀' x')
    DFib-2-cart .lifting .is-natural' _ _ _ = is-prop→pathp (λ _ → hlevel 1) _ _
    DFib-2-cart .cartesian .universal {u = u} {u' = u'} m h' .η' {x} x' = B'.^*-hom _ $ 
      m.η x B'.^* (α.η x B'.^* g'.₀' x') ≡˘⟨ B'.^*-∘ _ _ _ ⟩
      (α.η x B.∘ m.η x) B'.^* g'.₀' x'   ≡⟨ B'.^*-lift (α.η x B.∘ m.η x) (h'.η' x') ⟩
      u'.₀' x' ∎
      where
        module u = Functor u
        module u' = Displayed-functor u'
        module m = _=>_ m
        module h' = _=[_]=>_ h'
    DFib-2-cart .cartesian .universal m h' .is-natural' _ _ _ = is-prop→pathp (λ _ → hlevel 1) _ _
    DFib-2-cart .cartesian .commutes m h' = Nat'-path (λ _ → is-prop→pathp (λ _ → hlevel 1) _ _)
    DFib-2-cart .cartesian .unique m' x = Nat'-path (λ _ → is-prop→pathp (λ _ → hlevel 1) _ _)

  module _ 
    {A B C A' B' C'} {f₁ f₂ : B Cat.↦ C} {f₁' : B' DFib.[ f₁ ]↦ C'} {f₂' : B' DFib.[ f₂ ]↦ C'}
    {α : f₁ Cat.⇒ f₂} {α' : f₁' Disp.[ α ]⇒ f₂'}
    {g₁ g₂ : A Cat.↦ B} {g₁' : A' DFib.[ g₁ ]↦ B'} {g₂' : A' DFib.[ g₂ ]↦ B'}
    {β : g₁ Cat.⇒ g₂} {β' : g₁' Disp.[ β ]⇒ g₂'} 
    (c1 : is-cartesian DFib.Hom[ B' , C' ] α α')
    (c2 : is-cartesian DFib.Hom[ A' , B' ] β β')
    where
    private
      module α = _=>_ α
      module β = _=>_ β
      module α' = _=[_]=>_ α'
      module β' = _=[_]=>_ β'

      module C = CR C
      module C' where
        open Displayed (C' .fst) public
        open DR (C' .fst) public
        open is-discrete-cartesian-fibration (C' .snd) public

      module c1 = is-cartesian c1
      module c2 = is-cartesian c2

    DFib-◆'-cart : is-cartesian DFib.Hom[ A' , C' ] (α Cat.◆ β) (α' Disp.◆' β')
    DFib-◆'-cart .universal {u = u} {u' = u'} m h' .η' {x} x' = C'.^*-hom _ $
      m.η x C'.^* ⌜ (f₁' Disp.⊗' g₁') .F₀' x' ⌝                      ≡˘⟨ ap¡ (C'.^*-lift _ ((α' Disp.◆' β') .η' x')) ⟩ 
      m.η x C'.^* ((α Cat.◆ β) .η x C'.^* (f₂' Disp.⊗' g₂') .F₀' x') ≡˘⟨ C'.^*-∘ _ _ _ ⟩
      ((α Cat.◆ β) .η x C.∘ m.η x) C'.^* (f₂' Disp.⊗' g₂') .F₀' x'   ≡⟨ C'.^*-lift _ (h'.η' x') ⟩
      u'.F₀' x'                                                      ∎

      where
        module h' = _=[_]=>_ h'
        module m = _=>_ m
        module u' = Displayed-functor u'
    DFib-◆'-cart .universal m h' .is-natural' _ _ _ = is-prop→pathp (λ _ → hlevel 1) _ _
    DFib-◆'-cart .commutes _ _ = Nat'-path (λ _ → is-prop→pathp (λ _ → hlevel 1) _ _)
    DFib-◆'-cart .unique _ _ = Nat'-path (λ _ → is-prop→pathp (λ _ → hlevel 1) _ _)



  DFib-bicartesian : Bicartesian-fibration DFib
  DFib-bicartesian .1-cart = DFib-1-cart
  DFib-bicartesian .2-cart {A' = A'} {B'} = DFib-2-cart {A' = A'} {B'}
  DFib-bicartesian .◆'-cart {A' = A'} {B'} {C'} = DFib-◆'-cart {A' = A'} {B'} {C'}

module _ {o' ℓ'} where
  private
    module DFib {o ℓ} = Bidisplayed (DFib o ℓ o' ℓ')
    module Disp {o ℓ} = Bidisplayed (Displayed-cat o ℓ o' ℓ)

  ∫ : ∀ {o ℓ} {A : Precategory o ℓ} → DFib.Ob[ A ] → Precategory _ _
  ∫ (E , _) = ∫' E

  πᶠ : ∀ {o ℓ} {A : Precategory o ℓ} (E : DFib.Ob[ A ]) → Functor (∫ E) A
  πᶠ (E , _) = πᶠ' E

  DFibΣ : ∀ {o ℓ} {A : Precategory o ℓ} (E : DFib.Ob[ A ]) → DFib.Ob[ ∫ E ] → DFib.Ob[ A ]
  DFibΣ (E , E*) (E' , E'*) = (E D∘ E') , discrete-∘ E* E'*

  is-representable : ∀ {o ℓ} {A : Precategory o ℓ} (E : DFib.Ob[ A ]) → DFib.Ob[ ∫ E ] → Type _
  is-representable E E' = Σ[ δ ∈ Functor (∫ E) (∫ E') ] πᶠ E' ⊣ δ

 
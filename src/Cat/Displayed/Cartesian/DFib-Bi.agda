

open import Cat.Prelude
open import Cat.Displayed.Base
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Cartesian.Discrete
open import Cat.Instances.Functor
open import Cat.Displayed.Functor
open import Cat.Displayed.Total renaming (∫ to ∫' ; πᶠ to πᶠ' ; ∫ᶠ to ∫ᶠ')
import Cat.Displayed.Reasoning as DR

module Cat.Displayed.Cartesian.DFib-Bi where

-- Conceptually, DFib is displayed 2-category (not bicategory!) over Cat
-- We're going to define a fragment of this structure without having to actually define displayed 2-categories


DFib-Ob : ∀ {o ℓ} → Precategory o ℓ → ∀ o' ℓ' → Type _
DFib-Ob 𝒮 o' ℓ' = Σ (Displayed 𝒮 o' ℓ') is-discrete-cartesian-fibration

∫ : ∀ {o ℓ o' ℓ'} {𝒮 : Precategory o ℓ} → DFib-Ob 𝒮 o' ℓ' → Precategory _ _
∫ (A , _) = ∫' A

πᶠ : ∀ {o ℓ o' ℓ'} {𝒮 : Precategory o ℓ} (A : DFib-Ob 𝒮 o' ℓ') → Functor (∫ A) 𝒮 
πᶠ (A , _) = πᶠ' A




module DFib-Ob {o ℓ o' ℓ'} {𝒮 : Precategory o ℓ} ((A , A*) : DFib-Ob 𝒮 o' ℓ') where
  open Displayed A public
  open DR A public
  open Cartesian-fibration A (discrete→cartesian A A*) public
  open is-discrete-cartesian-fibration A* hiding (_^*_ ; π*) public

record DFib-functor 
  {ob ℓb oc ℓc ox ℓx oy ℓy} {B : Precategory ob ℓb} {C : Precategory oc ℓc}
  (F : Functor B C) 
  (x : DFib-Ob B ox ℓx) (y : DFib-Ob C oy ℓy) : Type (ob ⊔ ℓb ⊔ oc ⊔ ℓc ⊔ ox ⊔ ℓx ⊔ oy ⊔ ℓy) where
  constructor hom
  field
    fun : Displayed-functor F (x .fst) (y .fst)

  open Displayed-functor fun public

open DFib-functor

module _ 
  {ob ℓb oc ℓc od ℓd oe ℓe} 
  {B : Precategory ob ℓb} {C : Precategory oc ℓc} 
  {D : DFib-Ob B od ℓd} {E : DFib-Ob C oe ℓe} 
  {F : Functor B C}
  (F' : DFib-functor F D E)
   where

  ∫ᶠ : Functor (∫ D) (∫ E)
  ∫ᶠ = ∫ᶠ' (F' .fun)

Vertical-DFib-functor 
  : ∀ {o ℓ ox ℓx oy ℓy} {B : Precategory o ℓ}
  → (x : DFib-Ob B ox ℓx) (y : DFib-Ob B oy ℓy)
  → Type _
Vertical-DFib-functor = DFib-functor Id

module _ 
  {o ℓ ox ℓx oy ℓy} {A B : Precategory o ℓ}
  {F : Functor A B} 
  {ℰ : DFib-Ob A ox ℓx} {ℱ : DFib-Ob B oy ℓy} where
  private
    module A = Precategory A
    module ℰ = DFib-Ob ℰ
    module ℱ = DFib-Ob ℱ
    unquoteDecl eqv = declare-record-iso eqv (quote DFib-functor)
    unquoteDecl eqv' = declare-record-iso eqv' (quote Displayed-functor)


  open Functor
  open Displayed-functor
  DFib-functor-pathp 
    : {G : Functor A B} 
    → {F' : DFib-functor F ℰ ℱ} {G' : DFib-functor G ℰ ℱ}
    → (p : F ≡ G)
    → (q0 : ∀ {x} → (x' : ℰ.Ob[ x ]) → PathP (λ i → ℱ.Ob[ p i .F₀ x ]) (F' .fun .F₀' x') (G' .fun .F₀' x'))
    → (q1 : ∀ {x y x' y'} {f : A.Hom x y} → (f' : ℰ.Hom[ f ] x' y')
        → PathP (λ i → ℱ.Hom[ p i .F₁ f ] (q0 x' i) (q0 y' i)) (F' .fun .F₁' f') (G' .fun .F₁' f'))
    → PathP (λ i → DFib-functor (p i) ℰ ℱ) F' G'
  DFib-functor-pathp {F' = (hom F')} {G' = (hom G')} p q0 q1 i .fun = Displayed-functor-pathp {F' = F'} {G' = G'} p q0 q1 i

  instance
    DFib-functor-set : ∀ {n} → H-Level (DFib-functor F ℰ ℱ) (2 + n)
    DFib-functor-set = basic-instance 2 (Iso→is-hlevel 2 eqv (Displayed-functor-is-set ℱ.fibre-set))

open Displayed-functor
module DFib {o ℓ} o' ℓ' where

  -- For each object in Cat, a type of displayed objects
  DFib[_] : Precategory o ℓ → Type _
  DFib[ A ] = Σ (Displayed A o' ℓ') is-discrete-cartesian-fibration

  module _ {A B} (A' : DFib[ A ]) (B' : DFib[ B ]) where
    open _=[_]=>_
    open _=>_
    private
      module A = Precategory A
      module B = Precategory B
      module A' = DFib-Ob A'
      module B' = DFib-Ob B'

    -- For each pair of displayed objects and a displayed category over Cat[ A , B ]
    -- Discrete fibrations have trivial hom structure, 
    DFibHom[_,_] : Displayed (Cat[ A , B ]) _ _
    DFibHom[_,_] .Displayed.Ob[_] f = Displayed-functor f (A' .fst) (B' .fst)
    DFibHom[_,_] .Displayed.Hom[_] α F' G' = ∀ {x} (x' : A'.Ob[ x ]) → B'.Hom[ α .η x ] (F' .F₀' x') (G' .F₀' x')
    DFibHom[_,_] .Displayed.Hom[_]-set _ _ _ = hlevel 2
    DFibHom[_,_] .Displayed.id' x' = B'.id'
    DFibHom[_,_] .Displayed._∘'_ f' g' x' = f' x' B'.∘' g' x' 
    DFibHom[_,_] .Displayed.idr' _ = is-prop→pathp (λ _ → hlevel 1) _ _
    DFibHom[_,_] .Displayed.idl' _ = is-prop→pathp (λ _ → hlevel 1) _ _ 
    DFibHom[_,_] .Displayed.assoc' _ _ _ = is-prop→pathp (λ _ → hlevel 1) _ _


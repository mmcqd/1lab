```agda 

open import Cat.Prelude
open import Cat.Bi.Base
open import Cat.Bi.Instances.Opposite
open import Cat.Bi.Displayed.Base
open import Cat.Bi.Displayed.Cartesian
open import Cat.Displayed.Base
open import Cat.Functor.Base
open import Cat.Displayed.Functor
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Cartesian.Discrete
open import Cat.Displayed.Instances.TotalProduct

import Cat.Reasoning as Cr

module Cat.Bi.Displayed.Discrete where

-- module _ 
--   {o oh ℓh}
--   (B : Prebicategory o oh ℓh)
--   where
--   open Prebicategory B
--   open import Data.Set.Truncation


--   U : Precategory _ _
--   U .Precategory.Ob = Ob
--   U .Precategory.Hom a b = ∥ a ↦ b ∥₀
--   U .Precategory.Hom-set _ _ = hlevel 2
--   U .Precategory.id = inc id
--   U .Precategory._∘_ = elim! λ f g → inc (f ⊗ g)
--   U .Precategory.idr = elim! λ f → {! λ≅ !}
--   U .Precategory.idl = {!   !}
--   U .Precategory.assoc = {!   !}

```

A discrete bifibration should be one where each of its fibre bicategories is locally discrete, that is, it has
fibre *categories*.

```agda 

module _ {o oh ℓh o' oh' ℓh'} {B : Prebicategory o oh ℓh} (E : Bidisplayed B o' oh' ℓh') where
  open Prebicategory B hiding (module Hom)
  private module Hom {A B} = Cr (Hom A B)
    
  open Bidisplayed E
  open 1-cell-cartesian-lift

  record is-discrete-cartesian-bifibration : Type (o ⊔ oh ⊔ ℓh ⊔ o' ⊔ oh' ⊔ ℓh') where
    no-eta-equality
    field 
      1-cart : ∀ {A B} (f : A ↦ B) (B' : Ob[ B ]) → 1-cell-pre-cartesian-lift E f B'
      2-cart : ∀ {A B} {A' : Ob[ A ]} {B' : Ob[ B ]} → is-discrete-cartesian-fibration Hom[ A' , B' ]
    module _ {A B} (f : A ↦ B) (B' : Ob[ B ]) where
      open 1-cell-pre-cartesian-lift (1-cart f B') 
        using () 
        renaming (A' to _^*1_ ; lifting to π*1)
        public
  
    module π*1 {A B} {f : A ↦ B} {B' : Ob[ B ]} where
       open 1-cell-pre-cartesian-lift (1-cart f B') 
        hiding (A' ; lifting)
        public

    module _ {A B} {A' : Ob[ A ]} {B' : Ob[ B ]} where
      open is-discrete-cartesian-fibration (2-cart {A} {B} {A'} {B'})
        renaming (_^*_ to _^*2_ ; π* to π*2)
        public
  
  module _ (E* : is-discrete-cartesian-bifibration) where
    open is-discrete-cartesian-bifibration E*
    open 1-cell-cartesian

    discrete→bifibration : Cartesian-bifibration E
    discrete→bifibration .Cartesian-bifibration.1-cart f B' .A' = f ^*1 B'
    discrete→bifibration .Cartesian-bifibration.1-cart f B' .lifting = π*1 f B'
    discrete→bifibration .Cartesian-bifibration.1-cart f B' .cartesian .pre-cartesian = π*1.pre-cartesian
    discrete→bifibration .Cartesian-bifibration.1-cart f B' .cartesian .commutes² _ _ = prop!
    discrete→bifibration .Cartesian-bifibration.1-cart f B' .cartesian .unique² _ _ _ = prop!
    discrete→bifibration .Cartesian-bifibration.2-cart = discrete→cartesian _ 2-cart
    discrete→bifibration .Cartesian-bifibration.is-fibred-compose' .is-fibred-functor.F-cartesian _ = all-cartesian _

    idempunitor : ∀ {a} → id Hom.≅ (id ⊗ id)
    idempunitor {a} = λ≅ $ id {a}
    Fibre : Ob → Precategory _ _ 
    Fibre X .Precategory.Ob = Ob[ X ]
    Fibre X .Precategory.Hom a b = a [ id ]↦ b
    Fibre X .Precategory.Hom-set _ _ = fibre-set id
    Fibre X .Precategory.id = ↦id'
    Fibre X .Precategory._∘_ f g = (λ→ id) ^*2 (f ⊗' g)
    Fibre X .Precategory.idr f = ^*-lift _ (Hom[].hom[ {!   !} ] (ρ→' f))
    Fibre X .Precategory.idl f = {!   !}
    Fibre X .Precategory.assoc = {!   !} 

    -- Reindex : ∀ {A B} → Functor (Hom B A ^op) Cat[ Fibre A , Fibre B ]
    -- Reindex {A} {B} .Functor.F₀ x .Functor.F₀ y = x ^*1 y
    -- Reindex {A} {B} .Functor.F₀ x .Functor.F₁ {x = a} {y = b} f = {! π*1  !}
    -- Reindex {A} {B} .Functor.F₀ x .Functor.F-id = {!   !}
    -- Reindex {A} {B} .Functor.F₀ x .Functor.F-∘ = {!   !}
    -- Reindex .Functor.F₁ = {!   !}
    -- Reindex .Functor.F-id = {!   !}
    -- Reindex .Functor.F-∘ = {!   !}

    -- open Pseudofunctor
    -- open Lax-functor

    -- discrete→cat-psh : Pseudofunctor (B ^Coop) (Cat _ _)
    -- discrete→cat-psh .lax .P₀ = Fibre
    -- discrete→cat-psh .lax .P₁ = {!   !}
    -- discrete→cat-psh .lax .compositor = {!   !}
    -- discrete→cat-psh .lax .unitor = {!   !}
    -- discrete→cat-psh .lax .hexagon = {!   !}
    -- discrete→cat-psh .lax .right-unit = {!   !}
    -- discrete→cat-psh .lax .left-unit = {!   !}
    -- discrete→cat-psh .unitor-inv = {!   !}
    -- discrete→cat-psh .compositor-inv = {!   !}

```
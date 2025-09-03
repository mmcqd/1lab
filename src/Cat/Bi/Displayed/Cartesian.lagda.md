```agda

open import Cat.Prelude
open import Cat.Displayed.Base
open import Cat.Displayed.Functor
open import Cat.Displayed.Cartesian
open import Cat.Bi.Base
open import Cat.Bi.Displayed.Base
open import Cat.Displayed.Instances.DisplayedFunctor hiding (_◆'_)
open import Cat.Morphism hiding (Ob ; Hom)
open import Cat.Instances.Product

import Cat.Displayed.Reasoning as DR
import Cat.Displayed.Morphism as DM


module Cat.Bi.Displayed.Cartesian where

-- Definition and proofs taken from https://arxiv.org/pdf/1212.6283

module _ {o oh ℓh o' oh' ℓh'} {B : Prebicategory o oh ℓh} (E : Bidisplayed B o' oh' ℓh') where

  open Prebicategory B 
  open Bidisplayed E hiding (module Hom[])

  private module Hom[] {A B} {A' : Ob[ A ]} {B' : Ob[ B ]} where
    open DM Hom[ A' , B' ] public
    open DR Hom[ A' , B' ] public
  

  

  open is-cartesian

  Locally-cartesian : Type _
  Locally-cartesian = ∀ {A B} {A' : Ob[ A ]} {B' : Ob[ B ]} → Cartesian-fibration (Hom[ A' , B' ])

  record 1-cell-pre-cartesian {A B A' B'} (f : A ↦ B) (f' : A' [ f ]↦ B') : Type (o ⊔ o' ⊔ oh ⊔ oh' ⊔ ℓh ⊔ ℓh') where
    no-eta-equality
    field 
      universal¹ : ∀ {U U'} (m : U ↦ A) (h' : U' [ f ⊗ m ]↦ B') → U' [ m ]↦ A'
      commutes¹ : ∀ {U U'} (m : U ↦ A) (h' : U' [ f ⊗ m ]↦ B') 
                  → (f' ⊗' universal¹ m h') Hom[].≅↓ h'
      universal² : ∀ {U U'} {m₁ m₂ : U ↦ A} 
              → (δ : m₁ ⇒ m₂) 
              → {h₁' : U' [ f ⊗ m₁ ]↦ B'} {h₂' : U' [ f ⊗ m₂ ]↦ B'}
            → (σ : h₁' [ f ▶ δ ]⇒ h₂')
              → universal¹ m₁ h₁' [ δ ]⇒ universal¹ m₂ h₂' 
      
    module comm¹ {U U'} {m : U ↦ A} {h' : U' [ f ⊗ m ]↦ B'} = Hom[]._≅[_]_ (commutes¹ m h')
    
  record 1-cell-cartesian {A B A' B'} (f : A ↦ B) (f' : A' [ f ]↦ B') : Type (o ⊔ o' ⊔ oh ⊔ oh' ⊔ ℓh ⊔ ℓh') where
    no-eta-equality
    field 
      pre-cartesian : 1-cell-pre-cartesian f f'

    open 1-cell-pre-cartesian pre-cartesian public
    field
      commutes² : ∀ {U U'} {m₁ m₂ : U ↦ A} {h₁' : U' [ f ⊗ m₁ ]↦ B'} {h₂' : U' [ f ⊗ m₂ ]↦ B'}
                → (δ : m₁ ⇒ m₂) (σ : h₁' [ f ▶ δ ]⇒ h₂')
                → (f' ▶' universal² δ σ) Hom[].≡[ sym (Hom.idl _ ∙ Hom.idr _) ] (comm¹.from' ∘' σ ∘' comm¹.to')
                -- If the E is locally displayed-univalent then we can upgrade to this
                -- → PathP (λ i → commutes¹ m₁ h₁' i [ f ▶ δ ]⇒ commutes¹ m₂ h₂' i) (f' ▶' universal² δ σ) σ

      unique² : ∀ {U U'} {m₁ m₂ : U ↦ A} {h₁' : U' [ f ⊗ m₁ ]↦ B'} {h₂' : U' [ f ⊗ m₂ ]↦ B'}
                → {δ : m₁ ⇒ m₂} (σ : h₁' [ f ▶ δ ]⇒ h₂')
                → (δ' : universal¹ m₁ h₁' [ δ ]⇒ universal¹ m₂ h₂')
                → (f' ▶' δ') Hom[].≡[ sym (Hom.idl _ ∙ Hom.idr _) ] (comm¹.from' ∘' σ ∘' comm¹.to')
                → δ' ≡ universal² δ σ
      
  record 1-cell-pre-cartesian-lift {A B} (f : A ↦ B) (B' : Ob[ B ]) : Type (o ⊔ o' ⊔ oh ⊔ oh' ⊔ ℓh ⊔ ℓh') where
    field
      {A'} : Ob[ A ]
      lifting : A' [ f ]↦ B'
      pre-cartesian : 1-cell-pre-cartesian f lifting

    open 1-cell-pre-cartesian pre-cartesian public

  record 1-cell-cartesian-lift {A B} (f : A ↦ B) (B' : Ob[ B ]) : Type (o ⊔ o' ⊔ oh ⊔ oh' ⊔ ℓh ⊔ ℓh') where
    field
      {A'} : Ob[ A ]
      lifting : A' [ f ]↦ B'
      cartesian : 1-cell-cartesian f lifting

    open 1-cell-cartesian cartesian public

  record Cartesian-bifibration : Type (o ⊔ o' ⊔ oh ⊔ oh' ⊔ ℓh ⊔ ℓh') where
    field
      1-cart : ∀ {A B} (f : A ↦ B) (B' : Ob[ B ]) → 1-cell-cartesian-lift f B'
      2-cart : Locally-cartesian
      is-fibred-compose' : ∀ {A B C A' B' C'} → is-fibred-functor (compose' {A} {B} {C} {A'} {B'} {C'})
    
    module _ {A B} (f : A ↦ B) (B' : Ob[ B ]) where
      open 1-cell-cartesian-lift (1-cart f B') 
        using () 
        renaming (A' to _^*1_ ; lifting to π*1)
        public
    
    module π*1 {A B} {f : A ↦ B} {B' : Ob[ B ]} where
       open 1-cell-cartesian-lift (1-cart f B') 
        hiding (A' ; lifting)
        public
      
    module _ {A B} {A' : Ob[ A ]} {B' : Ob[ B ]} where
      open Cartesian-fibration Hom[ A' , B' ] 2-cart 
        renaming (_^*_ to _^*2_ ; π* to π*2 ; module π* to π*2)
        public
```
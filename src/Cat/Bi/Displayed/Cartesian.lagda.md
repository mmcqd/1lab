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

  open Prebicategory-Hom-Reasoning B
  open Bidisplayed-Hom[]-Reasoning E

  module _ {A B A' B'} (f : A ↦ B) (f' : A' [ f ]↦ B') where

    _is-factor-of_ : ∀ {U U'} {h : U ↦ A} (h' : U' [ h ]↦ A') (g' : U' [ f ⊗ h ]↦ B') → Type _
    _is-factor-of_ h' g' = (f' ⊗' h') Hom[].≅↓ g'
    
    record 1-cell-cartesian : Type (o ⊔ o' ⊔ oh ⊔ oh' ⊔ ℓh ⊔ ℓh') where
      no-eta-equality
      field
        universal¹ : ∀ {U U'} (h : U ↦ A) (g' : U' [ f ⊗ h ]↦ B') → U' [ h ]↦ A'
        commutes¹ : ∀ {U U'} (h : U ↦ A) (g' : U' [ f ⊗ h ]↦ B') → universal¹ h g' is-factor-of g'
       
        universal² 
          : ∀ {U U'} {h₁ h₂ : U ↦ A} 
          → {δ : h₁ ⇒ h₂}
          → {h₁' : U' [ h₁ ]↦ A'} {h₂' : U' [ h₂ ]↦ A'}
          → {g₁' : U' [ f ⊗ h₁ ]↦ B'} {g₂' : U' [ f ⊗ h₂ ]↦ B'}
          → (i₁ : h₁' is-factor-of g₁')
          → (i₂ : h₂' is-factor-of g₂')
          → (σ' : g₁' [ f ▶ δ ]⇒ g₂')
          → h₁' [ δ ]⇒ h₂' 
        
        commutes² 
          : ∀ {U U'} {h₁ h₂ : U ↦ A} 
          → {δ : h₁ ⇒ h₂}
          → {h₁' : U' [ h₁ ]↦ A'} {h₂' : U' [ h₂ ]↦ A'}
          → {g₁' : U' [ f ⊗ h₁ ]↦ B'} {g₂' : U' [ f ⊗ h₂ ]↦ B'}
          → (i₁ : h₁' is-factor-of g₁')
          → (i₂ : h₂' is-factor-of g₂')
          → (σ' : g₁' [ f ▶ δ ]⇒ g₂')
          → (f' ▶' universal² i₁ i₂ σ') Hom[].≡[ sym $ Hom.idl _ ∙ Hom.idr _ ] (i₂ .Hom[].from' ∘' σ' ∘' i₁ .Hom[].to')
        
        unique²
          : ∀ {U U'} {h₁ h₂ : U ↦ A} 
          → {δ : h₁ ⇒ h₂}
          → {h₁' : U' [ h₁ ]↦ A'} {h₂' : U' [ h₂ ]↦ A'}
          → {g₁' : U' [ f ⊗ h₁ ]↦ B'} {g₂' : U' [ f ⊗ h₂ ]↦ B'}
          → {i₁ : h₁' is-factor-of g₁'}
          → {i₂ : h₂' is-factor-of g₂'}
          → {σ' : g₁' [ f ▶ δ ]⇒ g₂'}
          → (other : h₁' [ δ ]⇒ h₂')
          → (f' ▶' other) Hom[].≡[ sym $ Hom.idl _ ∙ Hom.idr _ ] (i₂ .Hom[].from' ∘' σ' ∘' i₁ .Hom[].to')
          → other ≡ universal² i₁ i₂ σ'

      module comm¹ {U U'} {m : U ↦ A} {h' : U' [ f ⊗ m ]↦ B'} = Hom[]._≅[_]_ (commutes¹ m h')
   
  record 1-cell-cartesian-lift {A B} (f : A ↦ B) (B' : Ob[ B ]) : Type (o ⊔ o' ⊔ oh ⊔ oh' ⊔ ℓh ⊔ ℓh') where
    no-eta-equality
    field
      {A'} : Ob[ A ]
      lifting : A' [ f ]↦ B'
      cartesian : 1-cell-cartesian f lifting

    open 1-cell-cartesian cartesian public

  record Cartesian-bifibration : Type (o ⊔ o' ⊔ oh ⊔ oh' ⊔ ℓh ⊔ ℓh') where
    no-eta-equality
    field
      1-cart : ∀ {A B} (f : A ↦ B) (B' : Ob[ B ]) → 1-cell-cartesian-lift f B'
      2-cart : ∀ {A B} {A' : Ob[ A ]} {B' : Ob[ B ]} → Cartesian-fibration (Hom[ A' , B' ])
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


_is-[_]-factor-of_ : ⊤ → ⊤ → ⊤
_is-[_]-factor-of_ = λ _ _ → tt


{-# DISPLAY _is-factor-of_ {_} {_} {_} {_} {_} {_} {_} E _ _ h' g' = h' is-[ E ]-factor-of g' #-}

```
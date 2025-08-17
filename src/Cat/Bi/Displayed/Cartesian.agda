
open import Cat.Prelude
open import Cat.Displayed.Base
open import Cat.Displayed.Cartesian
open import Cat.Bi.Base
open import Cat.Bi.Displayed.Base
open import Cat.Displayed.Instances.DisplayedFunctor hiding (_◆'_)
open import Cat.Morphism hiding (Hom)
import Cat.Displayed.Reasoning as DR
import Cat.Displayed.Morphism as DM

module Cat.Bi.Displayed.Cartesian where

-- Definition and proofs taken from https://arxiv.org/pdf/1212.6283

module _ {o oh ℓh o' oh' ℓh'} {B : Prebicategory o oh ℓh} (E : Bidisplayed B o' oh' ℓh') where

  open Prebicategory B 
  open Bidisplayed E hiding (module Hom[])

  module postaction {a b c} (f : a ↦ b) = Functor (postaction B {a} {b} {c} f)

  module Hom[] {A B} {A' : Ob[ A ]} {B' : Ob[ B ]} where
    open DR (Hom[ A' , B' ]) public
    open DM (Hom[ A' , B' ]) public
    open Displayed Hom[ A' , B' ] public


  module _ 
    {A B C} {f g : A ↦ B} {α : f ⇒ g} {h : B ↦ C} 
    (inv : is-invertible (Hom _ _) α)
    where
    module inv = is-invertible inv
    ▶-inv : is-invertible (Hom _ _) (h ▶ α)
    ▶-inv .is-invertible.inv = h ▶ inv.inv
    ▶-inv .is-invertible.inverses .Inverses.invl = 
      sym (compose.F-∘ _ _) ∙∙ ap₂ _◆_ (Hom.idl _) inv.invl ∙∙ compose.F-id
    ▶-inv .is-invertible.inverses .Inverses.invr = 
      sym (compose.F-∘ _ _) ∙∙ ap₂ _◆_ (Hom.idl _) inv.invr ∙∙ compose.F-id

  open is-cartesian

  Locally-cartesian : Type _
  Locally-cartesian = ∀ {A B} {A' : Ob[ A ]} {B' : Ob[ B ]} → Cartesian-fibration (Hom[ A' , B' ])

  2-cell-cartesian : ∀ {A B A' B'} {f₁ f₂ : A ↦ B} {f₁' : A' [ f₁ ]↦ B'} {f₂' : A' [ f₂ ]↦ B'}
                   → (f : f₁ ⇒ f₂) (f' : f₁' [ f ]⇒ f₂') → Type _
  2-cell-cartesian {A' = A'} {B'} f f' = is-cartesian Hom[ A' , B' ] f f'

  record 1-cell-cartesian {A B A' B'} (f : A ↦ B) (f' : A' [ f ]↦ B') : Type (o ⊔ o' ⊔ oh ⊔ oh' ⊔ ℓh ⊔ ℓh') where
    field
      universal₁ : ∀ {U U'} (m : U ↦ A) (h' : U' [ f ⊗ m ]↦ B') → U' [ m ]↦ A'
      commutes₁ : ∀ {U U'} (m : U ↦ A) (h' : U' [ f ⊗ m ]↦ B') 
                  → (f' ⊗' universal₁ m h') Hom[].≅↓ h'

    module comm₁ {U U'} {m : U ↦ A} {h' : U' [ f ⊗ m ]↦ B'} = Hom[]._≅[_]_ (commutes₁ m h')

    field
      universal₂ : ∀ {U U'} {m₁ m₂ : U ↦ A} {h₁' : U' [ f ⊗ m₁ ]↦ B'} {h₂' : U' [ f ⊗ m₂ ]↦ B'}
                 → (δ : m₁ ⇒ m₂) (σ : h₁' [ f ▶ δ ]⇒ h₂')
                 → universal₁ m₁ h₁' [ δ ]⇒ universal₁ m₂ h₂' 
      
      commutes₂ : ∀ {U U'} {m₁ m₂ : U ↦ A} {h₁' : U' [ f ⊗ m₁ ]↦ B'} {h₂' : U' [ f ⊗ m₂ ]↦ B'}
                → (δ : m₁ ⇒ m₂) (σ : h₁' [ f ▶ δ ]⇒ h₂')
                → (f' ▶' universal₂ δ σ) Hom[].≡[ sym (Hom.idl _ ∙ Hom.idr _) ] (comm₁.from' ∘' σ ∘' comm₁.to')

      unique₂ : ∀ {U U'} {m₁ m₂ : U ↦ A} {h₁' : U' [ f ⊗ m₁ ]↦ B'} {h₂' : U' [ f ⊗ m₂ ]↦ B'}
                → (δ : m₁ ⇒ m₂) (σ : h₁' [ f ▶ δ ]⇒ h₂')
                → (δ' : universal₁ m₁ h₁' [ δ ]⇒ universal₁ m₂ h₂')
                → (f' ▶' δ') Hom[].≡[ sym (Hom.idl _ ∙ Hom.idr _) ] (comm₁.from' ∘' σ ∘' comm₁.to')
                → δ' ≡ universal₂ δ σ

    -- module _
    --   {U U'} {m₁ m₂ : U ↦ A} {h₁' : U' [ f ⊗ m₁ ]↦ B'} {h₂' : U' [ f ⊗ m₂ ]↦ B'}
    --   {δ : m₁ ⇒ m₂} {σ : h₁' [ f ▶ δ ]⇒ h₂'}
    --   (δ-inv : is-invertible (Hom U A) δ)
    --   (σ-inv : Hom[].is-invertible[ ▶-inv δ-inv ] σ)
    --   where
    --   private
    --     module δ-inv = is-invertible δ-inv
    --     module σ-inv = Hom[].is-invertible[_] σ-inv

    --   inv-lift : Hom[].is-invertible[ δ-inv ] (universal₂ δ σ)
    --   inv-lift .DM.is-invertible[_].inv' = 
    --     universal₂ δ-inv.inv σ-inv.inv'
    --   inv-lift .DM.is-invertible[_].inverses' .DM.Inverses[_].invl' = {!   !}
    --     where
    --       δ' : m₂ ⇒ m₂
    --       δ' = δ Hom.∘ δ-inv.inv
    --       σ' : h₂' [ f ▶ δ' ]⇒ h₂'
    --       σ' = Hom[].hom[ postaction.F-∘ _ _ _ ]⁻ (σ ∘' σ-inv.inv')

    --       lemma : universal₂ δ σ Hom[].∘' universal₂ δ-inv.inv σ-inv.inv' ≡ universal₂ δ' σ'
    --       lemma = unique₂ _ _ _ $ Hom[].cast[] $ 
    --         f' ▶' universal₂ δ σ Hom[].∘' universal₂ δ-inv.inv σ-inv.inv' Hom[].≡[]⟨ {!   !} ⟩ 
    --         {!   !}

    --   inv-lift .DM.is-invertible[_].inverses' .DM.Inverses[_].invr' = {!   !}


  record Bicartesian-lift {A B} (f : A ↦ B) (B' : Ob[ B ]) : Type (o ⊔ o' ⊔ oh ⊔ oh' ⊔ ℓh ⊔ ℓh') where
    field
      {A'} : Ob[ A ]
      lifting : A' [ f ]↦ B'
      cartesian : 1-cell-cartesian f lifting

    open 1-cell-cartesian cartesian

  record Bicartesian-fibration : Type (o ⊔ o' ⊔ oh ⊔ oh' ⊔ ℓh ⊔ ℓh') where
    field
      1-cart : ∀ {A B} (f : A ↦ B) (B' : Ob[ B ]) → Bicartesian-lift f B'
      2-cart : Locally-cartesian
      ◆'-cart : ∀ {A B C A' B' C'} {f₁ f₂ : B ↦ C} {f₁' : B' [ f₁ ]↦ C'} {f₂' : B' [ f₂ ]↦ C'}
              → {f : f₁ ⇒ f₂} {f' : f₁' [ f ]⇒ f₂'}
              → {g₁ g₂ : A ↦ B} {g₁' : A' [ g₁ ]↦ B'} {g₂' : A' [ g₂ ]↦ B'}
              → {g : g₁ ⇒ g₂} {g' : g₁' [ g ]⇒ g₂'} 
              → is-cartesian Hom[ _ , _ ] f f'
              → is-cartesian Hom[ _ , _ ] g g'
              → is-cartesian Hom[ _ , _ ] (f ◆ g) (f' ◆' g')
    
    module _ {A B} (f : A ↦ B) (B' : Ob[ B ]) where
      open Bicartesian-lift (1-cart f B') 
        using () 
        renaming (A' to _^*1_ ; lifting to π*1)
        public
    
    module π*1 {A B} {f : A ↦ B} {B' : Ob[ B ]} where
       open Bicartesian-lift (1-cart f B') 
        hiding (A' ; lifting)
        public
      
    module _ {A B} {A' : Ob[ A ]} {B' : Ob[ B ]} where
      open Cartesian-fibration Hom[ A' , B' ] 2-cart 
        renaming (_^*_ to _^*2_ ; π* to π*2 ; module π* to π*2)
        public
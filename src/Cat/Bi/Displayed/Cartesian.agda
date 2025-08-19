open import Cat.Prelude
open import Cat.Displayed.Base
open import Cat.Displayed.Cartesian
open import Cat.Bi.Base
open import Cat.Bi.Displayed.Base
open import Cat.Displayed.Instances.DisplayedFunctor hiding (_◆'_)
open import Cat.Morphism hiding (Ob ; Hom)
open import Cat.Instances.Product

import Cat.Displayed.Reasoning as DR
import Cat.Displayed.Morphism as DM
import Cat.Bi.Morphism as BM
import Cat.Bi.Displayed.Morphism as DBM


module Cat.Bi.Displayed.Cartesian where

-- Definition and proofs taken from https://arxiv.org/pdf/1212.6283

module _ {o oh ℓh o' oh' ℓh'} {B : Prebicategory o oh ℓh} (E : Bidisplayed B o' oh' ℓh') where

  private module B = Prebicategory B
  open Prebicategory B 
  open Bidisplayed-Hom[]-Reasoning E
  open BM B
  open DBM E
  

  open is-cartesian

  Locally-cartesian : Type _
  Locally-cartesian = ∀ {A B} {A' : Ob[ A ]} {B' : Ob[ B ]} → Cartesian-fibration (Hom[ A' , B' ])


  record 1-cell-cartesian {A B A' B'} (f : A ↦ B) (f' : A' [ f ]↦ B') : Type (o ⊔ o' ⊔ oh ⊔ oh' ⊔ ℓh ⊔ ℓh') where
    no-eta-equality
    field 
      universal¹ : ∀ {U U'} (m : U ↦ A) (h' : U' [ f ⊗ m ]↦ B') → U' [ m ]↦ A'
      commutes¹ : ∀ {U U'} (m : U ↦ A) (h' : U' [ f ⊗ m ]↦ B') 
                  → (f' ⊗' universal¹ m h') Hom[].≅↓ h'

    module comm¹ {U U'} {m : U ↦ A} {h' : U' [ f ⊗ m ]↦ B'} = Hom[]._≅[_]_ (commutes¹ m h')
    

    field
      universal² : ∀ {U U'} {m₁ m₂ : U ↦ A} 
                 → (δ : m₁ ⇒ m₂) 
                 → {h₁' : U' [ f ⊗ m₁ ]↦ B'} {h₂' : U' [ f ⊗ m₂ ]↦ B'}
                → (σ : h₁' [ f ▶ δ ]⇒ h₂')
                 → universal¹ m₁ h₁' [ δ ]⇒ universal¹ m₂ h₂' 
      
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
      
    universal¹' : ∀ {U U'} {m : U ↦ A} {k : U ↦ B} (p : (f ⊗ m) ≡ k) (h' : U' [ k ]↦ B') → U' [ m ]↦ A'
    universal¹'  {U' = U'} p h' = universal¹ _ (coe1→0 (λ i → U' [ p i ]↦ B') h')

    universal²' : ∀ {U U'} {m₁ m₂ : U ↦ A} 
                → {h₁' : U' [ f ⊗ m₁ ]↦ B'} {h₂' : U' [ f ⊗ m₂ ]↦ B'}
                → {δ : m₁ ⇒ m₂} {k : (f ⊗ m₁) ⇒ (f ⊗ m₂)}
                → (p : f ▶ δ ≡ k) (σ : h₁' [ k ]⇒ h₂')
                → universal¹ m₁ h₁' [ δ ]⇒ universal¹ m₂ h₂' 
    universal²' {h₁' = h₁'} {h₂'} p σ = universal² _ (Hom[].hom[ p ]⁻ σ)

    abstract
      commutesp² : ∀ {U U'} {m₁ m₂ : U ↦ A} {h₁' : U' [ f ⊗ m₁ ]↦ B'} {h₂' : U' [ f ⊗ m₂ ]↦ B'}
                  → {δ : m₁ ⇒ m₂} {k : (f ⊗ m₁) ⇒ (f ⊗ m₂)} 
                  → (p : f ▶ δ ≡ k) (σ : h₁' [ k ]⇒ h₂')
                  → (f' ▶' universal²' p σ) Hom[].≡[ sym (Hom.idl _ ∙ Hom.idr _ ∙ sym p) ] (comm¹.from' ∘' σ ∘' comm¹.to')
      commutesp² {m₁ = m₁} {m₂ = m₂} {h₁' = h₁'} {h₂' = h₂'} p σ = Hom[].cast[] $
        f' ▶' universal²' p σ                                             Hom[].≡[]⟨ commutes² _ _ ⟩
        (comm¹.from' ∘' Hom[].hom[ p ]⁻ σ ∘' comm¹.to') Hom[].≡[]˘⟨ apd (λ _ e → comm¹.from' ∘' e ∘' comm¹.to') (transport-filler _ _) ⟩
        (comm¹.from' ∘' σ ∘' comm¹.to')                                   ∎ 
        
      universalp² : ∀ {U U'} {m₁ m₂ : U ↦ A} 
                  → {h₁' : U' [ f ⊗ m₁ ]↦ B'} {h₂' : U' [ f ⊗ m₂ ]↦ B'}
                  → {δ₁ δ₂ : m₁ ⇒ m₂} {k : (f ⊗ m₁) ⇒ (f ⊗ m₂)}
                  → (p : f ▶ δ₁ ≡ k) (q : δ₁ ≡ δ₂) (r : f ▶ δ₂ ≡ k) (σ : h₁' [ k ]⇒ h₂')
                  → universal²' p σ Hom[].≡[ q ] universal²' r σ
      universalp² p q r σ i = 
        universal²' (is-set→squarep (λ _ _ → hlevel 2) (ap (f ▶_) q) p r refl i) σ

      uniquep² : ∀ {U U'} {m₁ m₂ : U ↦ A} 
                → {h₁' : U' [ f ⊗ m₁ ]↦ B'} {h₂' : U' [ f ⊗ m₂ ]↦ B'}
                → {δ₁ δ₂ : m₁ ⇒ m₂} {k : (f ⊗ m₁) ⇒ (f ⊗ m₂)}
                → (p : f ▶ δ₁ ≡ k) (q : δ₁ ≡ δ₂) (r : f ▶ δ₂ ≡ k)
                → {σ : h₁' [ k ]⇒ h₂'}
                → (δ' : universal¹ m₁ h₁' [ δ₁ ]⇒ universal¹ m₂ h₂')
                → (f' ▶' δ') Hom[].≡[ sym (Hom.idl _ ∙ Hom.idr _ ∙ sym p) ] (comm¹.from' ∘' σ ∘' comm¹.to')
                → δ' Hom[].≡[ q ] universal²' r σ
      uniquep² {δ₁ = δ₁} p q r {σ = σ} δ' x = Hom[].cast[] $
        δ'                                Hom[].≡[]⟨ unique² (Hom[].hom[ p ]⁻ σ) δ' (Hom[].cast[] $
            f' ▶' δ'                                      Hom[].≡[]⟨ x ⟩
            comm¹.from' ∘' σ ∘' comm¹.to'                 Hom[].≡[]⟨ apd (λ _ e → comm¹.from' ∘' e ∘' comm¹.to') (transport-filler _ _) ⟩
            comm¹.from' ∘' Hom[].hom[ p ]⁻ σ ∘' comm¹.to' ∎
          )⟩
        universal² δ₁ (Hom[].hom[ p ]⁻ σ) Hom[].≡[]⟨ universalp² p q r σ ⟩
        universal²' r σ                   ∎

      uniquep²₂ : ∀ {U U'} {m₁ m₂ : U ↦ A} 
                → {h₁' : U' [ f ⊗ m₁ ]↦ B'} {h₂' : U' [ f ⊗ m₂ ]↦ B'}
                → {δ₁ δ₂ : m₁ ⇒ m₂} {k : (f ⊗ m₁) ⇒ (f ⊗ m₂)} {σ : h₁' [ k ]⇒ h₂'}
                → (p : f ▶ δ₁ ≡ k) (q : δ₁ ≡ δ₂) (r : f ▶ δ₂ ≡ k)
                → (δ₁' : universal¹ m₁ h₁' [ δ₁ ]⇒ universal¹ m₂ h₂')
                → (δ₂' : universal¹ m₁ h₁' [ δ₂ ]⇒ universal¹ m₂ h₂')
                → (f' ▶' δ₁') Hom[].≡[ sym (Hom.idl _ ∙ Hom.idr _ ∙ sym p) ] (comm¹.from' ∘' σ ∘' comm¹.to')
                → (f' ▶' δ₂') Hom[].≡[ sym (Hom.idl _ ∙ Hom.idr _ ∙ sym r) ] (comm¹.from' ∘' σ ∘' comm¹.to')
                → δ₁' Hom[].≡[ q ] δ₂'
      uniquep²₂ p q r δ₁' δ₂' α β = Hom[].cast[] (uniquep² p q r δ₁' α Hom[].∙[] universalp² r (sym q) p _ Hom[].∙[] symP (uniquep² r (sym q) p δ₂' β ))


  record Bicartesian-lift {A B} (f : A ↦ B) (B' : Ob[ B ]) : Type (o ⊔ o' ⊔ oh ⊔ oh' ⊔ ℓh ⊔ ℓh') where
    field
      {A'} : Ob[ A ]
      lifting : A' [ f ]↦ B'
      cartesian : 1-cell-cartesian f lifting

    open 1-cell-cartesian cartesian public

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

  -- Bicartesian-domain-unique
  --   : ∀ {A B A₁' A₂' B'} {f : A ↦ B} {f₁' : A₁' [ f ]↦ B'} {f₂' : A₂' [ f ]↦ B'}
  --   → 1-cell-cartesian f f₁'
  --   → 1-cell-cartesian f f₂'
  --   → A₁' ≅ᵇ↓ A₂'  
  -- Bicartesian-domain-unique {f = f} {f₁'} {f₂'} c1 c2 = 
  --   make-isoᵇ[ id-isoᵇ ] to* from* {!   !} {!   !} where
         
  --   module c1 = 1-cell-cartesian c1
  --   module c2 = 1-cell-cartesian c2

  --   to* = c2.universal¹ B.id (f₁' ⊗' ↦id')
  --   from* = c1.universal¹ B.id (f₂' ⊗' ↦id')


  --   invl*to : ↦id' [ λ→ _ ]⇒ (to* ⊗' from*)
  --   invl*to = {!  c1.commutes¹ ? ? .Hom[].from' !}
    
  --   invl* : ↦id' Hom[].≅[ λ≅ _ ] (to* ⊗' from*)
  --   invl* = Hom[].make-iso[ _ ] invl*to {!   !} {!   !} {!   !}


  -- cartesian→weak-monic
  --   : ∀ {x y} {f : Hom x y}
  --   → ∀ {x' y'} {f' : Hom[ f ] x' y'}
  --   → is-cartesian f f'
  --   → is-weak-monic f'
  -- cartesian→weak-monic {f = f} {f' = f'} f-cart g' g'' p p' =
  --   uniquep₂ (ap (f ∘_) p) p refl g' g'' p' refl
  --   where
  --     open is-cartesian f-cart

 
  -- cartesian-domain-unique
  -- : ∀ {x y} {f : Hom x y}
  -- → ∀ {x' x'' y'} {f' : Hom[ f ] x' y'} {f'' : Hom[ f ] x'' y'}
  -- → is-cartesian f f'
  -- → is-cartesian f f''
  -- → x' ≅↓ x''
  -- cartesian-domain-unique {f' = f'} {f'' = f''} f'-cart f''-cart =
  --   make-iso[ id-iso ] to* from* invl* invr* where
  --     module f' = is-cartesian f'-cart
  --     module f'' = is-cartesian f''-cart

  --     to* = f''.universalv f'
  --     from* = f'.universalv f''

  --     invl* : to* ∘' from* ≡[ idl id ] id'
  --     invl* =
  --       cartesian→weak-monic f''-cart (to* ∘' from*) id' (idl id) $
  --       cast[] $
  --         f'' ∘' to* ∘' from* ≡[]⟨ pulll[] _ (f''.commutesv f') ⟩
  --         f' ∘' from*         ≡[]⟨ f'.commutesv f'' ⟩
  --         f''                 ≡[]˘⟨ idr' f'' ⟩
  --         f'' ∘' id'          ∎

  --     invr* : from* ∘' to* ≡[ idl id ] id'
  --     invr* =
  --       cartesian→weak-monic f'-cart (from* ∘' to*) id' (idl id) $
  --       cast[] $
  --         f' ∘' from* ∘' to* ≡[]⟨ pulll[] _ (f'.commutesv f'') ⟩
  --         f'' ∘' to*         ≡[]⟨ f''.commutesv f' ⟩
  --         f'                 ≡[]˘⟨ idr' f' ⟩
  --         f' ∘' id'          ∎
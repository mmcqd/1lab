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


module Cat.Bi.Displayed.CartesianAlt where

-- Definition and proofs taken from https://arxiv.org/pdf/1212.6283

module _ {o oh ℓh o' oh' ℓh'} {B : Prebicategory o oh ℓh} (E : Bidisplayed B o' oh' ℓh') where

  open Prebicategory-Hom-Reasoning B
  open Bidisplayed E hiding (module Hom[])

  private module Hom[] {A B} {A' : Ob[ A ]} {B' : Ob[ B ]} where
    open DM Hom[ A' , B' ] public
    open DR Hom[ A' , B' ] public
  
  ◆'-invertible[] 
    : ∀ {a b c a' b' c'} 
    → {f g : b ↦ c} {h k : a ↦ b} 
    → {α : f ⇒ g} {β : h ⇒ k} 
    → {α-inv : Hom.is-invertible α} {β-inv : Hom.is-invertible β}
    → {f' : b' [ f ]↦ c'} {g' : b' [ g ]↦ c'}
    → {h' : a' [ h ]↦ b'} {k' : a' [ k ]↦ b'}
    → {α' : f' [ α ]⇒ g'} {β' : h' [ β ]⇒ k'}
    → Hom[].is-invertible[ α-inv ] α'
    → Hom[].is-invertible[ β-inv ] β'
    → Hom[].is-invertible[ (◆-invertible B α-inv β-inv) ] (α' ◆' β')
  ◆'-invertible[] α-inv' β-inv' = 
    Hom[].make-invertible[ _ ] 
      (α'.inv' ◆' β'.inv')
      (symP compose'.F-∘' Hom[].∙∙[] (λ i → (α'.invl' i) ◆' β'.invl' i) ∙∙[] compose'.F-id')
      (symP compose'.F-∘' Hom[].∙∙[] (λ i → (α'.invr' i) ◆' β'.invr' i) ∙∙[] compose'.F-id')
    where
      module α' = Hom[].is-invertible[_] α-inv'
      module β' = Hom[].is-invertible[_] β-inv'
  
  ◆'-iso[]
    : ∀ {a b c a' b' c'}
    → {f g : b ↦ c} {h k : a ↦ b}
    → {f' : b' [ f ]↦ c'} {g' : b' [ g ]↦ c'}
    → {h' : a' [ h ]↦ b'} {k' : a' [ k ]↦ b'}
    → {i : f Hom.≅ g} {j : h Hom.≅ k}
    → f' Hom[].≅[ i ] g' 
    → h' Hom[].≅[ j ] k'
    → (f' ⊗' h') Hom[].≅[ ◆-iso B i j ] (g' ⊗' k') 
  ◆'-iso[] i' j' = Hom[].invertible[]→iso[] (◆'-invertible[] (Hom[].iso[]→invertible[] i') (Hom[].iso[]→invertible[] j'))


  open is-cartesian

  Locally-cartesian : Type _
  Locally-cartesian = ∀ {A B} {A' : Ob[ A ]} {B' : Ob[ B ]} → Cartesian-fibration (Hom[ A' , B' ])

 
                  
  record 1-cell-cartesian {A B A' B'} (f : A ↦ B) (f' : A' [ f ]↦ B') : Type (o ⊔ o' ⊔ oh ⊔ oh' ⊔ ℓh ⊔ ℓh') where
    no-eta-equality
    field
      universal¹ 
        : ∀ {U U'} (m : U ↦ A) (h' : U' [ f ⊗ m ]↦ B') 
        → U' [ m ]↦ A'
      commutes¹ 
        : ∀ {U U'} (m : U ↦ A) (h' : U' [ f ⊗ m ]↦ B') 
        → (f' ⊗' universal¹ m h') Hom[].≅↓ h'
      
      unique¹ 
        : ∀ {U U'} {m : U ↦ A} {h' : U' [ f ⊗ m ]↦ B'}
        → {other : U' [ m ]↦ A'}
        → (f' ⊗' other) Hom[].≅↓ h'
        → other Hom[].≅↓ universal¹ m h'

    module comm¹ {U U'} {m : U ↦ A} {h' : U' [ f ⊗ m ]↦ B'} = Hom[]._≅[_]_ (commutes¹ m h')
    module unique¹ {U U'} {m : U ↦ A} {h' : U' [ f ⊗ m ]↦ B'} {other : U' [ m ]↦ A'} (i : (f' ⊗' other) Hom[].≅↓ h') = Hom[]._≅[_]_ (unique¹ i)

    field
      unique-comm¹ 
        : ∀ {U U'} {m : U ↦ A} {h' : U' [ f ⊗ m ]↦ B'}
        → {other : U' [ m ]↦ A'}
        → (i : (f' ⊗' other) Hom[].≅↓ h')
        → (let module i = Hom[]._≅[_]_ i)
        → (comm¹.to' ∘' ((f' ▶' unique¹.to' i))) Hom[].≡[ (Hom.idl _) ∙ compose.F-id ] i.to'
 
    unique-comm¹-op 
      : ∀ {U U'} {m : U ↦ A} {h' : U' [ f ⊗ m ]↦ B'}
      → {other : U' [ m ]↦ A'}
      → (i : (f' ⊗' other) Hom[].≅↓ h')
      → (let module i = Hom[]._≅[_]_ i)
      → ((f' ▶' unique¹.from' i) ∘' comm¹.from') Hom[].≡[ (Hom.idr _) ∙ compose.F-id ] i.from'
    unique-comm¹-op i = 
      Hom[].cast[] $ 
      Hom[].inv-path[] 
        (Hom[].iso[]→invertible[] 
          ((commutes¹ _ _ Hom[].∘Iso[] ◆'-iso[] Hom[].id-iso↓ (unique¹ _)) 
            Hom[].Iso[]⁻¹)) 
        (Hom[].iso[]→invertible[] (i Hom[].Iso[]⁻¹)) $
      unique-comm¹ i

    field    
      universal² 
        : ∀ {U U'} {m₁ m₂ : U ↦ A} 
        → (δ : m₁ ⇒ m₂) 
        → {h₁' : U' [ f ⊗ m₁ ]↦ B'} {h₂' : U' [ f ⊗ m₂ ]↦ B'}
        → (σ : h₁' [ f ▶ δ ]⇒ h₂')
        → universal¹ m₁ h₁' [ δ ]⇒ universal¹ m₂ h₂' 
      

    field
      commutes² 
        : ∀ {U U'} {m₁ m₂ : U ↦ A} {h₁' : U' [ f ⊗ m₁ ]↦ B'} {h₂' : U' [ f ⊗ m₂ ]↦ B'}
        → (δ : m₁ ⇒ m₂) (σ : h₁' [ f ▶ δ ]⇒ h₂')
        → (f' ▶' universal² δ σ) Hom[].≡[ sym (Hom.idl _ ∙ Hom.idr _) ] (comm¹.from' ∘' σ ∘' comm¹.to')

      unique² 
        : ∀ {U U'} {m₁ m₂ : U ↦ A} {h₁' : U' [ f ⊗ m₁ ]↦ B'} {h₂' : U' [ f ⊗ m₂ ]↦ B'}
        → {δ : m₁ ⇒ m₂} (σ : h₁' [ f ▶ δ ]⇒ h₂')
        → (δ' : universal¹ m₁ h₁' [ δ ]⇒ universal¹ m₂ h₂')
        → (f' ▶' δ') Hom[].≡[ sym (Hom.idl _ ∙ Hom.idr _) ] (comm¹.from' ∘' σ ∘' comm¹.to')
        → δ' ≡ universal² δ σ

 
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


  module UniMath {a b aa bb} (f : a ↦ b) (ff : aa [ f ]↦ bb) where
    
    lift-1cell-factor 
      : ∀ {c cc} {h : c ↦ a} (gg : cc [ f ⊗ h ]↦ bb) → Type _
    lift-1cell-factor {cc = cc} {h = h} gg = 
      Σ[ hh ∈ (cc [ h ]↦ aa) ] ((ff ⊗' hh) Hom[].≅↓ gg)

    lift-2cell-factor-type 
      : ∀ {c cc} {h h' : c ↦ a} 
        → {gg : cc [ f ⊗ h ]↦ bb} {gg' : cc [ f ⊗ h' ]↦ bb}
        → {δ : h ⇒ h'}
        → (σσ : gg [ f ▶ δ ]⇒ gg')
        → lift-1cell-factor gg
        → lift-1cell-factor gg'
        → Type _ 
    lift-2cell-factor-type {δ = δ} σσ (Lh , comm)  (Lh' , comm') = 
      Σ[ δδ ∈ Lh [ δ ]⇒ Lh' ] ((ff ▶' δδ) Hom[].≡[ sym (Hom.idl _ ∙ Hom.idr _) ]  (comm' .Hom[].from' ∘' σσ ∘' comm .Hom[].to'))

    lift-2cell-factor
      : ∀ {c cc} {h h' : c ↦ a} 
        → {gg : cc [ f ⊗ h ]↦ bb} {gg' : cc [ f ⊗ h' ]↦ bb}
        → {δ : h ⇒ h'}
        → (σσ : gg [ f ▶ δ ]⇒ gg')
        → lift-1cell-factor gg
        → lift-1cell-factor gg'
        → Type _ 
    lift-2cell-factor σσ Lh Lh' = is-contr (lift-2cell-factor-type σσ Lh Lh')
    
    cartesian-1cell : Type _
    cartesian-1cell = 
        (
          (c : Ob) 
          (cc : Ob[ c ]) 
          (h : c ↦ a) 
          (gg : cc [ f ⊗ h ]↦ bb) 
          → lift-1cell-factor gg
        ) 
        × 
        (
          (c : Ob)
          (cc : Ob[ c ])
          (h h' : c ↦ a)
          (gg : cc [ f ⊗ h ]↦ bb)
          (gg' : cc [ f ⊗ h' ]↦ bb)
          (δ : h ⇒ h')
          (σσ : gg [ f ▶ δ ]⇒ gg')
          (Lh : lift-1cell-factor gg)
          (Lh' : lift-1cell-factor gg')
          → lift-2cell-factor σσ Lh Lh'
        )

    -- module _ (cart : 1-cell-cartesian f ff) where
    --   open 1-cell-cartesian cart
    --   open Displayed-functor

    --   lemma : cartesian-1cell
    --   lemma .fst c cc h gg .fst = universal¹ h gg
    --   lemma .fst c cc h gg .snd = commutes¹ h gg
    --   lemma .snd c cc h h' gg gg' δ σσ Lh Lh' .centre .fst = 
    --     Hom[].hom[ Hom.idl _ ∙ Hom.idr _ ] (unique¹.from' (Lh' .snd) ∘' universal² δ σσ ∘' unique¹.to' (Lh .snd))
    --   lemma .snd c cc h h' gg gg' δ σσ Lh Lh' .centre .snd = {!   !}
    --     -- where abstract
    --     --   module Lh = Hom[]._≅[_]_ (Lh .snd)
    --     --   module Lh' = Hom[]._≅[_]_ (Lh' .snd)
    --     --   p : (ff ▶' Hom[].hom[ Hom.idl _ ∙ Hom.idr _ ] (unique¹.from' (Lh' .snd) ∘' universal² δ σσ ∘' unique¹.to' (Lh .snd))) 
    --     --       Hom[].≡[ sym (Hom.idl _ ∙ Hom.idr _) ]
    --     --       (Lh'.from' ∘' σσ ∘' Lh.to') 
    --     --   p = Hom[].cast[] $
    --     --     ff ▶' Hom[].hom[ Hom.idl _ ∙ Hom.idr _ ] (unique¹.from' (Lh' .snd) ∘' universal² δ σσ ∘' unique¹.to' (Lh .snd)) Hom[].≡[]⟨ apd (λ _ → ff ▶'_) (Hom[].unwrap _) ⟩
    --     --     ff ▶' (unique¹.from' (Lh' .snd) ∘' universal² δ σσ ∘' unique¹.to' (Lh .snd)) Hom[].≡[]⟨ postaction' E _ .F-∘' Hom[].∙[] (Hom[].refl⟩∘'⟨ postaction' E _ .F-∘')  ⟩
    --     --     (ff ▶' unique¹.from' (Lh' .snd)) ∘' (ff ▶' universal² δ σσ) ∘' (ff ▶' unique¹.to' (Lh .snd)) Hom[].≡[]⟨ (Hom[].refl⟩∘'⟨ ((commutes² _ _) Hom[].⟩∘'⟨refl)) ⟩
    --     --     (ff ▶' unique¹.from' (Lh' .snd)) ∘' (comm¹.from' ∘' σσ ∘' comm¹.to') ∘' (ff ▶' unique¹.to' (Lh .snd)) Hom[].≡[]⟨ Hom[].pulll[] _ (Hom[].pulll[] _ (unique-comm¹-op _)) ⟩
    --     --     (Lh'.from' ∘' σσ ∘' comm¹.to') ∘' (ff ▶' unique¹.to' (Lh .snd)) Hom[].≡[]⟨ Hom[].pullr[] _ (Hom[].pullr[] _ (unique-comm¹ _)) ⟩
    --     --     Lh'.from' ∘' σσ ∘' Lh.to' ∎


    --   lemma .snd c cc h h' gg gg' δ σσ Lh Lh' .paths x = 
    --     Σ-pathp (Hom[].cast[] $ 
    --       Hom[].hom[ Hom.idl _ ∙ Hom.idr _ ] (unique¹.from' (Lh' .snd) ∘' universal² δ σσ ∘' unique¹.to' (Lh .snd)) Hom[].≡[]⟨ {! x .snd  !} ⟩ 
    --       x .fst ∎ 
    --     )
    --     prop!
     



```
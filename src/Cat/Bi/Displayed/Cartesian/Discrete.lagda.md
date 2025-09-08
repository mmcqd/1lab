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
open import Cat.Displayed.Univalence.Reasoning
open import Cat.Displayed.Instances.TotalProduct

import Cat.Reasoning as Cr
import Cat.Bi.Displayed.Morphism as Cbm
import Cat.Displayed.Cartesian.Discrete.Reasoning as Dcr 


module Cat.Bi.Displayed.Cartesian.Discrete 
  {o oh ℓh o' oh' ℓh'} 
  {B : Prebicategory o oh ℓh} 
  (E : Bidisplayed B o' oh' ℓh') 
  where
```

A discrete bifibration should be one where each of its fibre bicategories is locally discrete, that is, it has
fibre *categories*.

```agda 


open Prebicategory-Hom-Reasoning B 
open Bidisplayed-Hom[]-Reasoning E
open Cbm E

module 1-cell (E* : ∀ {A B} (A' : Ob[ A ]) (B' : Ob[ B ]) → is-discrete-cartesian-fibration Hom[ A' , B' ]) where
  private module _ {A B} {A' : Ob[ A ]} {B' : Ob[ B ]} where
    open is-discrete-cartesian-fibration (E* A' B') public
    open Dcr (E* A' B') public
 

  record is-discrete-cartesian {A B A' B'} (f : A ↦ B) (f' : A' [ f ]↦ B') : Type (o ⊔ o' ⊔ oh ⊔ oh' ⊔ ℓh ⊔ ℓh') where
    no-eta-equality
    field 

      universal¹ 
        : ∀ {U U'} (h : U ↦ A) (g' : U' [ f ⊗ h ]↦ B') → U' [ h ]↦ A'

      commutes¹ 
        : ∀ {U U'} (h : U ↦ A) (g' : U' [ f ⊗ h ]↦ B') 
        → (f' ⊗' universal¹ h g') ≡ g'

      unique¹
        : ∀ {U U'} {h : U ↦ A} {g' : U' [ f ⊗ h ]↦ B'}
        → (other :  U' [ h ]↦ A')
        → (f' ⊗' other) ≡ g'
        → other ≡ universal¹ h g'

      universal² 
        : ∀ {U U'} {h₁ h₂ : U ↦ A} 
        → (δ : h₁ ⇒ h₂) 
        → {g₁' : U' [ f ⊗ h₁ ]↦ B'} {g₂' : U' [ f ⊗ h₂ ]↦ B'}
        → (σ : g₁' [ f ▶ δ ]⇒ g₂')
        → universal¹ h₁ g₁' [ δ ]⇒ universal¹ h₂ g₂' 


    universal'
      : ∀ {U U'} {h : U ↦ A} {k : U ↦ B}
      → (p : f ⊗ h ⇒ k) (g' : U' [ k ]↦ B')
      → U' [ h ]↦ A'
    universal' {U' = U'} p g' = universal¹ _ $ ob[ p ] g'


    opaque
      commutesp¹ 
        : ∀ {U U'} {h : U ↦ A} {k : U ↦ B}
        → (p : f ⊗ h Hom.≅ k) (g' : U' [ k ]↦ B') 
        → (f' ⊗' universal' (p .Hom.to) g') ≡[ p ]ob g'
      commutesp¹ p g' = to-pathp[]ob⁻ p (commutes¹ _ _)
      
      universalp¹
        : ∀ {U U'} {h₁ h₂ : U ↦ A} {k : U ↦ B}
        → (p : f ⊗ h₁ ⇒ k) (q : h₁ Hom.≅ h₂) (r : f ⊗ h₂ ⇒ k)
        → (r ≡ p ∘ f ▶ (q .Hom.from))
        → (g' : U' [ k ]↦ B')
        → universal' p g' ≡[ q ]ob universal' r g'
      universalp¹ {U' = U'} {h₁} {h₂} {k = k} p q r w g' =
        universal² _ $ ^*-hom _ $
        (f ▶ q .Hom.from) ^* ob[ p ] g' ≡˘⟨ ^*-∘ _ _ _ ⟩
        (p ∘ (f ▶ q .Hom.from)) ^* g' ≡⟨ ^*-lift _ (Hom[].hom[ w ] (π* _ _)) ⟩
        ob[ r ] g' ∎
    
      uniquep¹ 
        : ∀ {U U'} {h₁ h₂ : U ↦ A} {k : U ↦ B}
        → (p : f ⊗ h₁ Hom.≅ k) (q : h₁ Hom.≅ h₂) (r : f ⊗ h₂ ⇒ k)
        → (r ≡ p .Hom.to ∘ f ▶ (q .Hom.from))
        → {g' : U' [ k ]↦ B'}
        → (other : U' [ h₁ ]↦ A')
        → (f' ⊗' other) ≡[ p ]ob g' 
        → other ≡[ q ]ob universal' r g'
      uniquep¹ p q r w other c = 
        to-pathp[]ob⁻ q ((unique¹ other (from-pathp[]ob⁻ p c)) ∙ from-pathp[]ob⁻ q (universalp¹ (p .Hom.to) q r w _))

      uniquep₂¹
        : ∀ {U U'} {h₁ h₂ : U ↦ A} {k : U ↦ B}
        → (p : f ⊗ h₁ Hom.≅ k) (q : h₁ Hom.≅ h₂) (r : f ⊗ h₂ Hom.≅ k)
        → (r .Hom.to ≡ p .Hom.to ∘ f ▶ (q .Hom.from))
        → {g' : U' [ k ]↦ B'}
        → (other₁ : U' [ h₁ ]↦ A') (other₂ : U' [ h₂ ]↦ A')
        → (f' ⊗' other₁) ≡[ p ]ob g' 
        → (f' ⊗' other₂) ≡[ r ]ob g' 
        → other₁ ≡[ q ]ob other₂
      uniquep₂¹ p q r x other₁ other₂ α β = to-pathp[]ob⁻ q $ 
           unique¹ other₁ (from-pathp[]ob⁻ p α) 
        ∙∙ from-pathp[]ob⁻ q (universalp¹ (p .Hom.to) q (r .Hom.to) x _) 
        ∙∙ ap ob[ q .Hom.to ] (sym (unique¹ other₂ (from-pathp[]ob⁻ r β)))

  record discrete-cartesian-lift {A B} (f : A ↦ B) (B' : Ob[ B ]) : Type (o ⊔ o' ⊔ oh ⊔ oh' ⊔ ℓh ⊔ ℓh') where
    no-eta-equality
    field
      {A'} : Ob[ A ]
      lifting : A' [ f ]↦ B'
      cartesian : is-discrete-cartesian f lifting

    open is-discrete-cartesian cartesian public

record is-discrete-cartesian-bifibration : Type (o ⊔ oh ⊔ ℓh ⊔ o' ⊔ oh' ⊔ ℓh') where
  no-eta-equality
  field 
    2-cart : ∀ {A B} (A' : Ob[ A ]) (B' : Ob[ B ]) → is-discrete-cartesian-fibration Hom[ A' , B' ]
    1-cart : ∀ {A B} (f : A ↦ B) (B' : Ob[ B ]) → 1-cell.discrete-cartesian-lift 2-cart f B'

  module _ {A B} (f : A ↦ B) (B' : Ob[ B ]) where
    open 1-cell.discrete-cartesian-lift (1-cart f B') 
      using () 
      renaming (A' to _^*1_ ; lifting to π*1)
      public

  module π*1 {A B} {f : A ↦ B} {B' : Ob[ B ]} where
    open 1-cell.discrete-cartesian-lift (1-cart f B') 
      hiding (A' ; lifting)
      public

  module _ {A B} {A' : Ob[ A ]} {B' : Ob[ B ]} where
    open is-discrete-cartesian-fibration (2-cart A' B')
      renaming (_^*_ to _^*2_ ; π* to π*2)
      public

module _ (E* : Cartesian-bifibration E) (locally : ∀ {A B} (A' : Ob[ A ]) (B' : Ob[ B ]) → is-discrete-cartesian-fibration Hom[ A' , B' ]) where
  open Cartesian-bifibration E*
  private module _ {A B} {A' : Ob[ A ]} {B' : Ob[ B ]} where
    open is-discrete-cartesian-fibration (locally A' B') public
    open Dcr (locally A' B') public

  
  open 1-cell.discrete-cartesian-lift
  open 1-cell.is-discrete-cartesian
  
  bifibration→discrete : is-discrete-cartesian-bifibration
  bifibration→discrete .is-discrete-cartesian-bifibration.1-cart f B' .A' = f ^*1 B'
  bifibration→discrete .is-discrete-cartesian-bifibration.1-cart f B' .lifting = π*1 f B'
  bifibration→discrete .is-discrete-cartesian-bifibration.1-cart f B' .cartesian .universal¹ = π*1.universal¹
  bifibration→discrete .is-discrete-cartesian-bifibration.1-cart f B' .cartesian .commutes¹ h g' = 
    vertical-iso→path Hom[ _ , _ ] discrete→is-category-displayed (π*1.commutes¹ h g')
  bifibration→discrete .is-discrete-cartesian-bifibration.1-cart f B' .cartesian .unique¹ other p = 
    vertical-iso→path Hom[ _ , _ ] discrete→is-category-displayed $
    Hom[].make-vertical-iso 
      (π*1.universal² (path→vertical-iso _ p) (π*1.commutes¹ _ _) (Hom[].hom[ compose.F-id ]⁻ ⇒id')) 
      (π*1.universal² (π*1.commutes¹ _ _) (path→vertical-iso _ p) (Hom[].hom[ compose.F-id ]⁻ ⇒id')) 
      prop! 
      prop!
  bifibration→discrete .is-discrete-cartesian-bifibration.1-cart f B' .cartesian .universal² δ σ = 
    π*1.universal² (π*1.commutes¹ _ _) (π*1.commutes¹ _ _) σ
  bifibration→discrete .is-discrete-cartesian-bifibration.2-cart = locally


module _ (E* : is-discrete-cartesian-bifibration) where
  open is-discrete-cartesian-bifibration E*
  open 1-cell-cartesian-lift
  open 1-cell-cartesian
  open is-fibred-functor

  discrete→bifibration : Cartesian-bifibration E
  discrete→bifibration .Cartesian-bifibration.1-cart f B' .A' = f ^*1 B'
  discrete→bifibration .Cartesian-bifibration.1-cart f B' .lifting = π*1 f B'
  discrete→bifibration .Cartesian-bifibration.1-cart f B' .cartesian .universal¹ h g' = π*1.universal¹ h g' 
  discrete→bifibration .Cartesian-bifibration.1-cart f B' .cartesian .commutes¹ h g' = path→vertical-iso _ (π*1.commutes¹ h g')
  discrete→bifibration .Cartesian-bifibration.1-cart f B' .cartesian .universal² 
    {h₁ = h₁} {h₂ = h₂} {δ = δ} {h₁' = h₁'} {h₂' = h₂'} {g₁' = g₁'} {g₂' = g₂'} i₁ i₂ σ' = 
    Hom[].hom[ Hom.idl _ ∙ Hom.idr _ ] 
    (
      subst (λ z → π*1.universal¹ h₂ g₂' [ Hom.id ]⇒ z) (sym p) ⇒id' ∘' 
      π*1.universal² δ σ' ∘' 
      subst (λ z → z [ Hom.id ]⇒  π*1.universal¹ h₁ g₁') (sym q) ⇒id'
    )
    where
      p : h₂' ≡ π*1.universal¹ h₂ g₂'
      p = π*1.unique¹ h₂' (vertical-iso→path Hom[ _ , _ ] (Dcr.discrete→is-category-displayed $ 2-cart _ _) i₂)

      q : h₁' ≡ π*1.universal¹ h₁ g₁'
      q = π*1.unique¹ h₁' (vertical-iso→path Hom[ _ , _ ] (Dcr.discrete→is-category-displayed $ 2-cart _ _) i₁)

  discrete→bifibration .Cartesian-bifibration.1-cart f B' .cartesian .commutes² _ _ _ = prop!
  discrete→bifibration .Cartesian-bifibration.1-cart f B' .cartesian .unique² _ _ = prop!
  discrete→bifibration .Cartesian-bifibration.2-cart = discrete→cartesian _ (2-cart _ _ )
  discrete→bifibration .Cartesian-bifibration.is-fibred-compose' .F-cartesian x = all-cartesian _
```
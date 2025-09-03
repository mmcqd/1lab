<!--
```agda
open import Cat.Prelude
open import Cat.Bi.Base
open import Cat.Displayed.Instances.TotalProduct
open import Cat.Displayed.Functor.Naturality
open import Cat.Displayed.Instances.FullSubcategory
open import Cat.Displayed.Functor
open import Cat.Bi.Displayed.Base
```
-->
```agda
module Cat.Bi.Displayed.Instances.2FullSubBicategory
  {o oh ℓh o' oh' ℓh'} 
  {B : Prebicategory o oh ℓh}
  (E : Bidisplayed B o' oh' ℓh') 
  where
```
# 2-full sub-bicategories

A *2-full sub-bicategory* of a displayed bicategory $\bB$ chooses 
a subset of displayed objects and displayed 1-cells, but keeps all displayed 2-cells.

```agda
open Prebicategory B
open Bidisplayed E
open Displayed-functor
open make-natural-iso[_]
open _=[_]=>_


record 2-full-sub-bicat ℓₒ ℓₕ : Type (lsuc (ℓₒ ⊔ ℓₕ) ⊔ o ⊔ oh ⊔ o' ⊔ oh') where
  no-eta-equality
  field
    is-ob[]     : ∀ {x} → Ob[ x ] → Type ℓₒ
    is-hom[]    : ∀ {A B A' B'} {f : A ↦ B} → A' [ f ]↦ B' → Type ℓₕ
    is-hom[]-id : ∀ {A A'} → is-hom[] (↦id' {A} {A'})
    is-hom[]-∘  : ∀ {A B C A' B' C'} {f : B ↦ C} {g : A ↦ B}
                → {f' : B' [ f ]↦ C'} {g' : A' [ g ]↦ B'}
                → is-hom[] f' → is-hom[] g'
                → is-hom[] (f' ⊗' g')

module _ 
  {ℓₒ ℓₕ} 
  (𝐏 : 2-full-sub-bicat ℓₒ ℓₕ) where

  private module 𝐏 = 2-full-sub-bicat 𝐏

  Restrict-compose' : ∀ {A B C A' B' C'} → Displayed-functor (compose {A} {B} {C})
    (Restrict Hom[ B' , C' ] 𝐏.is-hom[] ×ᵀᴰ Restrict Hom[ A' , B' ] 𝐏.is-hom[])
    (Restrict Hom[ A' , C' ] 𝐏.is-hom[])
  Restrict-compose' .F₀' ((f' , Pf') , (g' , Pg')) = f' ⊗' g' , 𝐏.is-hom[]-∘ Pf' Pg'
  Restrict-compose' .F₁' = compose'.F₁'
  Restrict-compose' .F-id' = compose'.F-id'
  Restrict-compose' .F-∘' = compose'.F-∘'

  Birestrict : Bidisplayed B _ _ _
  Birestrict .Bidisplayed.Ob[_] x = Σ Ob[ x ] 𝐏.is-ob[]
  Birestrict .Bidisplayed.Hom[_,_] (A , _) (B , _) = Restrict Hom[ A , B ] 𝐏.is-hom[]
  Birestrict .Bidisplayed.↦id' = ↦id' , 𝐏.is-hom[]-id
  Birestrict .Bidisplayed.compose' = Restrict-compose'
  Birestrict .Bidisplayed.unitor-l' = to-natural-iso' ni where
    ni : make-natural-iso[ _ ] _ _
    ni .eta' _ = λ→' _
    ni .inv' _ = λ←' _
    ni .eta∘inv' _ = unitor-l'.invl' ηₚ' _
    ni .inv∘eta' _ = unitor-l'.invr' ηₚ' _
    ni .natural' _ _ _ = λ→nat' _
  Birestrict .Bidisplayed.unitor-r' = to-natural-iso' ni where
    ni : make-natural-iso[ _ ] _ _
    ni .eta' _ = ρ→' _
    ni .inv' _ = ρ←' _
    ni .eta∘inv' _ = unitor-r'.invl' ηₚ' _
    ni .inv∘eta' _ = unitor-r'.invr' ηₚ' _
    ni .natural' _ _ _ = ρ→nat' _
  Birestrict .Bidisplayed.associator' = to-natural-iso' ni where
    ni : make-natural-iso[ _ ] _ _
    ni .eta' _ = α→' _ _ _
    ni .inv' _ = α←' _ _ _
    ni .eta∘inv' _ = associator'.invl' ηₚ' _
    ni .inv∘eta' _ = associator'.invr' ηₚ' _
    ni .natural' _ _ _ = α→nat' _ _ _
  Birestrict .Bidisplayed.triangle' _ _ = triangle' _ _
  Birestrict .Bidisplayed.pentagon' _ _ _ _ = pentagon' _ _ _ _
```



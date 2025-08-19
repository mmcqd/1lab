open import Cat.Prelude
open import Cat.Bi.Base
open import Cat.Bi.Displayed.Base
open import Cat.Bi.Displayed.Cartesian
open import Cat.Morphism hiding (Ob ; Hom)

import Cat.Bi.Morphism as BM
import Cat.Bi.Displayed.Morphism as DBM

module Cat.Bi.Displayed.Cartesian.Properties 
  {o oh ℓh o' oh' ℓh'} {B : Prebicategory o oh ℓh} 
  (E : Bidisplayed B o' oh' ℓh')
  where

private module B = Prebicategory B
open Prebicategory B 
open Bidisplayed-Hom[]-Reasoning E
open BM B
open DBM E

module _
  {A B A' B'} {f : A ↦ B} {f' : A' [ f ]↦ B'} 
  {U U'} {m₁ m₂ : U ↦ A} {h₁' : U' [ f ⊗ m₁ ]↦ B'} {h₂' : U' [ f ⊗ m₂ ]↦ B'}
  {δ : m₁ ⇒ m₂} {σ : h₁' [ f ▶ δ ]⇒ h₂'}
  (cart : 1-cell-cartesian E f f')
  (δ-inv : is-invertible (Hom U A) δ)
  (σ-inv : Hom[].is-invertible[ ▶-inv δ-inv ] σ)
  where
  private
    module f* = 1-cell-cartesian cart
    module δ-inv = is-invertible δ-inv
    module σ-inv = Hom[].is-invertible[_] σ-inv

    
  inv* : f*.universal¹ m₂ h₂' [ δ-inv.inv ]⇒ f*.universal¹ m₁ h₁'
  inv* = f*.universal² δ-inv.inv σ-inv.inv'
  
  lemma₁ : ∀ {p} → f' ▶' (f*.universal² δ σ ∘' inv*) Hom[].≡[ p ] (f*.comm¹.from' ∘' Hom[].id' ∘' f*.comm¹.to')
  lemma₁ = Hom[].cast[] $ 
    compose'.F₁' (Hom[].id' , f*.universal² δ σ ∘' inv*)                                        Hom[].≡[]˘⟨ apd (λ _ e → compose'.F₁' (e , (f*.universal² δ σ ∘' inv*))) (Hom[].idl' _) ⟩
    compose'.F₁' (Hom[].id' ∘' Hom[].id' , f*.universal² δ σ ∘' inv*)                           Hom[].≡[]⟨ compose'.F-∘' ⟩
    (f' ▶' f*.universal² δ σ) ∘' (f' ▶' inv*)                                                   Hom[].≡[]⟨ (f*.commutes² _ _ Hom[].⟩∘'⟨ f*.commutes² _ _) ⟩
    (f*.comm¹.from' ∘' (σ ∘' f*.comm¹.to')) ∘' (f*.comm¹.from' ∘' (σ-inv.inv' ∘' f*.comm¹.to')) Hom[].≡[]⟨ Hom[].pulll[] _ (Hom[].pullr[] _ (Hom[].cancelr[] _ f*.comm¹.invl')) ⟩
    (f*.comm¹.from' ∘' σ) ∘' (σ-inv.inv' ∘' f*.comm¹.to')                                       Hom[].≡[]⟨ Hom[].pull-inner[] _ σ-inv.invl'  ⟩
    f*.comm¹.from' ∘' ⇒id' ∘' f*.comm¹.to'                                                ∎
  
  lemma₂ : f' ▶' (⇒id' {f' = f*.universal¹ m₂ h₂'}) Hom[].≡[ sym (Hom.idl _ ∙ Hom.idr _ ∙ sym compose.F-id) ] (f*.comm¹.from' ∘' Hom[].id' ∘' f*.comm¹.to')
  lemma₂ = Hom[].cast[] $
    f' ▶' ⇒id'                                  Hom[].≡[]⟨ compose'.F-id' ⟩
    ⇒id'                                        Hom[].≡[]˘⟨ f*.comm¹.invr' ⟩
    f*.comm¹.from' ∘' f*.comm¹.to'              Hom[].≡[]˘⟨ Hom[].refl⟩∘'⟨ Hom[].idl' _ ⟩
    f*.comm¹.from' ∘' Hom[].id' ∘' f*.comm¹.to' ∎


module _
  {A B A' B'} {f : A ↦ B} {f' : A' [ f ]↦ B'} 
  {U U'} {m₁ m₂ : U ↦ A} {h₁' : U' [ f ⊗ m₁ ]↦ B'} {h₂' : U' [ f ⊗ m₂ ]↦ B'}
  {δ : m₁ ⇒ m₂} {σ : h₁' [ f ▶ δ ]⇒ h₂'}
  (cart : 1-cell-cartesian E f f')
  (δ-inv : is-invertible (Hom U A) δ)
  (σ-inv : Hom[].is-invertible[ ▶-inv δ-inv ] σ)
  where
  private
    module f* = 1-cell-cartesian cart
    module δ-inv = is-invertible δ-inv
    module σ-inv = Hom[].is-invertible[_] σ-inv

  inv-lift : Hom[].is-invertible[ δ-inv ] (f*.universal² δ σ)
  inv-lift = Hom[].make-invertible[ δ-inv ] (inv* cart δ-inv σ-inv) invl* invr* where
  

    invl* : _
    invl* = f*.uniquep²₂ {σ = Hom[].id'} (ap (f ▶_) δ-inv.invl ∙ compose.F-id) _ compose.F-id _ _ (lemma₁ cart δ-inv σ-inv) (lemma₂ cart δ-inv σ-inv)

    invr* : _
    invr* = f*.uniquep²₂ {σ = Hom[].id'} (ap (f ▶_) δ-inv.invr ∙ compose.F-id) _ compose.F-id _ _ (lemma₁ cart δ-inv.op σ-inv.op') (lemma₂ cart δ-inv.op σ-inv.op')

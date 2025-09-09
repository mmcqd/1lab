
```agda
open import Cat.Prelude
open import Cat.Displayed.Cartesian.Discrete
open import Cat.Displayed.Functor
open import Cat.Displayed.Composition
open import Cat.Displayed.Total renaming (∫ to ∫' ; πᶠ to πᶠ')
open import Cat.Bi.Base
open import Cat.Bi.Displayed.Base
open import Cat.Functor.Adjoint
open import Cat.Bi.Displayed.Cartesian.Discrete.Fibre
open import Cat.Bi.Displayed.Instances.FullSubBicategory 

module Cat.Bi.Displayed.Instances.DFib where
  
```

*DFib*, the displayed bicategory of *discrete* fibrations,
is the full sub-bicategory of `Displayed-cat` which picks out the discrete fibrations.

```agda

module _ o ℓ o' ℓ' where
  DFib : Bidisplayed (Cat o ℓ) _ _ _
  DFib = Birestrict (Displayed-cat o ℓ o' ℓ') is-discrete-cartesian-fibration
```
  

```agda 
module _ {o' ℓ'} where
  private 
    module Cat o ℓ = Prebicategory (Cat o ℓ)
    module DFib {o ℓ} = Bidisplayed (DFib o ℓ o' ℓ')

  ∫ : ∀ {o ℓ} {A : Cat.Ob o ℓ} → DFib.Ob[ A ] → Precategory _ _
  ∫ (x , _) = ∫' x

  πᶠ : ∀ {o ℓ} {A : Cat.Ob o ℓ} (E : DFib.Ob[ A ]) → Functor (∫ E) A
  πᶠ (E , _) = πᶠ' E

  is-representable : ∀ {o ℓ} → {A : Cat.Ob o ℓ} (E : DFib.Ob[ A ]) → DFib.Ob[ ∫ E ] → Type _
  is-representable E E' = Σ[ δ ∈ Functor (∫ E ) (∫ E') ] πᶠ E' ⊣ δ

  DFibΣ : ∀ {o ℓ} {A : Cat.Ob o ℓ} (E : DFib.Ob[ A ]) → DFib.Ob[ ∫ E ] → DFib.Ob[ A ]
  DFibΣ (E , E*) (E' , E'*) = (E D∘ E') , discrete-∘ E* E'*


```
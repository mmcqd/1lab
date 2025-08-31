


```agda

open import Cat.Prelude
open import Cat.Instances.Functor
open import Cat.Displayed.Base
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Functor
open import Cat.Displayed.Functor.Naturality
open import Cat.Displayed.Instances.DisplayedFunctor

import Cat.Reasoning as CR
import Cat.Displayed.Reasoning as DR
import Cat.Displayed.Morphism as DM

module Cat.Displayed.Functor.Cartesian where

open _=>_
open _=[_]=>_
open Functor
open Displayed-functor

module _ 
  {oa ℓa ob ℓb oa' ℓa' ob' ℓb'} 
  {A : Precategory oa ℓa} {B : Precategory ob ℓb}
  {D : Displayed A oa' ℓa'} {E : Displayed B ob' ℓb'}
  where
  private
    module A = CR A
    module B = CR B
    module D = Displayed D
    module E where
      open DR E public
      open DM E public

```
Being cartesian in $\cE$ is a sufficient condition for being cartesian in $[\cD, \cE]$.

```agda
  private
    module Cat[] = CR Cat[ A , B ]
    module Disp[] where
      open DR Disp[ D , E ] public
      open DM Disp[ D , E ] public

  module _ 
    {f g : Cat[].Ob} {α : Cat[].Hom f g} 
    {f' : Disp[].Ob[ f ]} {g' : Disp[].Ob[ g ]} 
    {α' : Disp[].Hom[ α ] f' g'}  
    where

    Disp[]-cartesian : (cart : ∀ {x} x' → is-cartesian E (α .η x) (α' .η' x')) → is-cartesian Disp[ D , E ] α α'
    Disp[]-cartesian cart = α'-cart where
      module _ {x} x' where open is-cartesian (cart {x} x') public

      α'-cart : is-cartesian _ _ _
      α'-cart .is-cartesian.universal m h' = NT' (λ x' → universal x' _ (h' .η' x')) λ x' y' f' → 
        uniquep₂ _ _ _ _ _ _ (E.pulll[] _ (commutes _ _ _) E.∙[] h' .is-natural' _ _ _) ((E.pulll[] _ (α' .is-natural' _ _ _)) E.∙[] E.pullr[] _ (commutes _ _ _))
      α'-cart .is-cartesian.commutes m h' = Nat'-path λ x' → commutes _ _ _
      α'-cart .is-cartesian.unique m' p = Nat'-path λ x' → unique _ _ (p ηₚ' x')

```

If $\cE$ is a fibration, then $[\cD, \cE] \liesover [\cA, \cB]$ is also a fibration.

```agda 
  module _ (E* : Cartesian-fibration E) where

    open Cartesian-fibration _ E*
    open Cartesian-lift
    open is-cartesian


    Disp^* : {f g : Functor A B} (α : f => g) → Displayed-functor g D E → Displayed-functor f D E
    Disp^* α g' .F₀' {x} x' = α .η x ^* g' .F₀' x'
    Disp^* α g' .F₁' h' = π*.universal' (α .is-natural _ _ _) (g' .F₁' h' E.∘' π* (α .η _) (g' .F₀' _))
    Disp^* α g' .F-id' = symP $ π*.uniquep _ _ _ _ (E.idr' _ E.∙[] symP (E.eliml[] _ (g' .F-id')))
    Disp^* α g' .F-∘' = symP $ π*.uniquep _ _ _ _ $ 
      E.pulll[] _ (π*.commutesp (α .is-natural _ _ _) _) 
        E.∙∙[] 
      E.pullr[] _ (π*.commutesp (α .is-natural _ _ _) _)
          ∙∙[] 
      E.pulll[] _ (symP $ g' .F-∘') 
    
    Disp[]-fibration : Cartesian-fibration Disp[ D , E ]
    Disp[]-fibration {x = f} {y = g} α g' .x' = Disp^* α g'
    Disp[]-fibration {x = f} {y = g} α g' .lifting = NT' (λ {x} x' → π* (α .η x) (g' .F₀' x')) λ x' y' f' → π*.commutesp _ _
    Disp[]-fibration {x = f} {y = g} α g' .cartesian = Disp[]-cartesian λ {x} x' → π*.cartesian

    private module Disp[]* = Cartesian-fibration _ Disp[]-fibration
```

In fact, Disp[]-cartesian is an equivalence.

```agda 
    module _ 
      {f g : Cat[].Ob} {α : Cat[].Hom f g} 
      {f' : Disp[].Ob[ f ]} {g' : Disp[].Ob[ g ]} 
      {α' : Disp[].Hom[ α ] f' g'}  
      where

      η'-cartesian : is-cartesian Disp[ D , E ] α α' → ∀ {x} x' → is-cartesian E (α .η x) (α' .η' x')
      η'-cartesian cart x' = domain-iso→cartesian _ 
            (iso[]ⁿ→iso _ 
              (cartesian-domain-unique _ cart Disp[]*.π*.cartesian) 
              x'
            ) 
            (π*.commutesp (B.idr _) _)
            π*.cartesian
```

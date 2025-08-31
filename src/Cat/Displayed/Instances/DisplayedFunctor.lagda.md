<!--
```agda
open import Cat.Displayed.Instances.FullSubcategory
open import Cat.Displayed.Instances.TotalProduct
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Total
open import Cat.Displayed.Functor
open import Cat.Instances.Functor
open import Cat.Functor.Compose
open import Cat.Displayed.Base
open import Cat.Prelude

import Cat.Reasoning as CR
import Cat.Displayed.Reasoning as DR
import Cat.Displayed.Morphism as DM
```
-->

```agda
module Cat.Displayed.Instances.DisplayedFunctor where
```

# Displayed functor categories {defines=displayed-functor-category}

Given two displayed categories $\cD \liesover \cA$ and $\cE \liesover \cB$, we
can assemble them into a displayed category $[\cD, \cE] \liesover [\cA, \cB]$.
The construction mirrors the construction of ordinary functor categories,
using displayed versions of all the same data.

<!--
```agda
open _=>_
open _=[_]=>_
open Functor
open Displayed-functor

module _ 
  {oa ℓa ob ℓb oa' ℓa' ob' ℓb'} 
  {A : Precategory oa ℓa} {B : Precategory ob ℓb}
  (D : Displayed A oa' ℓa') (E : Displayed B ob' ℓb')
  where
  private
    module A = CR A
    module B = CR B
    module D = Displayed D
    module E = DR E
```
-->

```agda
  Disp[_,_] : Displayed (Cat[ A , B ]) _ _
  Disp[_,_] .Displayed.Ob[_] f = Displayed-functor f D E
  Disp[_,_] .Displayed.Hom[_] α F' G' = F' =[ α ]=> G'
  Disp[_,_] .Displayed.Hom[_]-set _ _ _ = hlevel 2
  Disp[_,_] .Displayed.id' = idnt'
  Disp[_,_] .Displayed._∘'_ = _∘nt'_
  Disp[_,_] .Displayed.idr' _ = Nat'-path λ x' → E.idr' _
  Disp[_,_] .Displayed.idl' _ = Nat'-path λ x' → E.idl' _
  Disp[_,_] .Displayed.assoc' _ _ _ = Nat'-path λ x' → E.assoc' _ _ _
  Disp[_,_] .Displayed.hom[_] {x = F} {y = G} p α' = NT' (λ {x} x' → E.hom[ p ηₚ x ] (α' .η' x')) 
    λ {x} {y} x' y' f' → E.cast[] $ E.unwrapl _ E.∙∙[] α' .is-natural' x' y' f' ∙∙[] E.wrapr _
  Disp[_,_] .Displayed.coh[_] p f = Nat'-path (λ {x} x' → E.coh[ p ηₚ x ] (f .η' x'))
```


<!--
```agda
module _ 
  {oa ℓa ob ℓb oc ℓc oa' ℓa' ob' ℓb' oc' ℓc'} 
  {A : Precategory oa ℓa} {B : Precategory ob ℓb}
  {C : Precategory oc ℓc} 
  {A' : Displayed A oa' ℓa'} {B' : Displayed B ob' ℓb'}
  {C' : Displayed C oc' ℓc'} 
  {F G : Functor B C} {H K : Functor A B}
  {α : F => G} {β : H => K}
  {F' : Displayed-functor F B' C'} {G' : Displayed-functor G B' C'}
  {H' : Displayed-functor H A' B'} {K' : Displayed-functor K A' B'}
  where
  private
    module B' = Displayed B'
    module C' = DR C'
```
-->

We can also construct a displayed version of the [[functor composition functor|composition-functor]]. 
First we'll define displayed horizontal composition of natural transformations.

```agda
  _◆'_ : F' =[ α ]=> G' → H' =[ β ]=> K' → F' F∘' H' =[ α ◆ β ]=> G' F∘' K'
  (α' ◆' β') .η' x' = G' .F₁' (β' .η' _) C'.∘' α' .η' _
  (α' ◆' β') .is-natural' x' y' f' = cast[] $
    (G' .F₁' (β' .η' y') ∘' α' .η' (H' .F₀' y')) ∘' F' .F₁' (H' .F₁' f')  ≡[]⟨ pullr[] _ (α' .is-natural' _ _ _) ⟩
     G' .F₁' (β' .η' y') ∘' G' .F₁' (H' .F₁' f') ∘' α' .η' (H' .F₀' x')   ≡[]⟨ pulll[] _ (symP (G' .F-∘') ∙[] apd (λ _ → G' .F₁') (β' .is-natural' _ _ _) ∙[] G' .F-∘') ⟩
    (G' .F₁' (K' .F₁' f') ∘' G' .F₁' (β' .η' x')) ∘' α' .η' (H' .F₀' x')  ≡[]˘⟨ assoc' _ _ _ ⟩ 
     G' .F₁' (K' .F₁' f') ∘' G' .F₁' (β' .η' x') ∘' α' .η' (H' .F₀' x')   ∎  
    where open C'
```

<!--
```agda
module _ 
  {oa ℓa ob ℓb oc ℓc oa' ℓa' ob' ℓb' oc' ℓc'} 
  {A : Precategory oa ℓa} {B : Precategory ob ℓb}
  {C : Precategory oc ℓc} 
  {A' : Displayed A oa' ℓa'} {B' : Displayed B ob' ℓb'}
  {C' : Displayed C oc' ℓc'} 
  where
  private 
    module A = CR A
    module A' = Displayed A'
    module B = CR B
    module B' = Displayed B'
    module C = CR C
    module C' = Displayed C'
```
-->

:::{.definition #displayed-composition-functor}
Armed with this, we can define our displayed composition functor.
:::

```agda
  F∘'-functor : Displayed-functor F∘-functor (Disp[ B' , C' ] ×ᵀᴰ Disp[ A' , B' ]) Disp[ A' , C' ]
  F∘'-functor .F₀' (F' , G') = F' F∘' G' 
  F∘'-functor .F₁' (α' , β') = α' ◆' β'
  F∘'-functor .F-id' {F , G} {F' , G'} = 
    Nat'-path λ x' → C'.idr' _ C'.∙[] F' .F-id'
  F∘'-functor .F-∘' {a' = F' , G'} {H' , I'} {J' , K'} {α' , _} {β' , _} = 
    Nat'-path λ x' → 
        pushl[] _ (J' .F-∘')                              C'.∙[] 
        ((extend-inner' _ (symP (α' .is-natural' _ _ _))) C'.∙[] 
        (pulll' refl refl))
      where open DR C'
```

We can also define a restriction of this functor for any property that respects composition.


If *insert conditions here*, then the displayed composition functor itself is fibred.

```agda 
  -- module _ (C'* : Cartesian-fibration C') where
  --   open Cartesian-fibration _ C'*

  --   open is-fibred-functor
  --   open is-cartesian

  --   F∘'-functor-fibred : is-fibred-functor F∘'-functor
  --   F∘'-functor-fibred .F-cartesian {a = F , H} {b = G , K} {a' = F' , H'} {b' = G' , K'} {f = α , β} {f' = α' , β'} cart = 
  --     Disp[ _ , _ ]-cartesian λ {x} x' → cartesian-∘ C' (G'-fibred .F-cartesian (×ᵀᴰ-cartesian _ _ {!   !} .fst)) {!   !} where

      

  --     module cart = is-cartesian cart
  --     postulate
  --       F'-fibred : is-fibred-functor F'
  --       H'-fibred : is-fibred-functor H'
  --       G'-fibred : is-fibred-functor G'
  --       K'-fibred : is-fibred-functor K'
  --     module F'-fibred = is-fibred-functor F'-fibred
  --     module H'-fibred = is-fibred-functor H'-fibred
  --     module F'∘H'-fibred = is-fibred-functor (F∘'-fibred F'-fibred H'-fibred)
  --     module G'∘K'-fibred = is-fibred-functor (F∘'-fibred G'-fibred K'-fibred)
        
  --     ◆'-cart : is-cartesian _ (α ◆ β) (α' ◆' β')
  --     ◆'-cart = {! F'∘H'-fibred.F-cartesian  !}

      -- ◆'-cart : is-cartesian _ _ _
      -- ◆'-cart .universal {u = u} {u' = u'} m h' = NT' (λ {x} x' → {! F'∘H'-fibred.F-cartesian  !}) {!   !} where
      --   postulate
      --     u'-fibred : is-fibred-functor u'
      --     F'-fibred : is-fibred-functor F'
      --     H'-fibred : is-fibred-functor H'
      --     G'-fibred : is-fibred-functor G'
      --     K'-fibred : is-fibred-functor K'
      --   module u'-fibred = is-fibred-functor u'-fibred
      --   module F'-fibred = is-fibred-functor F'-fibred
      --   module H'-fibred = is-fibred-functor H'-fibred
      --   module F'∘H'-fibred = is-fibred-functor (F∘'-fibred F'-fibred H'-fibred)
      --   module G'∘K'-fibred = is-fibred-functor (F∘'-fibred G'-fibred K'-fibred)

      --   -- lemma : ∀ {x} (x' : A'.Ob[ x ]) → h' .η' x' C'.≡[ _ ] _
      --   -- lemma {x} x' = G'∘K'-fibred.uniquep {!   !} {!   !} (sym {! β .is-natural _ _ _  !}) {!   !} (h' .η' x') (symP (h' .is-natural' _ _ _))
      --     --  G'∘K'-fibred.uniquep {!   !} (h' .η' x') {! symP $ h' .is-natural' _ _ _ !}




      -- ◆'-cart .commutes = {!   !}
      -- ◆'-cart .unique = {!   !}
```

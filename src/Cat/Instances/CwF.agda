
open import Cat.Prelude
open import Cat.Bi.Base
open import Cat.Bi.Displayed.Base
open import Cat.Bi.Displayed.DFib
open import Cat.Bi.Displayed.Cartesian
open import Cat.Displayed.Cartesian.Discrete
open import Cat.Displayed.Cartesian
open import Cat.Functor.Adjoint
open import Cat.Displayed.Base
open import Cat.Displayed.Functor
open import Cat.Displayed.Composition
open import Cat.Instances.Functor
open import Cat.Displayed.Total hiding (∫ ; πᶠ)


import Cat.Displayed.Reasoning as DR
import Cat.Reasoning


module Cat.Instances.CwF where

open Displayed-functor

module DFib-Ob {o ℓ o' ℓ'} {𝒮 : Precategory o ℓ} ((A , A*) : Σ (Displayed 𝒮 o' ℓ') is-discrete-cartesian-fibration) where
  open Displayed A public
  open DR A public
  open Cartesian-fibration A (discrete→cartesian A A*) public
  open is-discrete-cartesian-fibration A* hiding (_^*_ ; π*) public


record Sub-notation {ℓ ℓ'} (Ix : Type ℓ) (A : Ix → Type ℓ') : Typeω where
  constructor sub-notation
  field
    {lvl} : Level
    Subst : Ix → Ix → Type lvl
    _[_] : ∀ {i j} → A i → Subst j i → A j
  infix 50 _[_]

open Sub-notation ⦃...⦄ using (_[_]) public

record Sub-Rel-notation {ℓ ℓ'} (Ix : Type ℓ) (A : Ix → Type ℓ') : Typeω where
  constructor sub-rel-notation
  field
    {l1 l2} : Level
    Subst : Ix → Ix → Type l1
    _[_]≡_ : ∀ {i j} → A i → Subst j i → A j → Type l2
  infix 40 _[_]≡_

open Sub-Rel-notation ⦃...⦄ using (_[_]≡_) public

{-# DISPLAY Sub-Rel-notation._[_]≡_ _ A γ B = A [ γ ]≡ B #-}

record CwF o ℓ : Type (lsuc (o ⊔ ℓ)) where
  open ∫Hom
  field
    𝒞 : Precategory o ℓ

  module 𝒞 = Cat.Reasoning 𝒞
  open Prebicategory (Cat o ℓ) public
  open Bidisplayed (DFib o ℓ o ℓ) renaming (Ob[_] to DFib[_]) public
  open Bicartesian-fibration (DFib-bicartesian o ℓ o ℓ) public

  DFibConst : ∀ {A} (E : DFib[ A ]) → DFib[ ∫ E ]
  DFibConst E = πᶠ E ^*1 E

  -- foo : ∀ {A} (E : DFib[ A ]) (F : DFib[ A ]) → DFib[ ∫ E ]
  -- foo E F = πᶠ E ^*1 F

  πᶜ : ∀ {A} {E : DFib[ A ]} → DFibConst E [ πᶠ E ]↦ E
  πᶜ {E = E} = π*1 (πᶠ E) E

  field
    Tp  : DFib[ 𝒞 ]
    Chk : DFib[ ∫ Tp ]
    Extension : is-representable Tp Chk

  open _⊣_ (Extension .snd) hiding (η ; ε)

  Syn : DFib[ 𝒞 ]
  Syn = DFibΣ Tp Chk

  -- In Uemura's paper, (A ≡ Syn) and (B ≡ Tp)

  Infer : Syn []↦ Tp
  Infer = πᵈ

  Extend : (∫ Tp) ↦ (∫ Chk) 
  Extend = Extension .fst
  module Extend = Functor Extend

  Ext𝒞 : (∫ Tp) ↦ 𝒞
  Ext𝒞 = (πᶠ Tp ⊗ πᶠ Chk) ⊗ Extend

  


  Tm : Chk [ πᶠ Tp ]↦ Syn
  Tm = π̂

  TpFam : DFib[ ∫ Tp ]
  TpFam = Ext𝒞 ^*1 Tp

  ChkFam : DFib[ ∫ TpFam ]
  ChkFam = ∫ᶠ (π*1 Ext𝒞 Tp) ^*1 Chk


  module Tp = DFib-Ob Tp
  module Chk = DFib-Ob Chk
  module Syn = DFib-Ob Syn 

  module Syntax where

    Ctx : Type _
    Ctx = 𝒞.Ob

    Sub : Ctx → Ctx → Type _
    Sub = 𝒞.Hom

    instance
      Tp-Sub : Sub-notation Ctx Tp.Ob[_]
      Tp-Sub = sub-notation Sub λ A γ → γ Tp.^* A

      -- Tps.Hom[_] expresses the equational theory of subsitutions as functional relation
      Tp-Sub-Rel : Sub-Rel-notation Ctx Tp.Ob[_]
      Tp-Sub-Rel = sub-rel-notation Sub λ A γ B → Tp.Hom[ γ ] B A

      -- We have the same sort of substitution data on Chk and Syn
      Chk-sub : Sub-notation (Σ Ctx Tp.Ob[_]) Chk.Ob[_]
      Chk-sub .Sub-notation.lvl = _
      Chk-sub .Sub-notation.Subst (Γ , A) (Δ , B) = Σ[ γ ∈ Sub Γ Δ ] B [ γ ]≡ A
      Chk-sub .Sub-notation._[_] x (γ , p) = (∫hom γ p) Chk.^* x

      Chk-sub-rel : Sub-Rel-notation (Σ Ctx Tp.Ob[_]) Chk.Ob[_]
      Chk-sub-rel .Sub-Rel-notation.l1 = _
      Chk-sub-rel .Sub-Rel-notation.l2 = _
      Chk-sub-rel .Sub-Rel-notation.Subst (Γ , A) (Δ , B) = Σ[ γ ∈ Sub Γ Δ ] B [ γ ]≡ A
      Chk-sub-rel .Sub-Rel-notation._[_]≡_ x (γ , p) y = Chk.Hom[ (∫hom γ p) ] y x
      
      Syn-sub : Sub-notation Ctx Syn.Ob[_]
      Syn-sub .Sub-notation.lvl = _
      Syn-sub .Sub-notation.Subst = Sub
      Syn-sub .Sub-notation._[_] (α , e) σ = α [ σ ] , (e [ σ , Tp.π* σ α ])

      Syn-sub-rel : Sub-Rel-notation Ctx Syn.Ob[_]
      Syn-sub-rel .Sub-Rel-notation.l1 = _
      Syn-sub-rel .Sub-Rel-notation.l2 = _
      Syn-sub-rel .Sub-Rel-notation.Subst = Sub
      Syn-sub-rel .Sub-Rel-notation._[_]≡_ x γ y = Syn.Hom[ γ ] y x

    _⨾_ : (Γ : Ctx) → Tp ʻ Γ → Ctx
    Γ ⨾ A = Extend.₀ (Γ , A) .fst .fst

    wkₜ : ∀ {Γ} (A : Tp ʻ Γ) → Tp ʻ (Γ ⨾ A)
    wkₜ A = Extend.₀ (_ , A) .fst .snd

    var : ∀ {Γ} (A : Tp ʻ Γ) → Chk · (Γ ⨾ A , wkₜ A)
    var A = Extend.₀ (_ , _) .snd

    keep : ∀ {Γ Δ A B} (γ : Sub Γ Δ) → B [ γ ]≡ A → Sub (Γ ⨾ A) (Δ ⨾ B)
    keep γ p = Extend.₁ (∫hom _ p) .fst .fst

    keep-tp
      : ∀ {Γ Δ A B}
      → (γ : Sub Γ Δ)
      → (p : B [ γ ]≡ A)
      → (wkₜ B) [ keep γ p ]≡ (wkₜ A) 
    keep-tp γ p = Extend.₁ (∫hom γ p) .fst .snd 


    keep-chk
      : ∀ {Γ Δ A B}
      → (γ : Sub Γ Δ)
      → (p : B [ γ ]≡ A)
      → (var B) [ (keep γ p) , (keep-tp γ p) ]≡ (var A)
    keep-chk γ p = Extend.₁ (∫hom γ p) .snd


    keep-id : ∀ {Γ Δ} {A : Tp ʻ Δ} (γ : Sub Γ Δ) → Sub (Γ ⨾ (A [ γ ])) (Δ ⨾ A)
    keep-id γ = keep γ (Tp.π* _ _)

    tp-[] : ∀ {Γ Δ} {A : Tp ʻ Δ} {γ : Sub Γ Δ} → A [ γ ]≡ A [ γ ]
    tp-[] = Tp.π* _ _

    π : ∀ {Γ} {A : Tp ʻ Γ} → Sub (Γ ⨾ A) Γ
    π {Γ} {A} = counit.ε (Γ , A) .fst

    π-tp : ∀ {Γ} {A : Tp ʻ Γ} → A [ π ]≡ wkₜ A 
    π-tp {Γ} {A} = counit.ε (Γ , A) .snd

    inst : ∀ {Γ} {A : Tp ʻ Γ} (x : Chk ʻ (Γ , A)) → Sub Γ (Γ ⨾ A)
    inst {Γ = Γ} {A = A} x = unit.η ((Γ , A) , x) .fst .fst

    inst-tp : ∀ {Γ} {A : Tp ʻ Γ} (x : Chk ʻ (Γ , A)) → wkₜ A [ inst x ]≡ A 
    inst-tp {Γ = Γ} {A = A} x = unit.η ((Γ , A) , x) .fst .snd

    inst-chk
      : ∀ {Γ} {A : Tp ʻ Γ}
      → (x : Chk ʻ (Γ , A))
      → var A [ inst x , inst-tp x ]≡ x
    inst-chk {Γ = Γ} {A = A} x = unit.η ((Γ , A) , x) .snd

    
    huh : DFib[ ∫ Tp ]
    huh = (πᶠ Syn ⊗ ∫ᶠ Tm ⊗ Extend) ^*1 Syn


    foo : DFib[ ∫ Tp ]
    foo = (πᶠ Tp ⊗ πᶠ Chk ⊗ Extend) ^*1 Tp

    -- SubstTp : DFibΣ Chk (πᶠ Chk ^*1 TpFam) [ πᶠ Tp ]↦ Tp
    -- SubstTp .F₀' (x , B) = B [ inst x ]
    -- SubstTp .F₁' {a' = a'} {b' = b'} (γ , σ) = {!  !}
    -- SubstTp .F-id' = {!   !}
    -- SubstTp .F-∘' = {!   !}

    -- bar : (πᶠ Chk) ⇒ (πᶠ Chk F∘ Extend F∘ πᶠ Chk)
    -- bar = ((πᶠ Chk) ▶ unit) ∘ ρ→ _

    -- baz : (πᶠ Tp ⊗ πᶠ Chk) ⇒ (πᶠ Tp ⊗ πᶠ Chk) ⊗ Extend ⊗ πᶠ Chk
    -- baz = ((πᶠ Tp ⊗ πᶠ Chk) ▶ unit) ∘ ρ→ _
    
    -- SubstTp : (((πᶠ Tp ⊗ πᶠ Chk) ⊗ Extend ⊗ πᶠ Chk) ^*1 Tp) [ πᶠ Tp ⊗ πᶠ Chk ]↦ Tp
    -- SubstTp = _^*2_ {A' = ((πᶠ Tp ⊗ πᶠ Chk) ⊗ Extend ⊗ πᶠ Chk) ^*1 Tp } {B' = Tp} baz (π*1 _ Tp)

    -- subst-tp : ∀ {Γ} {A : Tp ʻ Γ} (B : Tp ʻ (Γ ⨾ A)) (x : Chk ʻ (Γ , A)) → Tp ʻ Γ
    -- subst-tp {Γ = Γ} {A = A} B x = SubstTp .F₀' {(Γ , A) , x} B

    -- subst-tp-path : ∀ {Γ} {A : Tp ʻ Γ} {B : Tp ʻ (Γ ⨾ A)} {x : Chk ʻ (Γ , A)} → B [ inst x ]≡ subst-tp B x
    -- subst-tp-path {B = B} {x = x} = Tp.^*-hom _ λ i → B [ 𝒞.idr (𝒞.idr (inst x) (~ i)) (~ i) ]

    -- SigmaData : DFib[ ∫ Chk ]
    -- SubstChk : ((πᶠ Chk F∘ Extend F∘ πᶠ Chk) ^*1 Chk) [ πᶠ Chk ]↦ Chk
    -- SubstChk = _^*2_ {A' = (πᶠ Chk F∘ Extend F∘ πᶠ Chk) ^*1 Chk} {B' = Chk} bar (π*1 _ Chk)

    -- SubstTp : ((πᶠ Chk F∘ Extend F∘ πᶠ Chk) ^*1 DFibConst Tp) [ πᶠ Chk ]↦ DFibConst Tp
    -- SubstTp = _^*2_ {A' = (πᶠ Chk F∘ Extend F∘ πᶠ Chk) ^*1 DFibConst Tp} {B' = DFibConst Tp} bar (π*1 _ (DFibConst Tp))

    _ = λ (Γ : Ctx) (A : Tp ʻ Γ) → {! (((πᶠ Tp ⊗ πᶠ Chk) ⊗ Extend ⊗ πᶠ Chk) ^*1 Tp) !}


record PiStructure {o ℓ} (C : CwF o ℓ) : Type (lsuc (o ⊔ ℓ)) where
  open CwF C
  open Syntax
  field
    Pi  : TpFam [ πᶠ Tp ]↦ Tp
    Lam : ChkFam [ ∫ᶠ Pi ]↦ Chk
    Lam* : 1-cell-cartesian (DFib o ℓ o ℓ) {A' = ChkFam} {B' = Chk} (∫ᶠ Pi) Lam

  module Pi = Displayed-functor Pi
  module Lam = Displayed-functor Lam
  module Lam* = 1-cell-cartesian Lam*

  Unlam : (∫ᶠ Pi ^*1 Chk) []↦ ChkFam
  Unlam = Lam*.universal¹' {U' = ∫ᶠ Pi ^*1 Chk} F∘-idr (π*1 (∫ᶠ Pi) Chk)
  module Unlam = Displayed-functor Unlam

  pi : ∀ {Γ} (A : Tp ʻ Γ) (B : Tp ʻ (Γ ⨾ A)) → Tp ʻ Γ
  pi A B = Pi.₀' B

  lam : ∀ {Γ} {A : Tp ʻ Γ} {B : Tp ʻ (Γ ⨾ A)} (x : Chk ʻ (Γ ⨾ A , B)) → Chk ʻ (Γ , pi A B)
  lam x = Lam.₀' x

  unlam : ∀ {Γ} {A : Tp ʻ Γ} {B : Tp ʻ (Γ ⨾ A)} (f : Chk ʻ (Γ , pi A B)) → Chk ʻ (Γ ⨾ A , B)
  unlam f = Unlam.₀' f

  -- lam-β : ∀ {Γ} {A : Tp ʻ Γ} {B : Tp ʻ (Γ ⨾ A)} {x : Chk ʻ (Γ ⨾ A , B)} → unlam (lam x) ≡ x
  -- lam-β {x = x} = apd (λ _ z → z .F₀' x) [λ].invr'

  -- lam-η : ∀ {Γ} {A : Tp ʻ Γ} {B : Tp ʻ (Γ ⨾ A)} {f : Chk ʻ (Γ , Π A B)} → lam (unlam f) ≡ f
  -- lam-η {f = f} = apd (λ _ z → z .F₀' f) [λ].invl'

  -- Π-[] : ∀ {Γ Δ} {γ : Sub Δ Γ} {A : Tp ʻ Γ} {B : Tp ʻ (Γ ⨾ A)} → Π A B [ γ ]≡ Π (A [ γ ]) (B [ keep-id γ ])
  -- Π-[] = Pi.₁' (Tp.π* _ _ , Tp.π* _ _)

  -- lam-[] : ∀ {Γ Δ} {γ : Sub Δ Γ} {A : Tp ʻ Γ} {B : Tp ʻ (Γ ⨾ A)} {x : Chk ʻ (Γ ⨾ A , B)} → lam x [ γ , Π-[] ]≡ lam (x [ keep-id γ , Tp.π* _ _ ])
  -- lam-[] = [λ].to' .F₁' (Chk.π* _ _)

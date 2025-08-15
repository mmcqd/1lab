open import Cat.Prelude
open import Cat.Reasoning
open import Cat.Functor.Adjoint
open import Cat.Displayed.Reasoning
open import Cat.Displayed.Base
open import Cat.Functor.Base
open import Cat.Displayed.Total hiding (∫ ; πᶠ) renaming (∫ᶠ to ∫ᶠ')
open import Cat.Displayed.Functor
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Cartesian.Discrete
open import Cat.Displayed.Cartesian.DFib
open import Cat.Displayed.Composition
open import Cat.Displayed.Instances.Pullback
open import Cat.Displayed.Instances.Product
open import Cat.Diagram.Terminal
open import Cat.Displayed.Instances.Lifting
open import Cat.Functor.Compose
open import Cat.Displayed.Comprehension
open import Cat.Displayed.Instances.Slice
open import Cat.Instances.Slice
open import Cat.Instances.Product
open import Cat.Instances.Functor

module CwF where


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

open Functor
open _=>_
open Displayed-functor

record CwF oc ℓc ot ℓt : Type (lsuc (oc ⊔ ℓc ⊔ ot ⊔ ℓt)) where
  open ∫Hom  

  -- Contexts are just a category
  field
    𝒞 : Precategory oc ℓc

  DFib𝒞 : Precategory _ _
  DFib𝒞 = DFib 𝒞 ot ℓt

  DFib𝒞/ : Displayed DFib𝒞 _ _
  DFib𝒞/ = DFib/ 𝒞 ot ℓt

  module 𝒞 = Cat.Reasoning 𝒞
  module DFib𝒞 = Cat.Reasoning DFib𝒞
  module DFib/ {o ℓ} {A : Precategory o ℓ} = Make-DFib/ A ot ℓt

  field
    Tp : DFib𝒞.Ob
    Chk : DFib/.Ob[ Tp ]

  Syn : DFib𝒞.Ob
  Syn = DFibΣ Tp Chk

  Infer : DFib𝒞.Hom Syn Tp
  Infer = hom πᵈ

  
  field
    ExtensionData : is-representable Tp Chk
 
  Extend : Functor (∫ Tp) (∫ Chk) 
  Extend = ExtensionData .fst

  Ext𝒞 : Functor (∫ Tp) 𝒞
  Ext𝒞 = (πᶠ Tp F∘ πᶠ Chk) F∘ Extend

  open _⊣_ (ExtensionData .snd) hiding (η ; ε) public

  module Tp = DFib-Ob Tp
  module Chk = DFib-Ob Chk
  module Syn = DFib-Ob Syn 
  module Extend = Functor Extend
  
  Tp/ : DFib/.Ob[ Tp ]
  Tp/ = (Ext𝒞 DFib^*) · Tp

  -- In Uemura's paper, (A ≡ SynData) and (B ≡ TpData)
  TpFam : DFib𝒞.Ob
  TpFam = DFibΣ Tp Tp/


  πTp : DFib𝒞.Hom TpFam Tp
  πTp = hom πᵈ

  ChkFam : DFib/.Ob[ TpFam ]
  ChkFam = ((∫ᶠ' (Change-of-base-functor Ext𝒞 (Tp .fst)) F∘ Shift) DFib^*) · Chk

  unit^* : (Extend F∘ πᶠ Chk) DFib^* => Id
  unit^* = id^* ot ℓt .to ∘nt ^*-natural unit 

  counit^* : Id => (πᶠ Chk F∘ Extend) DFib^*
  counit^* = ^*-natural counit ∘nt id^* ot ℓt .from

  unit-Ext𝒞 : (πᶠ Tp F∘ πᶠ Chk) => Ext𝒞 F∘ πᶠ Chk
  unit-Ext𝒞 = NT (λ x → 𝒞.id) (λ _ _ _ → 𝒞.id-comm-sym) ∘nt ((πᶠ Tp F∘ πᶠ Chk) ▸ unit) ∘nt NT (λ x → 𝒞.id) (λ _ _ _ → 𝒞.id-comm-sym)

  unit-Ext𝒞^* : (Ext𝒞 F∘ πᶠ Chk) DFib^* => (πᶠ Tp F∘ πᶠ Chk) DFib^*
  unit-Ext𝒞^* = ^*-natural {o' = ot} {ℓ' = ℓt} unit-Ext𝒞



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

  open Syntax
  -- unit-Ext𝒞^* .η Tp
  foo : Functor _ _
  foo .F₀ ((Γ , A , B) , x) = (Γ , B [ inst x ]) --unit-Ext𝒞^* .η Tp .F₀' {x = (Γ , A) , x} B)
  foo .F₁ (∫hom (∫hom γ γ') γ'') = ∫hom γ {!   !}
  foo .F-id = {!   !}
  foo .F-∘ = {!   !}

  ChkPair : DFib/.Ob[ TpFam ]
  ChkPair = DFibΣ (πTp DFib/.^* Chk) ((foo DFib^*) · Chk)

  TpΛ : Type _
  TpΛ = DFib𝒞.Hom TpFam Tp 

  ChkΛ : TpΛ → Type _
  ChkΛ Λ = Cartesian-morphism (DFib/ 𝒞 ot ℓt) Λ ChkFam Chk

 


record PiStructure {oc ℓc ot ℓt} (C : CwF oc ℓc ot ℓt) : Type (lsuc (ot ⊔ ℓt) ⊔ oc ⊔ ℓc) where
  open CwF C
  open Syntax
  field
    Pi : TpΛ
    Lam : ChkΛ Pi

  module Pi = DFib-functor Pi
  module LamData = Cartesian-morphism Lam

 -- The fibration of terms with Pi types
  ChkPi : DFib/.Ob[ TpFam ]
  ChkPi = Pi DFib/.^* Chk

  [λ] : ChkFam DFib/.≅↓ ChkPi 
  [λ] = cartesian-domain-unique _ LamData.cartesian DFib/.π*.cartesian

  module [λ] = DFib/._≅[_]_ [λ] 

  Π : ∀ {Γ} (A : Tp ʻ Γ) (B : Tp ʻ (Γ ⨾ A)) → Tp ʻ Γ
  Π A B = Pi.₀' (A , B)

  lam : ∀ {Γ} {A : Tp ʻ Γ} {B : Tp ʻ (Γ ⨾ A)} (x : Chk ʻ (Γ ⨾ A , B)) → Chk ʻ (Γ , Π A B)
  lam x = [λ].to' .F₀' x

  unlam : ∀ {Γ} {A : Tp ʻ Γ} {B : Tp ʻ (Γ ⨾ A)} (f : Chk ʻ (Γ , Π A B)) → Chk ʻ (Γ ⨾ A , B)
  unlam f = [λ].from' .F₀' f

  lam-β : ∀ {Γ} {A : Tp ʻ Γ} {B : Tp ʻ (Γ ⨾ A)} {x : Chk ʻ (Γ ⨾ A , B)} → unlam (lam x) ≡ x
  lam-β {x = x} = apd (λ _ z → z .F₀' x) [λ].invr'

  lam-η : ∀ {Γ} {A : Tp ʻ Γ} {B : Tp ʻ (Γ ⨾ A)} {f : Chk ʻ (Γ , Π A B)} → lam (unlam f) ≡ f
  lam-η {f = f} = apd (λ _ z → z .F₀' f) [λ].invl'

  Π-[] : ∀ {Γ Δ} {γ : Sub Δ Γ} {A : Tp ʻ Γ} {B : Tp ʻ (Γ ⨾ A)} → Π A B [ γ ]≡ Π (A [ γ ]) (B [ keep-id γ ])
  Π-[] = Pi.₁' (Tp.π* _ _ , Tp.π* _ _)

  lam-[] : ∀ {Γ Δ} {γ : Sub Δ Γ} {A : Tp ʻ Γ} {B : Tp ʻ (Γ ⨾ A)} {x : Chk ʻ (Γ ⨾ A , B)} → lam x [ γ , Π-[] ]≡ lam (x [ keep-id γ , Tp.π* _ _ ])
  lam-[] = [λ].to' .F₁' (Chk.π* _ _)


-- record SigmaStructure {oc ℓc ot ℓt} (C : CwF oc ℓc ot ℓt) : Type (lsuc (ot ⊔ ℓt) ⊔ oc ⊔ ℓc) where
--   open CwF C
--   open Syntax
--   field
--     Sigma : TpΛ
--     Pair : DFib𝒞/.Hom[ {!   !} ] {!   !} {!   !}
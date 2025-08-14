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
  module DFib𝒞⊤ = Terminal (DFib-terminal 𝒞 ot ℓt)
  module DFib𝒞/ = DFib/ 𝒞 ot ℓt

  field
    Tp : DFib𝒞.Ob
    Chk : DFib𝒞/.Ob[ Tp ]

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

  -- P : ∀ {A : DFib𝒞.Ob} {B} → Functor (∫ A) B → Functor {! ∫ A   !} {!   !}
  -- P f .F₀ x = {!   !}
  -- P f .F₁ = {!   !}
  -- P f .F-id = {!   !}
  -- P f .F-∘ = {!   !} 
    -- DFibΣ {!   !} ((f DFib^*) · {!   !})

  -- DFibΠ : DFib𝒞.Ob → DFib𝒞/.Ob[ Tp ]
  -- DFibΠ x = (Ext𝒞 DFib^*) · x

  -- In Uemura's paper, (A ≡ SynData) and (B ≡ TpData)
  TpFam : DFib𝒞.Ob
  TpFam = DFibΣ Tp ((Ext𝒞 DFib^*) · Tp)


  πTp : DFib𝒞.Hom TpFam Tp 
  πTp = hom πᵈ

  ChkFam : DFib𝒞/.Ob[ TpFam ]
  ChkFam = ((∫ᶠ' (Change-of-base-functor Ext𝒞 (Tp .fst)) F∘ Shift) DFib^*) · Chk

  TpΛ : Type _
  TpΛ = DFib𝒞.Hom TpFam Tp 

  ChkΛ : TpΛ → Type _
  ChkΛ Λ = Cartesian-morphism (DFib/ 𝒞 ot ℓt) Λ ChkFam Chk 

  module Tp = DFib-Ob Tp
  module Chk = DFib-Ob Chk
  module Syn = DFib-Ob Syn 
  module Extend = Functor Extend
  
  open _⊣_ (ExtensionData .snd) hiding (η ; ε) public




  unit^* : (Extend F∘ πᶠ Chk) DFib^* => Id
  unit^* = id^* ot ℓt .to ∘nt Base-change .F₁ unit

  counit^* : Id => (πᶠ Chk F∘ Extend) DFib^*
  counit^* = (Base-change .F₁ counit) ∘nt id^* ot ℓt .from


  -- InstTp : DFib-functor Id _ _  -- DFib𝒞.Hom TpFamArg Tp
  -- InstTp = Base-change .F₁ ((πᶠ Tp F∘ πᶠ Chk) ▸ unit) .η Tp

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


    -- Comprehend : Vertical-functor (Syn .fst) (Slices 𝒞)
    -- Comprehend .F₀' {Γ} (A , x) = cut {domain = Γ ⨾ A} π
    -- Comprehend .F₁' (γ , γ') = slice-hom (keep _ γ) (sym $ ap fst $ counit.is-natural _ _ _)
    -- Comprehend .F-id' = Slice-path _ (ap (fst ⊙ fst) $ Extend .F-id)
    -- Comprehend .F-∘' = Slice-path _ (ap (fst ⊙ fst) $ Extend .F-∘ _ _)

    -- ComprehendTp : Vertical-functor (Tp .fst) (Slices 𝒞)
    -- ComprehendTp .F₀' {Γ} A = cut {domain = Γ ⨾ A} π
    -- ComprehendTp .F₁' {a} {b} {f} {a'} {b'} γ = slice-hom (keep _ γ) (sym $ ap fst $ counit.is-natural (a , a') (b , b') (∫hom f γ))
    -- ComprehendTp .F-id' = Slice-path _ (ap (fst ⊙ fst) $ Extend .F-id)
    -- ComprehendTp .F-∘' = Slice-path _ (ap (fst ⊙ fst) $ Extend .F-∘ _ _)

    -- ComprehendChk : Vertical-functor (Chk .fst) (Slices (∫ Tp))
    -- ComprehendChk .F₀' {Γ , A} x = cut (∫hom π π-tp)
    -- ComprehendChk .F₁' {f = ∫hom f f'} γ = slice-hom (∫hom (keep f f') (keep-tp f f')) (sym $ counit.is-natural _ _ _)
    -- ComprehendChk .F-id' = Slice-path _ (ap fst $ Extend .F-id)
    -- ComprehendChk .F-∘' = Slice-path _ (ap fst $ Extend .F-∘ _ _)



record PiStructure {oc ℓc ot ℓt} (C : CwF oc ℓc ot ℓt) : Type (lsuc (ot ⊔ ℓt) ⊔ oc ⊔ ℓc) where
  open CwF C
  open Syntax
  field
    Pi : TpΛ
    LamData : ChkΛ Pi

  Lam : DFib𝒞/.Hom[ Pi ] ChkFam Chk
  Lam = LamData .Cartesian-morphism.hom'


  module Pi = DFib-functor Pi
  module Lam where
    open DFib-functor Lam public
    open Cartesian-morphism LamData public
  
  
  open Displayed-functor
  open Functor
  -- open _=>_


  -- The fibration of terms with Pi types
  ChkPi : DFib𝒞/.Ob[ TpFam ]
  ChkPi = Pi DFib𝒞/.^* Chk

  -- Embedding of Pi terms in to terms
  EmbedPi : DFib𝒞/.Hom[ Pi ] ChkPi Chk
  EmbedPi = DFib𝒞/.π* Pi Chk

  -- Turn a Pi term back into a term family
  Unlam : DFib𝒞/.Hom[ DFib𝒞.id {TpFam} ] ChkPi ChkFam
  Unlam = Lam.universalv EmbedPi


  -- lam (unlam x) ≡ x
  Lam-η : (DFib𝒞/._∘'_ {a = TpFam} {b = TpFam} {c = Tp} Lam Unlam) DFib𝒞/.≡[ DFib𝒞.idr Pi ] EmbedPi
  Lam-η = Lam.commutesv EmbedPi


  -- The fibration of type families and arguments to subsitute
  TpFamArg : DFib𝒞.Ob
  TpFamArg = DFibΣ TpFam (πTp DFib𝒞/.^* Chk)

  InstTp : DFib𝒞.Hom TpFamArg Tp
  InstTp .fun .F₀' {Γ} ((A , B) , x) = B [ inst x ]
    -- Base-change .F₁ unit .η (((πᶠ Tp F∘ πᶠ Chk) DFib^*) · Tp) .F₀' B 
  InstTp .fun .F₁' ((γ , γ') , σ) = Base-change .F₁ unit .η (((πᶠ Tp F∘ πᶠ Chk) DFib^*) · Tp) .F₁' {f = ∫hom _ σ} γ'
  InstTp .fun .F-id' = is-prop→pathp (λ _ → hlevel 1) _ _
  InstTp .fun .F-∘' = is-prop→pathp (λ _ → hlevel 1) _ _

  -- The fibration of terms with Pi types and an argument
  ChkApp : DFib𝒞/.Ob[ TpFam ]
  ChkApp = ChkPi DFib× (πTp DFib𝒞/.^* Chk)

  Inst : DFib𝒞/.Hom[ InstTp ] {!   !} Chk
  Inst = {!   !}


--  unit^* .η (((πᶠ Tp F∘ πᶠ Chk) DFib^*) · Tp)



  -- Base-change .F₁ ? .η ?


  -- FamArg : DFib𝒞.Ob
  -- FamArg = DFibΣ TpFam (ChkFam DFib× (πTp DFib𝒞/.^* Chk))



  -- Inst : DFib𝒞.Hom TpFam Tp
  -- Inst = {!   !}

  -- Lam-β : Functor (∫ ChkApp) (∫ Chk)
  -- Lam-β .F₀ ((Γ , A , B) , (f , x)) = {!   !} , {!   !}
  -- Lam-β .F₁ = {!   !}
  -- Lam-β .F-id = {!   !}
  -- Lam-β .F-∘ = {!   !}

  -- Π : ∀ {Γ} (A : Tp Γ) (B : Tp (Γ ⨾ A)) → Tp Γ
  -- Π A B = Pi.₀' (A , B)

  -- lam : ∀ {Γ} {A : Tp Γ} {B : Tp (Γ ⨾ A)} → Chk (Γ ⨾ A) B → Chk Γ (Π A B)
  -- lam x = Lam.₀' x


  -- module Unlam = DFib-functor Unlam

  -- unlam : ∀ {Γ} {A : Tp Γ} {B : Tp (Γ ⨾ A)} (f : Chk Γ (Π A B)) → Chk (Γ ⨾ A) B
  -- unlam f = Unlam.₀' f


  -- lam-η : ∀ {Γ} {A : Tp Γ} {B : Tp (Γ ⨾ A)} {f : Chk Γ (Π A B)} → lam (unlam f) ≡ f
  -- lam-η {f = f} = apd (λ i (hom z) → z .F₀' f) Lam-η

  

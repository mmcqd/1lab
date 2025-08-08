open import Cat.Prelude
open import Cat.Reasoning
open import Cat.Functor.Adjoint
open import Cat.Displayed.Reasoning
open import Cat.Displayed.Base
open import Cat.Displayed.Total
open import Cat.Displayed.Functor
open import Cat.Displayed.Cartesian.Discrete
open import Cat.Displayed.Cartesian.DCF
open import Cat.Displayed.Composition
open import Cat.Displayed.Instances.Pullback



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

record CwF o ℓ : Type (lsuc (o ⊔ ℓ)) where
  
  -- Contexts are just a category
  field
    Ctxs : Precategory o ℓ
{-
  module Ctxs = Cat.Reasoning Ctxs
  module CtxFib = Cat.Reasoning (DCF Ctxs o ℓ)
  module ΣCtx = Poly Ctxs o ℓ o ℓ
  
  field
    TpsFib : CtxFib.Ob
    TmsFib : ΣCtx.Ob[ TpsFib ]

  -- module Tps = DCF TpsFib
  -- Tps = TpsFib .fst

  -- module Tms = DCF TmsFib
  -- Tms = TmsFib .fst

  module ΣTps = Poly (∫ Tps) o ℓ o ℓ
  module ΣTms = Poly (∫ Tms) o ℓ o ℓ

  field
    Extend : Functor (∫ Tps) (∫ Tms)
    π⊣Extend :  πᶠ Tms ⊣ Extend

  module Extend = Functor Extend


  SynsFib : CtxFib.Ob
  SynsFib = Tps D∘ Tms , discrete-∘ (TpsFib .snd)  (TmsFib .snd)

  Syns : Displayed Ctxs _ _
  Syns = SynsFib .fst

  module Syns = DCF SynsFib

  Infer : CtxFib.Hom SynsFib TpsFib
  Infer = πᵈ

  ExtCtx : Functor (∫ Tps) Ctxs
  ExtCtx = πᶠ Tps F∘ πᶠ Tms F∘ Extend



  TpFam : CtxFib.Ob
  TpFam = (Tps D∘ Change-of-base ExtCtx Tps) , discrete-∘ (TpsFib .snd) (Change-of-base-discrete-fibration _ _ (TpsFib .snd))


  -- ChkFam : CtxPoly.Ob[ TpFam ]
  -- ChkFam = (Change-of-base (Collapse ExtCtx) Tms) , (Change-of-base-discrete-fibration _ _ (TmsFib .snd))


  -- TpAbs : Type _
  -- TpAbs = CtxFib.Hom TpFam TpsFib

  -- ChkAbs : TpAbs → Type _
  -- ChkAbs Con = CtxPoly.Hom[ Con ] ChkFam TmsFib

  module Syntax where
    open _⊣_ π⊣Extend
    open ∫Hom

    Ctx : Type _
    Ctx = Ctxs.Ob

    Sub : Ctx → Ctx → Type _
    Sub = Ctxs.Hom

    Tp : Ctx → Type _
    Tp Γ = Tps.Ob[ Γ ]

    instance
      Tp-Sub : Sub-notation Ctx Tp
      Tp-Sub = sub-notation Sub λ A γ → γ Tps.^* A

      -- Tps.Hom[_] expresses the equational theory of subsitutions as functional relation
      Tp-Sub-Rel : Sub-Rel-notation Ctx Tp
      Tp-Sub-Rel = sub-rel-notation Sub λ A γ B → Tps.Hom[ γ ] B A



    tp-hom≃path : ∀ {Γ Δ} {A : Tp Δ} {B : Tp Γ} {γ : Sub Γ Δ} → (A [ γ ] ≡ B) ≃ (A [ γ ]≡ B)
    tp-hom≃path = Tps.^*-hom _ , Tps.^*-hom-is-equiv _

    tp-[] : ∀ {Γ Δ} {A : Tp Δ} {γ : Sub Γ Δ} → A [ γ ]≡ A [ γ ]
    tp-[] = Tps.π* _ _


    Chk : (Γ : Ctx) → Tp Γ → Type _
    Chk Γ A = Tms.Ob[ Γ , A ]

    -- We have the same sort of substitution data on Chk
    instance
      Chk-sub : Sub-notation (Σ Ctx Tp) λ (Γ , A) → Chk Γ A
      Chk-sub .Sub-notation.lvl = _
      Chk-sub .Sub-notation.Subst (Γ , A) (Δ , B) = Σ[ γ ∈ Sub Γ Δ ] B [ γ ]≡ A
      Chk-sub .Sub-notation._[_] x (γ , p) = (∫hom γ p) Tms.^* x

      Chk-sub-rel : Sub-Rel-notation (Σ Ctx Tp) λ (Γ , A) → Chk Γ A
      Chk-sub-rel .Sub-Rel-notation.l1 = _
      Chk-sub-rel .Sub-Rel-notation.l2 = _
      Chk-sub-rel .Sub-Rel-notation.Subst (Γ , A) (Δ , B) = Σ[ γ ∈ Sub Γ Δ ] B [ γ ]≡ A
      Chk-sub-rel .Sub-Rel-notation._[_]≡_ x (γ , p) y = Tms.Hom[ (∫hom γ p) ] y x

    Syn : Ctx → Type _
    Syn Γ = Syns.Ob[ Γ ]

    instance
      Syn-sub : Sub-notation Ctx Syn
      Syn-sub .Sub-notation.lvl = _
      Syn-sub .Sub-notation.Subst = Sub
      Syn-sub .Sub-notation._[_] (α , e) σ = α [ σ ] , (e [ σ , Tps.π* σ α ])

      Syn-sub-rel : Sub-Rel-notation Ctx Syn
      Syn-sub-rel .Sub-Rel-notation.l1 = _
      Syn-sub-rel .Sub-Rel-notation.l2 = _
      Syn-sub-rel .Sub-Rel-notation.Subst = Sub
      Syn-sub-rel .Sub-Rel-notation._[_]≡_ x γ y = Syns.Hom[ γ ] y x


    _⨾_ : (Γ : Ctx) → Tp Γ → Ctx
    Γ ⨾ A = Extend.₀ (Γ , A) .fst .fst

    wkₜ : ∀ {Γ} (A : Tp Γ) → Tp (Γ ⨾ A)
    wkₜ A = Extend.₀ (_ , A) .fst .snd

    var : ∀ {Γ} (A : Tp Γ) → Chk (Γ ⨾ A) (wkₜ A)
    var A = Extend.₀ (_ , _) .snd

    keep : ∀ {Γ Δ A B} (γ : Sub Γ Δ) → B [ γ ]≡ A → Sub (Γ ⨾ A) (Δ ⨾ B)
    keep γ p = Extend.₁ (∫hom _ p) .fst .fst

    keep-id : ∀ {Γ Δ} {A : Tp Δ} (γ : Sub Γ Δ) → Sub (Γ ⨾ (A [ γ ])) (Δ ⨾ A)
    keep-id γ = keep γ (Tps.π* _ _)


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


    inst : ∀ {Γ} {A : Tp Γ} (x : Chk Γ A) → Sub Γ (Γ ⨾ A)
    inst {Γ = Γ} {A = A} x = unit.η ((Γ , A) , x) .fst .fst

    inst-tp : ∀ {Γ} {A : Tp Γ} (x : Chk Γ A) → wkₜ A [ inst x ]≡ A 
    inst-tp {Γ = Γ} {A = A} x = unit.η ((Γ , A) , x) .fst .snd

    inst-chk
      : ∀ {Γ} {A : Tp Γ}
      → (x : Chk Γ A)
      → var A [ inst x , inst-tp x ]≡ x
    inst-chk {Γ = Γ} {A = A} x = unit.η ((Γ , A) , x) .snd

    π : ∀ {Γ} {A : Tp Γ} → Sub (Γ ⨾ A) Γ
    π {Γ} {A} = counit.ε (Γ , A) .fst

    π-tp : ∀ {Γ} {A : Tp Γ} → A [ π ]≡ wkₜ A 
    π-tp {Γ} {A} = counit.ε (Γ , A) .snd

-}

-- record CwF oc hc otp htp otm htm : Type (lsuc (oc ⊔ hc ⊔ otm ⊔ htm ⊔ otp ⊔ htp)) where
--   field
--     Ctxs : Precategory oc hc

--   module Ctxs = Cat.Reasoning Ctxs
  
--   field
--     Tps : Displayed Ctxs otp htp
--     Tps* : is-discrete-cartesian-fibration Tps

--     Tms : Displayed (∫ Tps) otm htm
--     Tms* : is-discrete-cartesian-fibration Tms


--     Extend : Functor (∫ Tps) (∫ Tms)
--     π⊣Extend :  πᶠ Tms ⊣ Extend

--   -- πᶠ Tms : Functor (∫ Tms) (∫ Tps) is our representable map of discrete fibrations
  
--   module Extend = Functor Extend

--   module Tps where
--     open Displayed Tps public
--     open Cat.Displayed.Reasoning Tps public
--     open is-discrete-cartesian-fibration Tps* public

--   module Tms where
--     open Displayed Tms public
--     open Cat.Displayed.Reasoning Tms public
--     open is-discrete-cartesian-fibration Tms* public

--   open _⊣_ π⊣Extend
--   open ∫Hom

--   Ctx : Type oc
--   Ctx = Ctxs.Ob

--   Sub : Ctx → Ctx → Type hc
--   Sub = Ctxs.Hom

--   Tp : Ctx → Type otp
--   Tp Γ = Tps.Ob[ Γ ]

--   instance
--     Tp-Sub : Sub-notation Ctx Tp
--     Tp-Sub = sub-notation Sub λ A γ → γ Tps.^* A

--     -- Tps.Hom[_] expresses the equational theory of subsitutions as functional relation
--     Tp-Sub-Rel : Sub-Rel-notation Ctx Tp
--     Tp-Sub-Rel = sub-rel-notation Sub λ A γ B → Tps.Hom[ γ ] B A



--   -- tp-hom≃path : ∀ {Γ Δ} {A : Tp Δ} {B : Tp Γ} {γ : Sub Γ Δ} → (A [ γ ] ≡ B) ≃ (A [ γ ]≡ B)
--   -- tp-hom≃path = Tps*.^*-hom _ , Tps*.^*-hom-is-equiv _

--   tp-[] : ∀ {Γ Δ} {A : Tp Δ} {γ : Sub Γ Δ} → A [ γ ]≡ A [ γ ]
--   tp-[] = Tps.π* _ _

--   -- -- We have the expected functor laws

--   -- []-id : ∀ {Γ} {A : Tp Γ} → A [ Ctxs.id ]≡ A
--   -- []-id = Tps.id'

--   -- []-∘ : ∀ {Γ Δ Ξ} {γ : Sub Γ Δ} {σ : Sub Δ Ξ} {A : Tp Ξ} → A [ σ Ctxs.∘ γ ]≡ A [ σ ] [ γ ]
--   -- []-∘ {γ = γ} {σ = σ} {A = A} = tp-[] Tps.∘' tp-[]


--   Chk : (Γ : Ctx) → Tp Γ → Type otm
--   Chk Γ A = Tms.Ob[ Γ , A ]

--   -- We have the same sort of substitution data on Chk
--   instance
--     Chk-sub : Sub-notation (Σ Ctx Tp) λ (Γ , A) → Chk Γ A
--     Chk-sub .Sub-notation.lvl = _
--     Chk-sub .Sub-notation.Subst (Γ , A) (Δ , B) = Σ[ γ ∈ Sub Γ Δ ] B [ γ ]≡ A
--     Chk-sub .Sub-notation._[_] x (γ , p) = (∫hom γ p) Tms.^* x

--     Chk-sub-rel : Sub-Rel-notation (Σ Ctx Tp) λ (Γ , A) → Chk Γ A
--     Chk-sub-rel .Sub-Rel-notation.l1 = _
--     Chk-sub-rel .Sub-Rel-notation.l2 = _
--     Chk-sub-rel .Sub-Rel-notation.Subst (Γ , A) (Δ , B) = Σ[ γ ∈ Sub Γ Δ ] B [ γ ]≡ A
--     Chk-sub-rel .Sub-Rel-notation._[_]≡_ x (γ , p) y = Tms.Hom[ (∫hom γ p) ] y x

--   Syns : Displayed Ctxs _ _
--   Syns = Tps D∘ Tms

--   Syns* : is-discrete-cartesian-fibration Syns
--   Syns* = discrete-∘ Tps* Tms*

--   module Syns where
--     open Displayed Syns public
--     open Cat.Displayed.Reasoning Syns public
--     open is-discrete-cartesian-fibration Syns* public

--   Syn : Ctx → Type (otp ⊔ otm)
--   Syn Γ = Syns.Ob[ Γ ]

--   instance
--     Syn-sub : Sub-notation Ctx Syn
--     Syn-sub .Sub-notation.lvl = _
--     Syn-sub .Sub-notation.Subst = Sub
--     Syn-sub .Sub-notation._[_] (α , e) σ = α [ σ ] , (e [ σ , Tps.π* σ α ])

--     Syn-sub-rel : Sub-Rel-notation Ctx Syn
--     Syn-sub-rel .Sub-Rel-notation.l1 = hc
--     Syn-sub-rel .Sub-Rel-notation.l2 = htp ⊔ htm
--     Syn-sub-rel .Sub-Rel-notation.Subst = Sub
--     Syn-sub-rel .Sub-Rel-notation._[_]≡_ x γ y = Syns.Hom[ γ ] y x


--   Infer : Vertical-functor Syns Tps 
--   Infer = πᵈ

--   _⨾_ : (Γ : Ctx) → Tp Γ → Ctx
--   Γ ⨾ A = Extend.₀ (Γ , A) .fst .fst

--   wkₜ : ∀ {Γ} (A : Tp Γ) → Tp (Γ ⨾ A)
--   wkₜ A = Extend.₀ (_ , A) .fst .snd

--   var : ∀ {Γ} (A : Tp Γ) → Chk (Γ ⨾ A) (wkₜ A)
--   var A = Extend.₀ (_ , _) .snd

--   keep : ∀ {Γ Δ A B} (γ : Sub Γ Δ) → B [ γ ]≡ A → Sub (Γ ⨾ A) (Δ ⨾ B)
--   keep γ p = Extend.₁ (∫hom _ p) .fst .fst

--   keep-id : ∀ {Γ Δ} {A : Tp Δ} (γ : Sub Γ Δ) → Sub (Γ ⨾ (A [ γ ])) (Δ ⨾ A)
--   keep-id γ = keep γ (Tps.π* _ _)


--   keep-tp
--     : ∀ {Γ Δ A B}
--     → (γ : Sub Γ Δ)
--     → (p : B [ γ ]≡ A)
--     → (wkₜ B) [ keep γ p ]≡ (wkₜ A) 
--   keep-tp γ p = Extend.₁ (∫hom γ p) .fst .snd 

--   keep-chk
--     : ∀ {Γ Δ A B}
--     → (γ : Sub Γ Δ)
--     → (p : B [ γ ]≡ A)
--     → (var B) [ (keep γ p) , (keep-tp γ p) ]≡ (var A)
--   keep-chk γ p = Extend.₁ (∫hom γ p) .snd


--   inst : ∀ {Γ} {A : Tp Γ} (x : Chk Γ A) → Sub Γ (Γ ⨾ A)
--   inst {Γ = Γ} {A = A} x = unit.η ((Γ , A) , x) .fst .fst

--   inst-tp : ∀ {Γ} {A : Tp Γ} (x : Chk Γ A) → wkₜ A [ inst x ]≡ A 
--   inst-tp {Γ = Γ} {A = A} x = unit.η ((Γ , A) , x) .fst .snd

--   inst-chk
--     : ∀ {Γ} {A : Tp Γ}
--     → (x : Chk Γ A)
--     → var A [ inst x , inst-tp x ]≡ x
--   inst-chk {Γ = Γ} {A = A} x = unit.η ((Γ , A) , x) .snd

--   π : ∀ {Γ} {A : Tp Γ} → Sub (Γ ⨾ A) Γ
--   π {Γ} {A} = counit.ε (Γ , A) .fst

--   π-tp : ∀ {Γ} {A : Tp Γ} → A [ π ]≡ wkₜ A 
--   π-tp {Γ} {A} = counit.ε (Γ , A) .snd

--   ExtCtx : Functor (∫ Tps) Ctxs
--   ExtCtx = πᶠ Tps F∘ πᶠ Tms F∘ Extend

--   -- The discrete fibration of type families
--   -- The object set over Γ is Σ[ A ∈ Tp Γ ] Tp (Γ ⨾ A)
--   TpFam : Displayed Ctxs  _ _
--   TpFam = Tps D∘ Change-of-base ExtCtx Tps

--   TpFam* : is-discrete-cartesian-fibration TpFam
--   TpFam* = discrete-∘ Tps* (Change-of-base-discrete-fibration _ Tps Tps*)

--   module TpFam where
--     open Displayed TpFam public
--     open is-discrete-cartesian-fibration TpFam* public

--   -- The discrete fibration of term families
--   -- The object set over (Γ , (A , B)) is Chk (Γ ⨾ A) B
--   ChkFam : Displayed (∫ TpFam) _ _
--   ChkFam = Change-of-base (Collapse ExtCtx) Tms

--   ChkFam* : is-discrete-cartesian-fibration ChkFam
--   ChkFam* = Change-of-base-discrete-fibration _ Tms Tms*

--   module ChkFam where
--     open Displayed ChkFam public
--     open is-discrete-cartesian-fibration ChkFam* public

--   SynFam : Displayed Ctxs _ _
--   SynFam = TpFam D∘ ChkFam

--   SynFam* : is-discrete-cartesian-fibration SynFam
--   SynFam* = discrete-∘ TpFam* ChkFam*

--   module SynFam where
--     open Displayed SynFam public
--     open is-discrete-cartesian-fibration SynFam* public

--   InferFam : Vertical-functor SynFam TpFam
--   InferFam = πᵈ


--   TpAbs : Type _
--   TpAbs = Vertical-functor TpFam Tps

--   module StrictD  {c d} = Precategory (StrictD Ctxs c d)
--   module FamS {c d e f} where
--     open Displayed (FamS Ctxs c d e f) public
--     open Cartesian-fibration (FamS Ctxs c d e f) FamS-cartesian public


--   -- ChkAbs : TpAbs → Type _
--   -- ChkAbs Con = 
--   --   -- FamS.Cartesian-morphism 
--   --   --   {x = _ , λ _ → hlevel 2} {y = _ , λ _ → hlevel 2} 
--   --   -- Con (ChkFam , λ _ → hlevel 2) (Tms , λ _ → hlevel 2)

  
--   -- Forget : Displayed (∫ SynFam) _ _
--   -- Forget = Change-of-base ((Collapse ExtCtx) F∘ F∫ πᵈ) Tms


-- record PiStructure (C : CwF lzero lzero lzero lzero lzero lzero) : Type (lsuc lzero) where
--   open CwF C
--   field
--     Pi : Vertical-functor TpFam Tps
--     Lam : Displayed-functor (F∫ Pi) ChkFam Tms

--   Lam : FamS.Hom[_] {x = TpFam ₛ} Pi (Pi FamS.^* (Tms ₛ)) (Tms ₛ)
--   Lam = {!   !}
--     -- FamS.π* {x = {!   !} , hlevel 2} {y = {!   !} , hlevel 2} {!   !} ({!   !} , hlevel 2)
  
  
--   module Pi = Vertical-functor Pi
--   module Lam where
--     -- open is-cartesian {! FamS.π*.cartesian  !} public
--     -- open Displayed-functor Lam public
  
--   open Displayed-functor


--   Π : ∀ {Γ} (A : Tp Γ) (B : Tp (Γ ⨾ A)) → Tp Γ
--   Π A B = Pi.₀' (A , B)

--   -- lam : ∀ {Γ} {A : Tp Γ} {B : Tp (Γ ⨾ A)} → Chk (Γ ⨾ A) B → Chk Γ (Π A B)
--   -- lam x = Lam.₀' x

--   -- Unlam : Displayed-functor (F∫ Id') (Change-of-base (F∫ Pi) Tms) ChkFam
--   -- Unlam = Lam.universalv {a'' = _ , λ _ → hlevel 2} (Change-of-base-functor (F∫ Pi) Tms)

--   -- module Unlam = Displayed-functor Unlam

--   -- unlam : ∀ {Γ} {A : Tp Γ} {B : Tp (Γ ⨾ A)} (f : Chk Γ (Π A B)) → Chk (Γ ⨾ A) B
--   -- unlam f = Unlam.₀' f

--   -- Unlam-β : (f : Displayed-functor (F∫ StrictD.id) (Change-of-base (F∫ Pi) Tms) ChkFam) → {! w  !}
--   -- Unlam-β f = Lam.uniquev f {!   !}




--   -- unlam-β : ∀ {Γ} {A : Tp Γ} {B : Tp (Γ ⨾ A)} {f : Chk (Γ ⨾ A) B} → unlam (lam f) ≡ f
--   -- unlam-β {Γ} {A} {B} {f} = 
--   --   unlam (lam f) ≡˘⟨ ap (λ z → z .F₀' (lam f)) (Lam.uniquev {!   !} {!   !}) ⟩
--   --   f ∎ 
--   --   where 
--   --     F : Displayed-functor (F∫ Id') (Change-of-base (F∫ Pi) Tms) (Change-of-base (Collapse ExtCtx) Tms)
--   --     F .F₀' {x = Γ , (A , B)} f = {!   !}
--   --     F .F₁' = {!   !}
--   --     F .F-id' = {!   !}
--   --     F .F-∘' = {!   !}
--       -- p : _
--       -- p = Displayed-functor-pathp _ {!   !} {!   !}

    
-- --     -- (ap (λ z → z .F₀' f) $ Lam.uniquev {!   !} {!   !}) ∙ {!   !}

-- --   app :  ∀ {Γ} {A : Tp Γ} {B : Tp (Γ ⨾ A)} (f : Chk Γ (Π A B)) (x : Chk Γ A) → Chk Γ (B [ inst x ])
-- --   app f x = unlam f [ inst x , tp-[] ]

-- --   -- app-β :  ∀ {Γ Δ} {A : Tp Γ} {B : Tp (Γ ⨾ A)} {f : Chk Γ (Π A B)} {x : Chk Γ A} {γ : Sub Δ Γ} → app (lam f) x [ γ ]≡ ?
-- --   -- app-β = ?




-- -- --   -- Π-sub : ∀ {Γ Δ} {A : Tp Γ} {B : Tp (Γ ⨾ A)} (γ : Sub Δ Γ) →  Π A B [ γ ]≡ Π (A [ γ ]) (B [ keep-id γ ])
-- -- --   -- Π-sub γ = Pi.₁' (TpFam.π* _ _)

-- -- --   -- lam-sub : ∀ {Γ Δ} {A : Tp Γ} {B : Tp (Γ ⨾ A)} {x : Chk (Γ ⨾ A) B} (γ : Sub Δ Γ) → lam x [ γ , Π-sub γ ]≡ lam (x [ keep-id γ , Tps.π* _ _ ])
-- -- --   -- lam-sub γ = Lam.₁' (ChkFam.π* _ _)


-- -- -- -- record SigmaStructure {oc hc otp htp otm htm} (C : CwF oc hc otp htp otm htm) : Type (oc ⊔ hc ⊔ otp ⊔ htp ⊔ otm ⊔ htm) where
-- -- -- --   open CwF C
-- -- -- --   field
-- -- -- --     Sigma : Displayed-functor (πᶠ Tps) TpFam Tps
  
-- -- -- --   module Sigma = Displayed-functor Sigma

-- -- -- --   SgF : Functor 

-- -- --   -- field
-- -- --   --   Pair : Displayed-functor {!   !} ChkFam Tms

-- -- --   -- module Sigma = Displayed-functor Sigma
-- -- --   -- module Pair = Vertical-functor Pair

-- -- --   -- Σ : ∀ {Γ} (A : Tp Γ) (B : Tp (Γ ⨾ A)) → Tp Γ
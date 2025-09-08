```agda

open import Cat.Prelude
open import Cat.Functor.Adjoint
open import Cat.Displayed.Base 
open import Cat.Displayed.Total hiding (∫ ; πᶠ)
open import Cat.Displayed.Functor
open import Cat.Displayed.Composition
open import Cat.Bi.Base
open import Cat.Bi.Displayed.Base 
open import Cat.Bi.Displayed.Instances.DFib
open import Cat.Bi.Displayed.Instances.Cartesian.DFib
open import Cat.Bi.Displayed.Cartesian.Discrete 
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Cartesian.Discrete 

import Cat.Displayed.Cartesian.Discrete.Reasoning as Dcr
import Cat.Bi.Displayed.Cartesian.Discrete.Properties as Dcp
import Cat.Displayed.Reasoning as Dr

module Cat.Instances.CwF-old where

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


module DFib-Ob {o ℓ o' ℓ'} {𝒮 : Precategory o ℓ} ((A , A*) : Σ (Displayed 𝒮 o' ℓ') is-discrete-cartesian-fibration) where
  open Dr A public
  open is-discrete-cartesian-fibration A* public
  open Dcr A* public


record CwF o ℓ : Type (lsuc (o ⊔ ℓ)) where
  open Dcp (DFib o ℓ o ℓ) DFib-2-cart  public
  open Prebicategory-Hom-Reasoning (Cat o ℓ) public
  open Bidisplayed-Hom[]-Reasoning (DFib o ℓ o ℓ)  renaming (Ob[_] to DFib[_]) public 
  open is-discrete-cartesian-bifibration (DFib-discrete-bifibration {o} {ℓ} {o} {ℓ}) public

  field
    𝒞 : Precategory o ℓ
    Tp : DFib[ 𝒞 ]
    Chk : DFib[ ∫ Tp ] 
    Extension : is-representable Tp Chk

  module 𝒞 = Precategory 𝒞

  open _⊣_ (Extension .snd) hiding (η ; ε)

  Syn : DFib[ 𝒞 ]
  Syn = DFibΣ Tp Chk

  module Tp = DFib-Ob Tp
  module Chk = DFib-Ob Chk
  module Syn = DFib-Ob Syn

  -- In Uemura's paper, (A ≡ Syn) and (B ≡ Tp)

  Infer : Syn [ Id ]↦ Tp
  Infer = πᵈ

  Extend : Functor (∫ Tp) (∫ Chk)
  Extend = Extension .fst 

  module Extend = Functor Extend

  Ext𝒞 : Functor (∫ Tp) 𝒞 
  Ext𝒞 = (πᶠ Tp F∘ πᶠ Chk) F∘ Extend


--   TpFam : DFib[ ∫ Tp ]
--   TpFam = Ext𝒞 ^*1 Tp

--   ChkFam : DFib[ ∫ TpFam ]
--   ChkFam = ∫ᶠ (π*1 Ext𝒞 Tp) ^*1 Chk

--   module Syntax where
--     open ∫Hom

--     Ctx : Type _
--     Ctx = 𝒞.Ob

--     Sub : Ctx → Ctx → Type _
--     Sub = 𝒞.Hom

--     instance
--       Tp-Sub : Sub-notation Ctx Tp.Ob[_]
--       Tp-Sub = sub-notation Sub λ A γ → Tp.ob[ γ ] A

--       -- Tps.Hom[_] expresses the equational theory of subsitutions as functional relation
--       Tp-Sub-Rel : Sub-Rel-notation Ctx Tp.Ob[_]
--       Tp-Sub-Rel = sub-rel-notation Sub λ A γ B → Tp.Hom[ γ ] B A

--       -- We have the same sort of substitution data on Chk and Syn
--       Chk-sub : Sub-notation (Σ Ctx Tp.Ob[_]) Chk.Ob[_]
--       Chk-sub .Sub-notation.lvl = _
--       Chk-sub .Sub-notation.Subst (Γ , A) (Δ , B) = Σ[ γ ∈ Sub Γ Δ ] B [ γ ]≡ A
--       Chk-sub .Sub-notation._[_] x (γ , p) = Chk.ob[ ∫hom γ p ] x

--       Chk-sub-rel : Sub-Rel-notation (Σ Ctx Tp.Ob[_]) Chk.Ob[_]
--       Chk-sub-rel .Sub-Rel-notation.l1 = _
--       Chk-sub-rel .Sub-Rel-notation.l2 = _
--       Chk-sub-rel .Sub-Rel-notation.Subst (Γ , A) (Δ , B) = Σ[ γ ∈ Sub Γ Δ ] B [ γ ]≡ A
--       Chk-sub-rel .Sub-Rel-notation._[_]≡_ x (γ , p) y = Chk.Hom[ (∫hom γ p) ] y x
      
--       Syn-sub : Sub-notation Ctx Syn.Ob[_]
--       Syn-sub .Sub-notation.lvl = _
--       Syn-sub .Sub-notation.Subst = Sub
--       Syn-sub .Sub-notation._[_] (α , e) σ = α [ σ ] , (e [ σ , Tp.π* σ α ])

--       Syn-sub-rel : Sub-Rel-notation Ctx Syn.Ob[_]
--       Syn-sub-rel .Sub-Rel-notation.l1 = _
--       Syn-sub-rel .Sub-Rel-notation.l2 = _
--       Syn-sub-rel .Sub-Rel-notation.Subst = Sub
--       Syn-sub-rel .Sub-Rel-notation._[_]≡_ x γ y = Syn.Hom[ γ ] y x

--     _⨾_ : (Γ : Ctx) → Tp ʻ Γ → Ctx
--     Γ ⨾ A = Extend.₀ (Γ , A) .fst .fst

--     wkₜ : ∀ {Γ} (A : Tp ʻ Γ) → Tp ʻ (Γ ⨾ A)
--     wkₜ A = Extend.₀ (_ , A) .fst .snd

--     var : ∀ {Γ} (A : Tp ʻ Γ) → Chk · (Γ ⨾ A , wkₜ A)
--     var A = Extend.₀ (_ , _) .snd

--     keep : ∀ {Γ Δ A B} (γ : Sub Γ Δ) → B [ γ ]≡ A → Sub (Γ ⨾ A) (Δ ⨾ B)
--     keep γ p = Extend.₁ (∫hom _ p) .fst .fst

--     keep-tp
--       : ∀ {Γ Δ A B}
--       → (γ : Sub Γ Δ)
--       → (p : B [ γ ]≡ A)
--       → (wkₜ B) [ keep γ p ]≡ (wkₜ A) 
--     keep-tp γ p = Extend.₁ (∫hom γ p) .fst .snd 


--     keep-chk
--       : ∀ {Γ Δ A B}
--       → (γ : Sub Γ Δ)
--       → (p : B [ γ ]≡ A)
--       → (var B) [ (keep γ p) , (keep-tp γ p) ]≡ (var A)
--     keep-chk γ p = Extend.₁ (∫hom γ p) .snd


--     keep-id : ∀ {Γ Δ} {A : Tp ʻ Δ} (γ : Sub Γ Δ) → Sub (Γ ⨾ (A [ γ ])) (Δ ⨾ A)
--     keep-id γ = keep γ (Tp.π* _ _)

--     tp-[] : ∀ {Γ Δ} {A : Tp ʻ Δ} {γ : Sub Γ Δ} → A [ γ ]≡ A [ γ ]
--     tp-[] = Tp.π* _ _

--     π : ∀ {Γ} {A : Tp ʻ Γ} → Sub (Γ ⨾ A) Γ
--     π {Γ} {A} = counit.ε (Γ , A) .fst

--     π-tp : ∀ {Γ} {A : Tp ʻ Γ} → A [ π ]≡ wkₜ A 
--     π-tp {Γ} {A} = counit.ε (Γ , A) .snd

--     inst : ∀ {Γ} {A : Tp ʻ Γ} (x : Chk ʻ (Γ , A)) → Sub Γ (Γ ⨾ A)
--     inst {Γ = Γ} {A = A} x = unit.η ((Γ , A) , x) .fst .fst

--     inst-tp : ∀ {Γ} {A : Tp ʻ Γ} (x : Chk ʻ (Γ , A)) → wkₜ A [ inst x ]≡ A 
--     inst-tp {Γ = Γ} {A = A} x = unit.η ((Γ , A) , x) .fst .snd

--     inst-chk
--       : ∀ {Γ} {A : Tp ʻ Γ}
--       → (x : Chk ʻ (Γ , A))
--       → var A [ inst x , inst-tp x ]≡ x
--     inst-chk {Γ = Γ} {A = A} x = unit.η ((Γ , A) , x) .snd

-- open Displayed-functor 
-- open _=[_]=>_

-- record PiStructure {o ℓ} (C : CwF o ℓ) : Type (lsuc (o ⊔ ℓ)) where
--   open CwF C
--   open Syntax
--   field
--     Pi  : TpFam [ πᶠ Tp ]↦ Tp
--     Lam : ChkFam [ ∫ᶠ Pi ]↦ Chk
--     Lam* : is-discrete-cartesian {A' = ChkFam} {B' = Chk} (∫ᶠ Pi) Lam

--   module Pi = Displayed-functor Pi

--   Laws : ChkFam ≅ᵇ↓ (∫ᶠ Pi ^*1 Chk) 
--   Laws = discrete-cartesian→domain-unique Lam* π*1.cartesian
  
--   module Laws = _≅ᵇ↓_ Laws
--   module Lam   = Displayed-functor Laws.to'
--   module Unlam = Displayed-functor Laws.from'
  

--   Π : ∀ {Γ} (A : Tp ʻ Γ) → Tp ʻ (Γ ⨾ A) → Tp ʻ Γ
--   Π A B = Pi.₀' B

--   lam : ∀ {Γ} {A : Tp ʻ Γ} {B : Tp ʻ (Γ ⨾ A)} → Chk ʻ (Γ ⨾ A , B) → Chk ʻ (Γ , Π A B)
--   lam = Lam.₀'

--   unlam :  ∀ {Γ} {A : Tp ʻ Γ} {B : Tp ʻ (Γ ⨾ A)} → Chk ʻ (Γ , Π A B) → Chk ʻ (Γ ⨾ A , B)
--   unlam = Unlam.₀'

  
--   -- lam-β : ∀ {Γ} {A : Tp ʻ Γ} {B : Tp ʻ (Γ ⨾ A)} (x : Chk ʻ (Γ ⨾ A , B)) → unlam (lam x) Chk.≡[ {!  !} ]ob x 
--   -- lam-β x = Laws.invr' .η' x


  
```
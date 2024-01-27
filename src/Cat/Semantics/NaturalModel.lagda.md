<!--
```agda
open import Cat.Prelude hiding (⟪_⟫)
import Cat.Reasoning
open import Cat.Functor.Base
open import Cat.Instances.Product
open import Cat.Functor.Hom
open import Cat.Diagram.Terminal
open import Cat.Diagram.Product
open import Cat.Diagram.Exponential
open import Cat.Diagram.Coproduct
open import Cat.CartesianClosed.Instances.PSh
open import Cat.Displayed.Base
open import Cat.Displayed.Instances.Elements renaming (∫ to Elem)
open import Cat.Displayed.Total
open import Cat.Functor.Adjoint
open import 1Lab.Reflection hiding (var ; [_])

open Precategory
open Functor
open _=>_
open _⊣_
open Total-hom
open Displayed

```
-->

```agda
module Cat.Semantics.NaturalModel where
```

We present a way to model simply typed lambda calculus categorically

<!--
```agda



module PSh-reasoning {o h} (C : Precategory o (o ⊔ h)) where

  private
    module C = Cat.Reasoning C
    module C^ = Cat.Reasoning Cat[ C ^op , Sets (o ⊔ h) ]
    module Products A B = Product (PSh-products {o} {o ⊔ h} {o ⊔ h} {C = C} A B)
    module Exps A B = Exponential (PSh-closed {o} {o ⊔ h} {o ⊔ h} {C = C} .Cartesian-closed.has-exp A B)
    

  -- Fibre categories!
  ∫ᵉ_ : (c : C.Ob) → Precategory _ _
  ∫ᵉ c = ∫ (Elem C (よ₀ C c))

  module ∫ᵉ c = Cat.Reasoning (∫ᵉ c) 
  
  -- Cartesian lifts?? i.e. the assignment of fibre categories is functorial
  ∫ᶠ_ : ∀ {x y} (f : C.Hom x y) → Functor (∫ᵉ x) (∫ᵉ y)
  (∫ᶠ f) .F₀ (x' , f') = x' , (f C.∘ f')
  (∫ᶠ f) .F₁ g = total-hom (g .hom) (sym (C.assoc _ _ _) ∙ (ap (f C.∘_) (g .preserves)))
  (∫ᶠ f) .F-id = total-hom-path _ refl (C.Hom-set _ _ _ _ _ _)
  (∫ᶠ f) .F-∘ g h = total-hom-path _ refl (C.Hom-set _ _ _ _ _ _)

  module ∫ᶠ {x y} (f : C.Hom x y) = Functor (∫ᶠ f)

  ∫ᵉ-disc : (c : C.Ob) → 

--   ⟪⊤⟫ : C^.Ob
--   ⟪⊤⟫ = PSh-terminal {C = C} .Terminal.top

--   infixr 25 _⟪×⟫_
--   _⟪×⟫_ : C^.Ob → C^.Ob → C^.Ob
--   A ⟪×⟫ B = Products.apex A B
  
--   ⟪π₁⟫ : ∀ {A B} → A ⟪×⟫ B => A
--   ⟪π₁⟫ {A} {B} = Products.π₁ A B

--   ⟪π₂⟫ : ∀ {A B} → A ⟪×⟫ B => B
--   ⟪π₂⟫ {A} {B} = Products.π₂ A B

--   infixr 25 _⟪→⟫_
--   _⟪→⟫_ : C^.Ob → C^.Ob → C^.Ob
--   A ⟪→⟫ B = Exps.B^A A B

--   -- el ((よ₀ C c ⊗₀ A) => B

--   -- ⟪-⟫×_=>_ : C^.Ob → C^.Ob → C^.Ob
--   -- ⟪-⟫×_=>_ = PSh-closed.hom₀ {o} {o ⊔ h} {o ⊔ h} {C = C}

--   -- ⟪λ⟫ : ∀ {A B : C^.Ob} {c} → (∀ {d} → C.Hom d c → (A ʻ d) → B ʻ d) → (A ⟪→⟫ B) ʻ c
--   -- ⟪λ⟫ f .η d (h , e) = {! f  !}
--   -- ⟪λ⟫ f .is-natural = {!   !}
--   -- (⟪-⟫× A => B) => (A ⟪→⟫ B)
--   -- ⟪λ⟫  = {! PSh-closed.adj {o} {o ⊔ h} {o ⊔ h} {C = C} _ .unit !}

--   infixr 25 _⟪⊎⟫_
--   _⟪⊎⟫_ : C^.Ob → C^.Ob → C^.Ob
--   A ⟪⊎⟫ B = PSh-coproducts {C = C} A B .Coproduct.coapex

--   ∫ₑ : C^.Ob → Precategory _ _
--   ∫ₑ F = ∫ (Elem C F)
-- ```
-- -->

-- Given a precategory $C$, we define what we need to use $C$ to model a simple type theory

-- ```agda
-- record Natural-model o h : Type (lsuc (o ⊔ h)) where
--   no-eta-equality
--   field
--     Ctx : Precategory o (o ⊔ h)
-- ```
-- The idea is $C$ is going to a category of _contexts_. The objects of $C$ will be contexts, which we refer to using capital greek
-- letters ($\Gamma$, $\Theta$), and the morphisms of $C$ will be _simultaneous substitutions_ between contexts, which we refer to using
-- lower case greek letters ($\gamma$, $\theta$).

-- Note that so far we have not imposed any restrictions on $C$, it could literally be any category! Crucially, the contexts are not
-- lists of types, and the simultaneous substitutions are not lists of terms. We haven't even defined types or terms yet. We call
-- $C$ $Ctx$ to remind us of its role.
-- ```agda 
--   module Ctx = Cat.Reasoning Ctx
--   open Ctx public
-- ```
-- The first thing we'll need to model simple type theory is a set of types. Recall again that this need not be some kind of AST, it can
-- be any set at all.
-- ```agda
--   field
--     Tp : Type h
--     Tp-set : is-set Tp
-- ```

-- Now we get to the interesting bit. We have some abstract notion of a context and some abstract notion of a type, but we need 
-- a way to connect them, we need a definition of _terms_. *Insert motivation for this idea here*.
-- We choose to model terms $\Gamma \vdash A$ using _presheaves on $Ctx$_. A presheaf on the category of contexts
-- is a functor $Ctx \to Set$. This packages up two things at once. The action on objects (contexts), is a function
-- that sends a context $\Gamma$ to abstact notion of "$\Gamma$ shaped stuff". The action on morphisms (substitutions)
-- is a function that sends a substitution $\gamma : \Delta \to \Gamma$ to a function from "$\Gamma$ shaped stuff" to 
-- $\Delta$ shaped stuff. We can see already that the structure of "terms in a context, acted on by substitutions" is arising.
-- We treat presheaves on $Ctx$ as a sort of logical framework, a meta-language in which we can describe the properties of
-- our type theory in a "nice" way. For this reason we call the category of such presheaves $Meta$.
-- ```agda
--   module Meta = Cat.Reasoning Cat[ Ctx ^op , Sets (o ⊔ h) ]
-- ```
-- Every context $\Gamma$ embeds into $Meta$ via the yoneda embedding. This is basically the "minimal $\Gamma$ shaped thing":
-- the set of all homs into $\Gamma$, which the yoneda lemma tells us has exactly the same context as $\Gamma$ itself.

-- But we still haven't mentioned types. "$\Gamma$ shaped stuff" won't do, we need "$\Gamma$ shaped stuff of type $A$"!
-- Using `Tp`{.Agda}, we carve out a particular subset of "$\Gamma$ shaped stuff" for each type. These are our terms!
-- Using our logical framework idea, for each `Tp`{.Agda} we have some `Meta`{.Agda} set of all the terms of that type.
-- ```agda
--   field
--     Tm : Tp → Meta.Ob
  
-- ```
-- We decompose the `Tm`{.Agda} presheaf into its two components to give us nice notation.
-- ```agda
--   module Tm (A : Tp) = Functor (Tm A)

--   _⊢_ : Ctx.Ob → Tp → Type _
--   Γ ⊢ A = ⌞ Tm.₀ A Γ ⌟

--   _[_] : ∀ {Γ Δ A} → Γ ⊢ A → Ctx.Hom Δ Γ → Δ ⊢ A
--   e [ γ ] = Tm.₁ _ γ e

--   open PSh-reasoning {o} {o ⊔ h} Ctx
-- ```
-- So far we still haven't imposed any restrictions on $Ctx$. It could literally be any precategory. The thing we're
-- missing is context extension! Given a context $\Gamma$, and a type $A$, we should be able to form the context $\Gamma, $A$.
-- ```agda
--   infixl 25 _⨾_
--   field
--     _⨾_ : Ctx.Ob → Tp → Ctx.Ob
-- ```
-- We'd like this operation to have some kind of meaning, so we give it semantics in our meta language.
-- Essentially, `Γ ⨾ A` shaped stuff should act like pairs of `Γ` shaped stuff and `A` shaped stuff.
-- Equivalently, `Γ ⨾ A` is the representing object for our product presheaf on the right.
-- ```agda
--     ⨾-sem : ∀ {Γ A} → ⟪ Γ ⨾ A ⟫ Meta.≅ ⟪ Γ ⟫ ⟪×⟫ Tm A
-- ``` 

-- Now we can start defining some type formers, and giving them semantics in our meta language.

-- ```agda
--   field
--     `⊤ : Tp
--     `⊤-sem : Tm `⊤ Meta.≅ ⟪⊤⟫
    
--     _`×_ : Tp → Tp → Tp
--     `×-sem : ∀ {A B} → Tm (A `× B) Meta.≅ Tm A ⟪×⟫ Tm B

--     _`→_ : Tp → Tp → Tp
--     `→-sem : ∀ {A B} → Tm (A `→ B) Meta.≅ Tm A ⟪→⟫ Tm B

--     ∅ : Ctx.Ob
--     ∅-empty : is-terminal Ctx ∅
-- ```

-- We can decompose the isomorphisms into all the expected rules of type theory

-- ```agda 
--   variable
--     Γ Δ Ξ Θ : Ctx.Ob
--     A B : Tp


--   data _∋_ : Ctx.Ob → Tp → Type (o ⊔ h) where
--     stop : Γ ⨾ A ∋ A
--     pop : Γ ∋ A → Γ ⨾ B ∋ A
    
--   ⟪_⟫ₙ : Γ ∋ A → Meta.Hom ⟪ Γ ⟫ (Tm A)
--   ⟪ stop ⟫ₙ = ⟪π₂⟫ ∘nt ⨾-sem .Meta.to
--   ⟪ pop x ⟫ₙ = ⟪ x ⟫ₙ ∘nt ⟪π₁⟫ ∘nt ⨾-sem .Meta.to
  
--   `var : Γ ∋ A → Γ ⊢ A
--   `var x = ⟪ x ⟫ₙ .η _ Ctx.id


--   -- `var stop = {! ⨾-sem .Meta.from .η _  !}
--   -- `var (pop x) = {!   !} 
  
--   -- ∅ₛ : Ctx.Hom Γ ∅
--   -- ∅ₛ = ∅-empty _ .centre

--   -- idₛ : Ctx.Hom Γ Γ
--   -- idₛ = Ctx.id

--   -- _⨾ₛ_ : Ctx.Hom Γ Δ → Γ ⊢ A → Ctx.Hom Γ (Δ ⨾ A)
--   -- γ ⨾ₛ e = ⨾-sem .Meta.from .η _ (γ , e)

--   -- π : Ctx.Hom Δ (Γ ⨾ A) →  Ctx.Hom Δ Γ
--   -- π γ = ⨾-sem .Meta.to .η _ γ .fst

--   -- _∘ₛ_ : Ctx.Hom Δ Ξ → Ctx.Hom Γ Δ → Ctx.Hom Γ Ξ
--   -- _∘ₛ_ = Ctx._∘_

--   -- idrₛ : (f : Ctx.Hom Γ Δ) → (f ∘ₛ idₛ) ≡ f
--   -- idrₛ = Ctx.idr

--   -- idlₛ : (f : Ctx.Hom Γ Δ) → (idₛ ∘ₛ f) ≡ f
--   -- idlₛ = Ctx.idl

--   -- assocₛ : (f : Ctx.Hom Ξ Θ) (g : Ctx.Hom Δ Ξ) (h : Ctx.Hom Γ Δ) → (f ∘ₛ (g ∘ₛ h)) ≡ ((f ∘ₛ g) ∘ₛ h)
--   -- assocₛ = Ctx.assoc

--   -- π-∘ : (γ : Ctx.Hom Γ Δ) (σ : Ctx.Hom Δ (Ξ ⨾ A)) → π σ ∘ₛ γ ≡ π (σ ∘ₛ γ)
--   -- π-∘ γ σ = ap fst (sym (⨾-sem .Meta.to .is-natural _ _ _) #ₚ _)

--   -- π-⨾ : (γ : Ctx.Hom Γ Δ) (x : Γ ⊢ A) → π (γ ⨾ₛ x) ≡ γ
--   -- π-⨾ γ x = ap fst (⨾-sem .Meta.invl ηₚ _ #ₚ (γ , x))

--   -- -- `var : Ctx.Hom Δ (Γ ⨾ A) → Δ ⊢ A
--   -- -- `var γ = ⨾-sem .Meta.to .η _ γ .snd

--   -- -- ηₛ : (γ : Ctx.Hom Γ (Δ ⨾ A)) → π γ ⨾ₛ `var γ ≡ γ
--   -- -- ηₛ γ = ⨾-sem .Meta.invr ηₚ _ #ₚ γ

--   -- -- η-∅ : (γ : Ctx.Hom Γ ∅) → ∅ₛ ≡ γ
--   -- -- η-∅ γ = ∅-empty _ .paths γ

--   -- opaque
--   --   -- ⟪λ⟫ : ∀ {A B} → (∀ {Δ} {γ : Ctx.Hom Δ Γ} → Δ ⊢ A → Δ ⊢ B) → Γ ⊢ (A `→ B)
--   --   -- ⟪λ⟫ f = `→-sem .Meta.from .η _ (NT (λ Δ (γ , x) → f {γ = γ} x) λ Δ Ξ γ → ext λ σ → {!   !})

--   --   -- _⟪$⟫_ : Γ ⊢ (A `→ B) → (

--   --   ⟪_⟫⊢ : ⟪ Γ ⟫ => Tm A → Γ ⊢ A
--   --   ⟪ φ ⟫⊢ = φ .η _ idₛ
    
--   --   ⊢⟪_⟫ : Γ ⊢ A → ⟪ Γ ⟫ => Tm A
--   --   ⊢⟪ f ⟫ .η Δ γ = f [ γ ] 
--   --   ⊢⟪ f ⟫ .is-natural Δ Ξ δ = ext λ δ → Tm.F-∘ _ _ _ #ₚ f

--   --   ⟪⟫-inv : (f : Γ ⊢ A) → ⟪ ⊢⟪ f ⟫ ⟫⊢ ≡ f
--   --   ⟪⟫-inv f = Tm.F-id _ #ₚ f

--   --   [⟪⟫⊢] : (φ : ⟪ Γ ⟫ => Tm A) (γ : Ctx.Hom Δ Γ) → ⟪ φ ⟫⊢ [ γ ] ≡ φ .η Δ γ
--   --   [⟪⟫⊢] {Γ = Γ} {Δ = Δ} φ γ = sym (φ .is-natural Γ _ γ #ₚ idₛ) ∙ ap (φ .η Δ) (Ctx.idl _)

--   -- `tt : Γ ⊢ `⊤
--   -- `tt = `⊤-sem .Meta.from .η _ (lift tt)

--   -- `⟨_,_⟩ : Γ ⊢ A → Γ ⊢ B → Γ ⊢ (A `× B)
--   -- `⟨ a , b ⟩ = `×-sem .Meta.from .η _ (a , b)

--   -- `π₁ : Γ ⊢ (A `× B) → Γ ⊢ A
--   -- `π₁ p = fst $ `×-sem .Meta.to .η _ p
  
--   -- `π₂ : Γ ⊢ (A `× B) → Γ ⊢ B
--   -- `π₂ p = snd $ `×-sem .Meta.to .η _ p
 
--   -- `λ : (Γ ⨾ A) ⊢ B → Γ ⊢ (A `→ B)
--   -- `λ {Γ} {A} {B} f = `→-sem .Meta.from .η _ (⊢⟪ f ⟫ ∘nt ⨾-sem .Meta.from)

--   -- `ν : Γ ⊢ (A `→ B) → (Γ ⨾ A) ⊢ B
--   -- `ν {Γ} {A} {B} f = ⟪ `→-sem .Meta.to .η _ f ∘nt ⨾-sem .Meta.to ⟫⊢
  
--   -- [id] : (x : Γ ⊢ A) → x [ idₛ ] ≡ x
--   -- [id] x = Tm.F-id _ #ₚ x

--   -- [∘] : (γ : Ctx.Hom Δ Ξ) (σ : Ctx.Hom Γ Δ) (x : Ξ ⊢ A) → x [ γ ∘ₛ σ ] ≡ (x [ γ ]) [ σ ]
--   -- [∘] γ σ x = Tm.F-∘ _ _ _ #ₚ x
  
--   -- `var-∘ : (γ : Ctx.Hom Δ (Ξ ⨾ A)) (σ : Ctx.Hom Γ Δ) → `var γ [ σ ] ≡ `var (γ ∘ₛ σ)
--   -- `var-∘ γ σ = sym (ap snd (⨾-sem .Meta.to .is-natural _ _ _ #ₚ _))
  
--   -- `var-⨾ : (γ : Ctx.Hom Γ Δ) (x : Γ ⊢ A) → `var (γ ⨾ₛ x) ≡ x
--   -- `var-⨾ γ x = ap snd (⨾-sem .Meta.invl ηₚ _ #ₚ _)

--   -- [`π₁] : (γ : Ctx.Hom Γ Δ) (x : Δ ⊢ (A `× B)) → (`π₁ x) [ γ ] ≡ `π₁ (x [ γ ])
--   -- [`π₁] γ x = sym (ap fst (`×-sem .Meta.to .is-natural _ _ _ #ₚ _))

--   -- [`π₂] : (γ : Ctx.Hom Γ Δ) (x : Δ ⊢ (A `× B)) → (`π₂ x) [ γ ] ≡ `π₂ (x [ γ ])
--   -- [`π₂] γ x = sym (ap snd (`×-sem .Meta.to .is-natural _ _ _ #ₚ _))

--   -- `νβ : (f : Δ ⨾ A ⊢ B) → `ν (`λ f) ≡ f
--   -- `νβ f = 
--   --   `ν (`λ f) ≡⟨ refl ⟩ 
--   --   ⟪ ⌜ `→-sem .Meta.to .η _ (`λ f) ⌝ ∘nt ⨾-sem .Meta.to ⟫⊢  ≡⟨ ap! (`→-sem .Meta.invl ηₚ _ #ₚ _) ⟩ -- (λ i → ⟪ ((`→-sem .Meta.invl ηₚ _) #ₚ (⊢⟪ f ⟫ ∘nt ⨾-sem .Meta.from)) i ∘nt ⨾-sem .Meta.to ⟫⊢ ) ⟩
--   --   ⟪ ⌜ (⊢⟪ f ⟫ ∘nt ⨾-sem .Meta.from) ∘nt ⨾-sem .Meta.to ⌝ ⟫⊢ ≡⟨ ap! trivial! ⟩
--   --   ⟪ ⊢⟪ f ⟫ ∘nt ⌜ ⨾-sem .Meta.from ∘nt ⨾-sem .Meta.to ⌝ ⟫⊢ ≡⟨ ap! (⨾-sem .Meta.invr) ⟩ 
--   --   ⟪ ⌜ ⊢⟪ f ⟫ ∘nt idnt ⌝ ⟫⊢ ≡⟨ ap! trivial! ⟩ 
--   --   ⟪ ⊢⟪ f ⟫ ⟫⊢ ≡⟨ ⟪⟫-inv f ⟩
--   --   f ∎




--   -- _`$_ : Γ ⊢ (A `→ B) → Γ ⊢ A → Γ ⊢ B
--   -- f `$ x = `→-sem .Meta.to .η _ f .η _ (Ctx.id , x)

    
-- -- instance
-- --   open hlevel-projection
  
-- --   decomp-Tp : hlevel-projection (quote Natural-model.Tp)
-- --   decomp-Tp .has-level = quote Natural-model.Tp-set
-- --   decomp-Tp .get-level _ = pure (lit (nat 2))
-- --   decomp-Tp .get-argument (_ ∷ _ ∷ arg _ t ∷ _) = pure t
-- --   decomp-Tp .get-argument _ = typeError []

-- -- record Model-hom {o h} (N : Natural-model o h) (M : Natural-model o h) : Type (o ⊔ h) where
-- --   no-eta-equality
-- --   private
-- --     module N = Natural-model N
-- --     module M = Natural-model M
-- --   field
-- --     F : Functor N.Ctx M.Ctx

-- --   private module F = Functor F

-- --   field
-- --     F-tp : N.Tp → M.Tp
-- --     F-tm : (A : N.Tp) → N.Tm A => M.Tm (F-tp A) F∘ F.op

-- --     pres-∅ : F.₀ N.∅ M.≅ M.∅
-- --     pres-⨾ : ∀ {Γ A} → F.₀ (Γ N.⨾ A) M.≅ ((F.₀ Γ) M.⨾ F-tp A)

-- --     pres-`⊤ : F-tp N.`⊤ ≡ M.`⊤
-- --     pres-`× : ∀ {A B} → F-tp (A N.`× B) ≡ (F-tp A M.`× F-tp B)
-- --     pres-`→ : ∀ {A B} → F-tp (A N.`→ B) ≡ (F-tp A M.`→ F-tp B)

-- --   open F public
-- --     -- Functors always preserve isos, so no need to explicitly require this


-- -- private 
-- --   unquoteDecl eqv = declare-record-iso eqv (quote Model-hom)
-- --   module Eqv {o h} {N M : Natural-model o h} = Equiv (Iso→Equiv (eqv {o} {h} {N} {M}))
    
-- --   funextP' : ∀ {ℓ ℓ₁} {A : Type ℓ} {B : A → I → Type ℓ₁}
-- --     → {f : ∀ {a} → B a i0} {g : ∀ {a} → B a i1}
-- --     → (∀ a → PathP (B a) (f {a}) (g {a}))
-- --     → PathP (λ i → ∀ {a} → B a i) (λ {a} → f {a}) (λ {a} → g {a})
-- --   funextP' p i {x} = p x i

-- -- Model-hom-path : 
-- --   ∀ {o h} {N M : Natural-model o h} 
-- --     {f g : Model-hom N M}
-- --     (let module N = Natural-model N)
-- --     (let module M = Natural-model M)
-- --     (let module f = Model-hom f)
-- --     (let module g = Model-hom g)
-- --   → (p : f.F ≡ g.F)
-- --   → (q : f.F-tp ≡ g.F-tp)
-- --   → (∀ A Δ x → PathP (λ i → ⌞ M.Tm (q i A) .F₀ ((p i) .F₀ Δ) ⌟) (f.F-tm A .η Δ x) (g.F-tm A .η Δ x))
-- --   → (PathP (λ i → M.Hom (p i .F₀ N.∅) M.∅) (f.pres-∅ .M.to) (g.pres-∅ .M.to))
-- --   → (∀ Δ A → PathP (λ i → M.Hom (p i .F₀ (Δ N.⨾ A)) ((p i .F₀ Δ) M.⨾ (q i A))) (f.pres-⨾ .M.to) (g.pres-⨾ .M.to)) 
-- --   → f ≡ g
-- -- Model-hom-path {M = M} a b c d e = Eqv.injective $
-- --   Σ-pathp a $ 
-- --   Σ-pathp b $
-- --   Σ-pathp (funextP λ A → Nat-pathp refl _ λ Δ → funextP λ x → c A Δ x) $
-- --   Σ-pathp (M.≅-pathp _ _ d) $
-- --   Σ-pathp (funextP' λ Δ → funextP' λ A → M.≅-pathp _ _ (e Δ A)) $
-- --   Σ-pathp (is-prop→pathp (λ i → M.Tp-set _ _) _ _) $ 
-- --   Σ-pathp (funextP' λ A → funextP' λ B → is-prop→pathp (λ i → M.Tp-set _ _) _ _) $
-- --   funextP' λ A → funextP' λ B → is-prop→pathp (λ i → M.Tp-set _ _) _ _
-- --   where
-- --     module M = Natural-model M
 

   
-- ```        
<!--
```agda
-- {-# OPTIONS --show-implicit #-}
open import Cat.Prelude hiding (⟪_⟫)
import Cat.Reasoning
open import Cat.Functor.Base
open import Cat.Instances.Product
open import Cat.Functor.Hom
open import Cat.Diagram.Terminal
open import Cat.Diagram.Initial
open import Cat.Diagram.Product
open import Cat.Diagram.Exponential
open import Cat.Diagram.Coproduct
open import Cat.CartesianClosed.Instances.PSh
open import Cat.Displayed.Base
open import Cat.Displayed.Instances.Elements renaming (∫ to Elem)
open import Cat.Displayed.Total
open import Cat.Functor.Adjoint
open import 1Lab.Reflection hiding (var ; [_] ; var₀)
open import Cat.Morphism
open import 1Lab.Rewrite

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

  module C^ = Cat.Reasoning Cat[ C ^op , Sets (o ⊔ h) ]

  private
    module C = Cat.Reasoning C
    module Products A B = Product (PSh-products {o} {o ⊔ h} {o ⊔ h} {C = C} A B)
    module Y = Yoneda C

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

  ⟪_⟫ : C.Ob → C^.Ob
  ⟪_⟫ = よ₀ C
  
  ⟪⊤⟫ : C^.Ob
  ⟪⊤⟫ = PSh-terminal {C = C} .Terminal.top
    
  infixr 25 _⟪×⟫_
  _⟪×⟫_ : C^.Ob → C^.Ob → C^.Ob
  A ⟪×⟫ B = Products.apex A B

  module Prods = Binary-products _ (PSh-products {o} {o ⊔ h} {o ⊔ h} {C = C})

  _⟪×⟫₁_ : _
  _⟪×⟫₁_ = Prods._⊗₁_
  
  ⟪π₁⟫ : ∀ {A B} → A ⟪×⟫ B => A
  ⟪π₁⟫ {A} {B} = Products.π₁ A B

  ⟪π₂⟫ : ∀ {A B} → A ⟪×⟫ B => B
  ⟪π₂⟫ {A} {B} = Products.π₂ A B

  infixr 25 _⟪→⟫_
  _⟪→⟫_ : C^.Ob → C^.Ob → C^.Ob
  A ⟪→⟫ B = Exps.B^A A B

  ⟪λ⟫ : {A B Γ : C^.Ob} → C^.Hom (Γ ⟪×⟫ A) B → C^.Hom Γ (A ⟪→⟫ B)
  ⟪λ⟫ = Exps.ƛ _ _ 

  ⟪ν⟫ : {A B Γ : C^.Ob} → C^.Hom Γ (A ⟪→⟫ B) → C^.Hom (Γ ⟪×⟫ A) B
  ⟪ν⟫ = Exps.unlambda _ _



  module ⟪λ⟫-Equiv {A B Γ} = Equiv (⟪λ⟫ {Γ = Γ} , Exps.lambda-is-equiv A B)
  
  
```
-->

Given a precategory $C$, we define what we need to use $C$ to model a simple type theory

```agda
record Natural-model o h : Type (lsuc (o ⊔ h)) where
  no-eta-equality
  field
    Ctx : Precategory o (o ⊔ h)
```
The idea is $C$ is going to a category of _contexts_. The objects of $C$ will be contexts, which we refer to using capital greek
letters ($\Gamma$, $\Theta$), and the morphisms of $C$ will be _simultaneous substitutions_ between contexts, which we refer to using
lower case greek letters ($\gamma$, $\theta$).

Note that so far we have not imposed any restrictions on $C$, it could literally be any category! Crucially, the contexts are not
lists of types, and the simultaneous substitutions are not lists of terms. We haven't even defined types or terms yet. We call
$C$ $Ctx$ to remind us of its role.
```agda 
  module Ctx = Cat.Reasoning Ctx
  open Ctx public
```
The first thing we'll need to model simple type theory is a set of types. Recall again that this need not be some kind of AST, it can
be any set at all.
```agda
  field
    Tp : Type h
    Tp-set : is-set Tp
  
  instance
    tp-set : ∀ {n} → H-Level Tp (2 + n)
    tp-set = basic-instance 2 Tp-set
```

Now we get to the interesting bit. We have some abstract notion of a context and some abstract notion of a type, but we need 
a way to connect them, we need a definition of _terms_. *Insert motivation for this idea here*.
We choose to model terms $\Gamma \vdash A$ using _presheaves on $Ctx$_. A presheaf on the category of contexts
is a functor $Ctx \to Set$. This packages up two things at once. The action on objects (contexts), is a function
that sends a context $\Gamma$ to abstact notion of "$\Gamma$ shaped stuff". The action on morphisms (substitutions)
is a function that sends a substitution $\gamma : \Delta \to \Gamma$ to a function from "$\Gamma$ shaped stuff" to 
$\Delta$ shaped stuff. We can see already that the structure of "terms in a context, acted on by substitutions" is arising.
We treat presheaves on $Ctx$ as a sort of logical framework, a meta-language in which we can describe the properties of
our type theory in a "nice" way. For this reason we call the category of such presheaves $Meta$.
```agda
  module Meta = Cat.Reasoning Cat[ Ctx ^op , Sets (o ⊔ h) ]
```
Every context $\Gamma$ embeds into $Meta$ via the yoneda embedding. This is basically the "minimal $\Gamma$ shaped thing":
the set of all homs into $\Gamma$, which the yoneda lemma tells us has exactly the same context as $\Gamma$ itself.

But we still haven't mentioned types. "$\Gamma$ shaped stuff" won't do, we need "$\Gamma$ shaped stuff of type $A$"!
Using `Tp`{.Agda}, we carve out a particular subset of "$\Gamma$ shaped stuff" for each type. These are our terms!
Using our logical framework idea, for each `Tp`{.Agda} we have some `Meta`{.Agda} set of all the terms of that type.
```agda
  field
    Tm : Tp → Meta.Ob
  
```
We decompose the `Tm`{.Agda} presheaf into its two components to give us nice notation.
```agda
  module Tm (A : Tp) = Functor (Tm A)
  module Y {A : Tp} = Yoneda Ctx (Tm A)

  _⊢_ : Ctx.Ob → Tp → Type _
  Γ ⊢ A = ⌞ Tm.₀ A Γ ⌟

  _[_] : ∀ {Γ Δ A} → Γ ⊢ A → Ctx.Hom Δ Γ → Δ ⊢ A
  e [ γ ] = Tm.₁ _ γ e

  open PSh-reasoning {o} {o ⊔ h} Ctx
```
So far we still haven't imposed any restrictions on $Ctx$. It could literally be any precategory. The thing we're
missing is context extension! Given a context $\Gamma$, and a type $A$, we should be able to form the context $\Gamma, $A$.
```agda
  infixl 25 _⨾_
  field
    _⨾_ : Ctx.Ob → Tp → Ctx.Ob
    
```
We'd like this operation to have some kind of meaning, so we give it semantics in our meta language.
Essentially, `Γ ⨾ A` shaped stuff should act like pairs of `Γ` shaped stuff and `A` shaped stuff.
Equivalently, `Γ ⨾ A` is the representing object for our product presheaf on the right.
```agda
    ⨾-sem : ∀ {Γ A} → ⟪ Γ ⨾ A ⟫ Meta.≅ ⟪ Γ ⟫ ⟪×⟫ Tm A

  module ⨾-sem {Γ A} = Meta._≅_ (⨾-sem {Γ} {A})
``` 

Now we can start defining some type formers, and giving them semantics in our meta language.

```agda
  field
    `⊤ : Tp
    `⊤-sem : Tm `⊤ Meta.≅ ⟪⊤⟫
    
    _`×_ : Tp → Tp → Tp
    `×-sem : ∀ {A B} → Tm (A `× B) Meta.≅ Tm A ⟪×⟫ Tm B

    _`→_ : Tp → Tp → Tp
    `→-sem : ∀ {A B} → Tm (A `→ B) Meta.≅ Tm A ⟪→⟫ Tm B

    ∅ : Ctx.Ob
    ∅-empty : is-terminal Ctx ∅
```

We can decompose the isomorphisms into all the expected rules of type theory

```agda 
  module ∅ = Terminal {C = Ctx} (record { top = ∅ ; has⊤ = ∅-empty })
  module `⊤-sem = Meta._≅_ `⊤-sem
  module `×-sem {A B} = Meta._≅_ (`×-sem {A} {B})
  module `→-sem {A B} = Meta._≅_ (`→-sem {A} {B})

  variable
    Γ Δ Ξ Θ : Ctx.Ob
    A B : Tp
    γ δ σ : Ctx.Hom Γ Δ
    x y : Δ ⊢ A
    f : Δ ⊢ (A `→ B)
    e : Δ ⨾ A ⊢ B

  _⨾ₛ_ : Ctx.Hom Γ Δ → Γ ⊢ A → Ctx.Hom Γ (Δ ⨾ A)
  γ ⨾ₛ e = ⨾-sem.from .η _ (γ , e)

  πₛ : Ctx.Hom Δ (Γ ⨾ A) → Ctx.Hom Δ Γ
  πₛ γ = ⨾-sem.to .η _ γ .fst

  `πₜ : Ctx.Hom Δ (Γ ⨾ A) → Δ ⊢ A
  `πₜ γ = ⨾-sem.to .η _ γ .snd

  ∅ₛ : Ctx.Hom Γ ∅
  ∅ₛ = ∅-empty _ .centre

  idₛ : Ctx.Hom Γ Γ
  idₛ = Ctx.id

  _∘ₛ_ : Ctx.Hom Δ Ξ → Ctx.Hom Γ Δ → Ctx.Hom Γ Ξ
  _∘ₛ_ = Ctx._∘_

  idrₛ : (γ ∘ₛ idₛ) ≡ γ
  idrₛ = Ctx.idr _

  idlₛ : (idₛ ∘ₛ γ) ≡ γ
  idlₛ = Ctx.idl _

  assocₛ : (γ ∘ₛ (δ ∘ₛ σ)) ≡ ((γ ∘ₛ δ) ∘ₛ σ)
  assocₛ = Ctx.assoc _ _ _

  πₛ-β : πₛ (γ ⨾ₛ x) ≡ γ
  πₛ-β = ap fst $ ⨾-sem.invl ηₚ _ $ₚ _

  ηₛ : πₛ γ ⨾ₛ `πₜ γ ≡ γ
  ηₛ = ⨾-sem.invr ηₚ _ $ₚ _

  πₛ-∘ : (πₛ σ ∘ₛ γ) ≡ πₛ (σ ∘ₛ γ)
  πₛ-∘ = sym (ap fst $ ⨾-sem.to .is-natural _ _ _ $ₚ _)
  
  ∅-η : ∅ₛ ≡ γ
  ∅-η = ∅.!-unique _

  `tt : Γ ⊢ `⊤
  `tt = `⊤-sem.from .η _ (lift tt)

  `⟨_,_⟩ : Γ ⊢ A → Γ ⊢ B → Γ ⊢ (A `× B)
  `⟨ a , b ⟩ = `×-sem.from .η _ (a , b)

  `π₁ : Γ ⊢ (A `× B) → Γ ⊢ A
  `π₁ p = fst $ `×-sem.to .η _ p
  
  `π₂ : Γ ⊢ (A `× B) → Γ ⊢ B
  `π₂ p = snd $ `×-sem.to .η _ p
 
  `λ : Γ ⨾ A ⊢ B → Γ ⊢ (A `→ B)
  `λ e = Y.from (`→-sem.from ∘nt ⟪λ⟫ (Y.to e ∘nt ⨾-sem.from))

  `ν : Γ ⊢ (A `→ B) → (Γ ⨾ A) ⊢ B
  `ν {A = A} f = Y.from (⟪ν⟫ (`→-sem.to ∘nt Y.to f) ∘nt ⨾-sem.to)

  [id] : x [ idₛ ] ≡ x
  [id] = Tm.F-id _ $ₚ _

  [∘] : x [ γ ∘ₛ δ ] ≡ x [ γ ] [ δ ]
  [∘] = Tm.F-∘ _ _ _ $ₚ _

  `πₜ-β : `πₜ (γ ⨾ₛ x) ≡ x
  `πₜ-β = ap snd $ ⨾-sem.invl ηₚ _ $ₚ _

  [`πₜ] : (`πₜ σ [ γ ]) ≡ `πₜ (σ ∘ₛ γ)
  [`πₜ] = sym (ap snd $ ⨾-sem.to .is-natural _ _ _ $ₚ _)

  `ν-β : `ν (`λ e) ≡ e
  `ν-β {e = e} =
    Y.from (⟪ν⟫ (`→-sem.to ∘nt ⌜ Y.to (Y.from (`→-sem.from ∘nt ⟪λ⟫ (Y.to e ∘nt ⨾-sem.from))) ⌝ ) ∘nt ⨾-sem.to) ≡⟨ ap! (Y.ε (`→-sem.from ∘nt ⟪λ⟫ (Y.to e ∘nt ⨾-sem.from))) ⟩
    Y.from (⟪ν⟫ (`→-sem.to ∘nt (`→-sem.from ∘nt ⟪λ⟫ (Y.to e ∘nt ⨾-sem.from))) ∘nt ⨾-sem.to) ≡⟨ trivial! ⟩
    Y.from (⟪ν⟫ (⌜ `→-sem.to ∘nt `→-sem.from ⌝ ∘nt ⟪λ⟫ (Y.to e ∘nt ⨾-sem.from)) ∘nt ⨾-sem.to) ≡⟨ ap! `→-sem.invl ⟩
    Y.from (⟪ν⟫ (idnt ∘nt ⟪λ⟫ (Y.to e ∘nt ⨾-sem.from)) ∘nt ⨾-sem.to) ≡⟨ trivial! ⟩
    Y.from (⌜ ⟪ν⟫ (⟪λ⟫ (Y.to e ∘nt ⨾-sem.from)) ⌝ ∘nt ⨾-sem.to) ≡⟨ ap! (⟪λ⟫-Equiv.η (Y.to e ∘nt ⨾-sem.from)) ⟩
    Y.from ((Y.to e ∘nt ⨾-sem.from) ∘nt ⨾-sem.to) ≡⟨ trivial! ⟩
    Y.from (Y.to e ∘nt ⌜ ⨾-sem.from ∘nt ⨾-sem.to ⌝) ≡⟨ ap! ⨾-sem.invr ⟩
    Y.from (Y.to e ∘nt idnt) ≡⟨ trivial! ⟩
    Y.from (Y.to e) ≡⟨ Y.η e ⟩
    e ∎




  ∘ₛ-⨾ₛ : ((γ ⨾ₛ x) ∘ₛ δ) ≡ ((γ ∘ₛ δ) ⨾ₛ (x [ δ ]))
  ∘ₛ-⨾ₛ = sym (⨾-sem.from .is-natural _ _ _ $ₚ (_ , _))

  [`λ] : ∀ {A B} {e : Δ ⨾ A ⊢ B} {γ : Ctx.Hom Γ Δ} → (`λ e) [ γ ] ≡ `λ (e [ (γ ∘ₛ πₛ idₛ) ⨾ₛ (`πₜ idₛ) ])
  [`λ] {Δ = Δ} {Γ = Γ} {A = A} {B = B} {e = e} {γ = γ} =
    Y.from α [ γ ] ≡⟨ from₁ _ (Tm _) γ α ⟩
    Y.from (`→-sem.from ∘nt ⌜ ⟪λ⟫ 𝕗 ∘nt よ₁ _ γ ⌝) ≡⟨ ap! prf₁ ⟩ 
    Y.from (`→-sem.from ∘nt ⟪λ⟫ 𝕗[]) ∎

    where
      𝕗 = Y.to e ∘nt ⨾-sem.from
      α = `→-sem.from ∘nt ⟪λ⟫ 𝕗
      
      𝕗[] = Y.to (e [ (γ ∘ₛ πₛ idₛ) ⨾ₛ (`πₜ idₛ) ]) ∘nt ⨾-sem.from
      α[] = `→-sem.from ∘nt ⟪λ⟫ 𝕗[]


      sub₁ : よ₀ Ctx (Γ ⨾ A) => よ₀ Ctx (Δ ⨾ A)
      sub₁ = よ₁ Ctx ((γ ∘ₛ πₛ idₛ) ⨾ₛ (`πₜ idₛ))

      prf₃ : sub₁ ∘nt ⨾-sem.from ≡ ⨾-sem.from ∘nt (よ₁ _ γ ⟪×⟫₁ idnt)
      prf₃ = ext λ Ξ δ x →
        ((γ ∘ₛ πₛ idₛ) ⨾ₛ `πₜ idₛ) ∘ₛ (δ ⨾ₛ x) ≡⟨ ∘ₛ-⨾ₛ ⟩ 
        ((γ ∘ₛ πₛ idₛ) ∘ₛ (δ ⨾ₛ x)) ⨾ₛ ⌜ `πₜ idₛ [ δ ⨾ₛ x ] ⌝ ≡⟨ ap! lemma₁ ⟩
        ⌜ (γ ∘ₛ πₛ idₛ) ∘ₛ (δ ⨾ₛ x) ⌝ ⨾ₛ x ≡⟨ ap! lemma₂ ⟩
        ((γ ∘ₛ δ) ⨾ₛ x) ∎
        where
          lemma₁ : `πₜ idₛ [ δ ⨾ₛ x ] ≡ x
          lemma₁ = [`πₜ] ∙ ap `πₜ idlₛ ∙ `πₜ-β

          lemma₂ : (γ ∘ₛ πₛ idₛ) ∘ₛ (δ ⨾ₛ x) ≡ γ ∘ₛ δ
          lemma₂ = pullr (πₛ-∘ ∙ (ap πₛ idlₛ) ∙ πₛ-β) 

      prf₂ : 𝕗 ∘nt (よ₁ _ γ ⟪×⟫₁ idnt) ≡ 𝕗[]
      prf₂ = sym $
        ⌜ Y.to (e [ (γ ∘ₛ πₛ idₛ) ⨾ₛ (`πₜ idₛ) ]) ⌝ ∘nt ⨾-sem.from ≡˘⟨ ap¡ (to₁ Ctx _ _ e) ⟩
        (Y.to e ∘nt (よ₁ _ ((γ ∘ₛ πₛ idₛ) ⨾ₛ (`πₜ idₛ)))) ∘nt ⨾-sem.from ≡⟨ trivial! ⟩
        Y.to e ∘nt ⌜ (よ₁ _ ((γ ∘ₛ πₛ idₛ) ⨾ₛ (`πₜ idₛ))) ∘nt ⨾-sem.from ⌝ ≡⟨ ap! prf₃ ⟩ 
        Y.to e ∘nt (⨾-sem.from ∘nt (よ₁ Ctx γ ⟪×⟫₁ idnt)) ≡⟨ trivial! ⟩
        (Y.to e ∘nt ⨾-sem.from) ∘nt (よ₁ Ctx γ ⟪×⟫₁ idnt) ∎

      prf₁ : ⟪λ⟫ 𝕗 ∘nt よ₁ _ γ ≡ ⟪λ⟫ 𝕗[]
      prf₁ = 
        ⟪λ⟫ 𝕗 ∘nt よ₁ _ γ ≡⟨ Exps.subst-comm _ _ _ _ ⟩
        ⟪λ⟫ ⌜ 𝕗 ∘nt (よ₁ _ γ ⟪×⟫₁ idnt) ⌝ ≡⟨ ap! prf₂ ⟩
        ⟪λ⟫ 𝕗[] ∎


  [`π₁] : (`π₁ x) [ γ ] ≡ `π₁ (x [ γ ])
  [`π₁] = sym (ap fst $ `×-sem.to .is-natural _ _ _ $ₚ _)

  [`π₂] : (`π₂ x) [ γ ] ≡ `π₂ (x [ γ ])
  [`π₂] = sym (ap snd $ `×-sem.to .is-natural _ _ _ $ₚ _)

  `π₁-β : `π₁ `⟨ x , y ⟩ ≡ x 
  `π₁-β = ap fst $ `×-sem.invl ηₚ _ $ₚ _

  `π₂-β : `π₂ `⟨ x , y ⟩ ≡ y
  `π₂-β = ap snd $ `×-sem.invl ηₚ _ $ₚ _

  `×-η : `⟨ `π₁ x , `π₂ x ⟩ ≡ x
  `×-η = `×-sem.invr ηₚ _ $ₚ _

  `⊤-η : `tt ≡ x
  `⊤-η = `⊤-sem.invr ηₚ _ $ₚ _

  `→-η : `λ (`ν f) ≡ f
  `→-η {f = f} = 
    Y.from (`→-sem.from ∘nt ⟪λ⟫ (⌜ Y.to (Y.from ((⟪ν⟫ (`→-sem.to ∘nt Y.to f)) ∘nt ⨾-sem.to)) ⌝ ∘nt ⨾-sem.from)) ≡⟨ ap! (Y.ε (⟪ν⟫ (`→-sem.to ∘nt Y.to f) ∘nt ⨾-sem.to)) ⟩
    Y.from (`→-sem.from ∘nt ⟪λ⟫ ⌜ ((⟪ν⟫ (`→-sem.to ∘nt Y.to f)) ∘nt ⨾-sem.to) ∘nt ⨾-sem.from ⌝) ≡⟨ ap! (C^.cancelr ⨾-sem.invl) ⟩
    Y.from (`→-sem.from ∘nt ⌜ ⟪λ⟫ (⟪ν⟫ (`→-sem.to ∘nt Y.to f)) ⌝) ≡⟨ ap! (⟪λ⟫-Equiv.ε (`→-sem.to ∘nt Y.to f)) ⟩
    Y.from ⌜ `→-sem.from ∘nt (`→-sem.to ∘nt Y.to f) ⌝ ≡⟨ ap! {y = Y.to f} (C^.cancell `→-sem.invr) ⟩
    Y.from (Y.to f) ≡⟨ Y.η f ⟩
    f ∎

  tm-set : is-set (Γ ⊢ A)
  tm-set {Γ = Γ} {A = A} = Tm.₀ A Γ .is-tr


    
record Strict-model o h : Type (lsuc (o ⊔ h)) where
  no-eta-equality
  field
    model : Natural-model o h
  module Model = Natural-model model
  
  field
    has-is-strict : is-set Model.Ob
  
  instance
    ob-set : ∀ {n} → H-Level Model.Ob (2 + n)
    ob-set = basic-instance 2 has-is-strict
  open Model public


instance
  open hlevel-projection
  
  decomp-Tp : hlevel-projection (quote Natural-model.Tp)
  decomp-Tp .has-level = quote Natural-model.Tp-set
  decomp-Tp .get-level _ = pure (lit (nat 2))
  decomp-Tp .get-argument (_ ∷ _ ∷ arg _ t ∷ _) = pure t
  decomp-Tp .get-argument _ = typeError []

record Strict-model-hom {o h} (N M : Strict-model o h) : Type (o ⊔ h) where
  no-eta-equality
  private
    module N = Strict-model N
    module M = Strict-model M
  field
    F : Functor N.Ctx M.Ctx

  private module F = Functor F


  field

    F-tp : N.Tp → M.Tp
    F-tm : (A : N.Tp) → N.Tm A => M.Tm (F-tp A) F∘ F.op

    pres-∅ : F.₀ N.∅ ≡ M.∅
    pres-⨾ : ∀ {Γ A} → F.₀ (Γ N.⨾ A) ≡ ((F.₀ Γ) M.⨾ F-tp A)

    pres-`⊤ : F-tp N.`⊤ ≡ M.`⊤
    pres-`× : ∀ {A B} → F-tp (A N.`× B) ≡ (F-tp A M.`× F-tp B)
    pres-`→ : ∀ {A B} → F-tp (A N.`→ B) ≡ (F-tp A M.`→ F-tp B)
    
  open F public
    -- Functors always preserve isos, so no need to explicitly require this

private 
  unquoteDecl eqv = declare-record-iso eqv (quote Strict-model-hom)
  module Eqv {o h} {N M : Strict-model o h} = Equiv (Iso→Equiv (eqv {o} {h} {N} {M}))
    
  funextP' : ∀ {ℓ ℓ₁} {A : Type ℓ} {B : A → I → Type ℓ₁}
    → {f : ∀ {a} → B a i0} {g : ∀ {a} → B a i1}
    → (∀ a → PathP (B a) (f {a}) (g {a}))
    → PathP (λ i → ∀ {a} → B a i) (λ {a} → f {a}) (λ {a} → g {a})
  funextP' p i {x} = p x i

abstract
  Strict-model-hom-path : 
    ∀ {o h} {N M : Strict-model o h} 
      {f g : Strict-model-hom N M}
      (let module N = Strict-model N)
      (let module M = Strict-model M)
      (let module f = Strict-model-hom f)
      (let module g = Strict-model-hom g)
    → (p : f.F ≡ g.F)
    → (q : f.F-tp ≡ g.F-tp)
    → (∀ A Δ x → PathP (λ i → ⌞ M.Tm (q i A) .F₀ ((p i) .F₀ Δ) ⌟) (f.F-tm A .η Δ x) (g.F-tm A .η Δ x))
    → f ≡ g
  Strict-model-hom-path {M = M} a b c = Eqv.injective $ 
    Σ-pathp a $ 
    Σ-pathp b $
    Σ-pathp (funextP λ A → Nat-pathp refl _ λ Δ → funextP λ x → c A Δ x) $
    prop!
    where
      module M = Strict-model M
    
```                    

open import Cat.Displayed.Cartesian
open import Cat.Displayed.Cartesian.Discrete
open import Cat.Displayed.Functor
open import Cat.Prelude
open import Cat.Displayed.Base
open import Cat.Diagram.Product
open import Cat.Diagram.Terminal
open import Cat.Displayed.Instances.Product
open import Cat.Displayed.Instances.Identity
open import Cat.Displayed.Instances.Lift
open import Cat.Diagram.Exponential
open import Cat.Displayed.Total
open import Cat.Displayed.Instances.Pullback
open import Cat.Instances.StrictDisplayed
open import Cat.Functor.FullSubcategory
open import Cat.Functor.Base
open import 1Lab.Univalence
open import Cat.Displayed.Reasoning as DR
open import Cat.Displayed.Fibre
open import Cat.Instances.StrictCat
open import Cat.Displayed.Cartesian.Indexing

import Cat.Functor.Bifunctor 

import Cat.Reasoning


module Cat.Displayed.Cartesian.DCF where


open is-discrete-cartesian-fibration


module _ 
  {ob ℓb od ℓd oe ℓe}
  {B : Precategory ob ℓb}
  {D : Displayed B od ℓd} {E : Displayed B oe ℓe}
  where
  private
    module B = Precategory B
    module D = Displayed D
    module E where
      open Displayed E public
      open DR E public

  open Functor
  open Displayed-functor 
  

  -- lemma : Vertical-functor D E ≃ (∀ x → Functor (Fibre D x) (Fibre E x))
  -- lemma = Iso→Equiv eqv where

  --   to : Vertical-functor D E → (∀ x → Functor (Fibre D x) (Fibre E (F.₀ x)))
  --   to F' x .F₀ = F' .F₀'
  --   to F' x .F₁ f = E.hom[ F.F-id ] (F' .F₁' f)
  --   to F' x .F-id = {!   !}
  --   to F' x .F-∘ = {!   !}
    
  --   eqv : Iso _ _
  --   eqv .fst = {!   !}
  --   eqv .snd = {!   !}

module _ {o ℓ} (B : Precategory o ℓ) o' ℓ' where
  private module B = Precategory B

  DCF : Precategory _ _
  DCF .Precategory.Ob = Σ (Displayed B o' ℓ') is-discrete-cartesian-fibration
  DCF .Precategory.Hom (D , _) (E , _) = ∀ x → Functor (Fibre D x) (Fibre E x) -- Vertical-functor D E
  DCF .Precategory.Hom-set _ (_ , E*) = Π-is-hlevel 2 (λ  _ → Functor-is-set (E* .fibre-set _)) -- Vertical-functor-is-set (E* .fibre-set)
  DCF .Precategory.id _ = Id -- Id'
  DCF .Precategory._∘_ f g x = f x F∘ g x -- _∘V_
  DCF .Precategory.idr _ = funext λ x → Functor-path (λ _ → refl) (λ _ → refl) -- ∘V-idr _
  DCF .Precategory.idl _ = funext λ x → Functor-path (λ _ → refl) (λ _ → refl) -- ∘V-idl _
  DCF .Precategory.assoc _ _ _ = funext λ x → Functor-path (λ _ → refl) (λ _ → refl)  -- ∘V-assoc _ _ _

  module _ o'' ℓ'' where
    Poly : Displayed DCF _ _
    Poly .Displayed.Ob[_] (D , _) = ∀ x → Σ (Displayed (Fibre D x) o'' ℓ'') is-discrete-cartesian-fibration
    Poly .Displayed.Hom[_]  f D' E' = ∀ x → Displayed-functor (f x) (D' x .fst) (E' x .fst)
    Poly .Displayed.Hom[_]-set _ _ E'* = Π-is-hlevel 2 (λ x → Displayed-functor-is-set (E'* x .snd .fibre-set)) -- Displayed-functor-is-set (E'* .fibre-set)
    Poly .Displayed.id' x = Id' -- F∫Id'
    Poly .Displayed._∘'_ f g x = (f x) F∘' g x -- _F∫∘V_
    Poly .Displayed.idr' f = funextP λ x → Displayed-functor-pathp _ (λ _ → refl) (λ _ → refl) -- Displayed-functor-pathp _ (λ _ → refl) (λ _ → refl)
    Poly .Displayed.idl' f = funextP λ x → Displayed-functor-pathp _ (λ _ → refl) (λ _ → refl) -- Displayed-functor-pathp _ (λ _ → refl) (λ _ → refl)
    Poly .Displayed.assoc' _ _ _ = funextP λ x → Displayed-functor-pathp _ (λ _ → refl) (λ _ → refl) -- Displayed-functor-pathp _ (λ _ → refl) (λ _ → refl)

module DCF {o ℓ o' ℓ'} {B : Precategory o ℓ} ((x , x*) : Σ (Displayed B o' ℓ') is-discrete-cartesian-fibration) where
  Fib = x
  Fib* = x*
  open Displayed x public
  open DR x public
  open is-discrete-cartesian-fibration x* public


module _ {o ℓ o' ℓ' o'' ℓ''} {B : Precategory o ℓ}  where

  open Cartesian-lift
  open is-cartesian
  open Functor
  open Displayed-functor

  Poly-cartesian : Cartesian-fibration (Poly B o' ℓ' o'' ℓ'')
  Poly-cartesian f y' .x' x = Change-of-base (f x) (y' x .fst) , Change-of-base-discrete-fibration _ _ (y' x .snd)
  Poly-cartesian f y' .lifting x = Change-of-base-functor _ _
  Poly-cartesian f y' .cartesian .universal {u' = u'} m h' x = F where
    module y' = DCF (y' x)
    F : Displayed-functor (m x) (u' x .fst) (Change-of-base (f x) (y' x .fst))
    F .F₀' = h' x .F₀'
    F .F₁' = h' x .F₁'
    F .F-id' = is-prop→pathp (λ _ → hlevel 1) _ _
    F .F-∘' = is-prop→pathp (λ _ → hlevel 1) _ _
  Poly-cartesian f y' .cartesian .commutes m h' = funext λ _ → Displayed-functor-pathp _ (λ _ → refl) (λ _ → refl)
  Poly-cartesian f y' .cartesian .unique m' p = funext λ x → Displayed-functor-pathp _ (λ x'' → ap (λ z → z x .F₀' x'') p) (λ f' → apd (λ _ z → z x .F₁' f') p)
  


module Poly {o ℓ} (B : Precategory o ℓ) o' ℓ' o'' ℓ'' where
  open Displayed (Poly B o' ℓ' o'' ℓ'') public
  open Cartesian-fibration (Poly B o' ℓ' o'' ℓ'') Poly-cartesian public


--   Poly-cartesian : Cartesian-fibration (Poly B o' ℓ' o'' ℓ'')
--   Poly-cartesian f (y' , y'*) .x' = Change-of-base (F∫ f) y' , Change-of-base-discrete-fibration _ _ y'*
--   Poly-cartesian f (y' , _) .lifting = Change-of-base-functor (F∫ f) y'
--   Poly-cartesian f (y' , y'*) .cartesian .universal {u' = u' , _} g F' = F where
--     module F' = Displayed-functor F'
--     module y' = DCF (y' , y'*)
--     F : Displayed-functor (F∫ g) u' (Change-of-base (F∫ f) y')
--     F .F₀' = F'.F₀'
--     F .F₁' = F'.F₁'
--     F .F-id' = is-prop→pathp (λ i → hlevel 1) _ _
--     F .F-∘' = is-prop→pathp (λ i → hlevel 1) _ _

--   Poly-cartesian f y' .cartesian .commutes _ _ = 
--     Displayed-functor-pathp refl (λ _ → refl) (λ _ → refl)
--   Poly-cartesian f y' .cartesian .unique _ p = 
--     Displayed-functor-pathp refl (λ x'' → ap (λ z → z .F₀' x'') p) (λ f' → apd (λ _ z → z .F₁' f') p)












-- module _ {o' l'} where
--   private module DCF = Cat.Reasoning (DCF o' l')

--   -- Let's re-implement presheaf stuff but using discrete fibrations

--   DCF-terminal : Terminal (DCF o' l')
--   DCF-terminal .Terminal.top = LiftD (IdD B) _ _ , record { fibre-set = λ _ → hlevel 2 ; cart-lift = λ _ _ → hlevel 0 }
--   DCF-terminal .Terminal.has⊤ (E , E*) .centre = dcf-hom $ λ where
--     .Displayed-functor.F₀' _ → lift tt
--     .Displayed-functor.F₁' _ → lift tt
--     .Displayed-functor.F-id' → refl
--     .Displayed-functor.F-∘' → refl
--   DCF-terminal .Terminal.has⊤ (E , E*) .paths v = DCF-Hom-path (λ _ → refl) λ _ → refl

--   DCF-has-products : has-products (DCF o' l')
--   DCF-has-products (D , D*) (E , E*) .Product.apex = D D× E , D×E* D* E*
--   DCF-has-products D E .Product.π₁ = dcf-hom Fst'
--   DCF-has-products D E .Product.π₂ = dcf-hom Snd'
--   DCF-has-products D E .Product.has-is-product .is-product.⟨_,_⟩ (dcf-hom p1) (dcf-hom p2) = dcf-hom (Pair' p1 p2)
--   DCF-has-products D E .Product.has-is-product .is-product.π₁∘⟨⟩ = DCF-Hom-path (λ _ → refl) (λ _ → refl)
--   DCF-has-products D E .Product.has-is-product .is-product.π₂∘⟨⟩ = DCF-Hom-path (λ _ → refl) (λ _ → refl)
--   DCF-has-products D E .Product.has-is-product .is-product.unique α β = 
--     DCF-Hom-path
--       (λ x' → ap (λ (dcf-hom q) → q .F₀' x') α ,ₚ ap (λ (dcf-hom q) → q .F₀' x') β) 
--       (λ f' → ap (λ (dcf-hom q) → q .F₁' f') α ,ₚ ap (λ (dcf-hom q) → q .F₁' f') β)
--       where open Vertical-functor
  

-- よ₀ : B.Ob → Displayed B _ _
-- よ₀ a .Displayed.Ob[_] b = B.Hom b a
-- よ₀ a .Displayed.Hom[_] f g h = h B.∘ f ≡ g
-- よ₀ a .Displayed.Hom[_]-set _ _ _ = hlevel 2
-- よ₀ a .Displayed.id' = B.idr _
-- よ₀ a .Displayed._∘'_ p q = B.pulll p ∙ q
-- よ₀ a .Displayed.idr' _ = is-prop→pathp (λ _ → hlevel 1) _ _
-- よ₀ a .Displayed.idl' _ = is-prop→pathp (λ _ → hlevel 1) _ _
-- よ₀ a .Displayed.assoc' _ _ _ = is-prop→pathp (λ _ → hlevel 1) _ _

-- よ₀* : ∀ x → is-discrete-cartesian-fibration (よ₀ x)
-- よ₀* a .fibre-set _ = hlevel 2
-- よ₀* a .cart-lift {x = x} f y' .centre = y' B.∘ f , refl
-- よ₀* a .cart-lift {x = x} f y' .paths (g , p) = Σ-prop-path! p

-- よ₁ : ∀ {a b} → B.Hom a b → Vertical-functor (よ₀ a) (よ₀ b)
-- よ₁ f .Displayed-functor.F₀' x' = f B.∘ x'
-- よ₁ f .Displayed-functor.F₁' g' = B.pullr g'
-- よ₁ f .Displayed-functor.F-id' = hlevel 1 _ _
-- よ₁ f .Displayed-functor.F-∘' = hlevel 1 _ _

-- よ : Functor B (DCF ℓ ℓ)
-- よ .Functor.F₀ x = よ₀ x , よ₀* x
-- よ .Functor.F₁ f = dcf-hom (よ₁ f) 
-- よ .Functor.F-id = DCF-Hom-path B.idl (λ f' → is-prop→pathp (λ _ → hlevel 1) _ _) 
-- よ .Functor.F-∘ f g = DCF-Hom-path (λ _ → sym (B.assoc _ _ _)) (λ f' → is-prop→pathp (λ _ → hlevel 1) _ _)

-- module よ = Functor よ

-- private module DCF = Cat.Reasoning (DCF ℓ ℓ)
-- module _ (D E : DCF.Ob) where
--   private module D where
--     open Displayed (D .fst) public
--     open is-discrete-cartesian-fibration (D .snd) public
    
--   private module E where
--     open Displayed (E .fst) public
--     open is-discrete-cartesian-fibration (E .snd) public

--   open Binary-products (DCF ℓ ℓ) DCF-has-products
--   open Cat.Functor.Bifunctor ×-functor

--   DCF[_,_] : Displayed B _ _
--   DCF[_,_] .Displayed.Ob[_] Γ = DCF.Hom (よ.₀ Γ ⊗₀ D) E
--   DCF[_,_] .Displayed.Hom[_] f x' y' = y' DCF.∘ first (よ.₁ f) ≡ x'
--   DCF[_,_] .Displayed.Hom[_]-set _ _ _ = hlevel 2
--   DCF[_,_] .Displayed.id' = DCF.elimr (ap first よ.F-id ∙ first-id)
--   DCF[_,_] .Displayed._∘'_ {b = b} {x = x} {y = y} {z = z} {f = f} {g = g} f' g' =
--       z DCF.∘ first ⌜ よ.₁ (f B.∘ g) ⌝ ≡⟨ ap! (よ.F-∘ f g) ⟩
--       z DCF.∘ ⌜ first (よ.₁ f DCF.∘ よ.₁ g) ⌝ ≡⟨ ap! (first∘first {b = よ.₀ b}) ⟩
--       z DCF.∘ (first (よ.₁ f) DCF.∘ first (よ.₁ g)) ≡⟨ DCF.pulll {b = first (よ.₁ f)} f' ⟩
--       y DCF.∘ first (よ.₁ g) ≡⟨ g' ⟩
--       x ∎
--   DCF[_,_] .Displayed.idr' _ = is-prop→pathp (λ i → hlevel 1) _ _
--   DCF[_,_] .Displayed.idl' _ = is-prop→pathp (λ i → hlevel 1) _ _
--   DCF[_,_] .Displayed.assoc' _ _ _ = is-prop→pathp (λ i → hlevel 1) _ _


--   DCF[_,_]* : is-discrete-cartesian-fibration DCF[_,_]
--   DCF[_,_]* .fibre-set x = hlevel 2
--   DCF[_,_]* .cart-lift f y' .centre = y' DCF.∘ first (よ.₁ f) , refl  
--   DCF[_,_]* .cart-lift f y' .paths (x , x') = Σ-prop-path! x'

-- -- DCF-CC : Cartesian-closed (DCF ℓ ℓ) DCF-has-products DCF-terminal
-- -- DCF-CC .Cartesian-closed.has-exp D E .Exponential.B^A = {!   !}
-- -- DCF-CC .Cartesian-closed.has-exp D E .Exponential.ev = {!   !}
-- -- DCF-CC .Cartesian-closed.has-exp D E .Exponential.has-is-exp = {!   !}
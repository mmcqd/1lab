
<!--
```agda
open import Cat.Prelude

open import Cat.Functor.Subcategory
open import Order.DCPO
open import Order.Base
open import Cat.Diagram.Coproduct
open import Cat.Diagram.Coproduct.Indexed
open import Cat.Diagram.Initial
open import Order.Instances.Coproduct
open import Data.Sum

open import Order.Instances.Disjoint

import Order.Diagram.Lub
import Order.Reasoning


```
-->


```agda

module Order.DCPO.Coproduct where

```


<!--
```agda
_ = DCPOs
``` 
-->

# Products of DCPOs

We show that `DCPOs`{.Agda} has all finite coproducts


```agda
module _ {o ℓ κ} (I : Set κ) (F : ⌞ I ⌟ → DCPO (o ⊔ κ) (ℓ ⊔ κ)) where
  private

    Fᵖ = fst ⊙ F

    open is-dcpo
    
    module F {i : ⌞ I ⌟} where
      open DCPO (F i) public
      open Order.Diagram.Lub poset public
      open Lub public
      open is-lub public
    
    module ΣF where
      open Order.Reasoning (Disjoint I Fᵖ) public
      open Order.Diagram.Lub (Disjoint I Fᵖ) public
      open Indexed-coproduct (Posets-has-set-indexed-coproducts {o} {ℓ} I Fᵖ) public
      open Lub public
      open is-lub public

    
    Disjoint-is-dcpo : is-dcpo (Disjoint I (Fᵖ))
    Disjoint-is-dcpo .directed-lubs f x = {!   !}

```

-- ```agda

-- module _ {o ℓ} (D E : DCPO o ℓ) where

--   open Initial
--   open is-directed-family
--   open is-dcpo
  
--   private
--     module D where
--       open DCPO D public
--       open Order.Diagram.Lub poset public
--       open Lub public
--       open is-lub public

--     module E where
--       open DCPO E public
--       open Order.Diagram.Lub poset public
--       open Lub public
--       open is-lub public


--     module D⊎ᵖE where
--       open Order.Reasoning (D.poset ⊎ᵖ E.poset) public
--       open Order.Diagram.Lub (D.poset ⊎ᵖ E.poset) public
--       open Coproduct (Posets-has-coproducts D.poset E.poset) public
--       open Lub public
--       open is-lub public
      
--   _⊎ᵖ_is-dcpo : is-dcpo (D.poset ⊎ᵖ E.poset)
--   _⊎ᵖ_is-dcpo .directed-lubs {Ix = Ix} f dir = ∥-∥-rec₂! ⊎ᵖ-Lub (dir .elt) (⊎-directed→one-sided-directed dir)
--     where module _ (i : Ix) where
--       open D⊎ᵖE

--       ⊎ᵖ-Lub : is-one-sided-directed {P = D.poset} {Q = E.poset} f → Lub f
--       ⊎ᵖ-Lub (inl (f , f-dir , f-inl)) .lub = inl (D.⋃ _ f-dir)
--       ⊎ᵖ-Lub (inl (f , f-dir , f-inl)) .has-lub .fam≤lub i = (sym $ happly f-inl i) ▶ D.fam≤⋃ f f-dir i
--       ⊎ᵖ-Lub (inl (f , f-dir , f-inl)) .has-lub .least (inl ub') le = D.⋃-least f f-dir ub' λ j → happly f-inl j ▶ le j
--       ⊎ᵖ-Lub (inl (f , f-dir , f-inl)) .has-lub .least (inr ub') le = absurd* (happly f-inl i ▶ le i)
      
--       ⊎ᵖ-Lub (inr (g , g-dir , g-inr)) .lub = inr (E.⋃ _ g-dir)
--       ⊎ᵖ-Lub (inr (g , g-dir , g-inr)) .has-lub .fam≤lub i = (sym $ happly g-inr i) ▶ E.fam≤⋃ g g-dir i
--       ⊎ᵖ-Lub (inr (g , g-dir , g-inr)) .has-lub .least (inl ub') le = absurd* (happly g-inr i ▶ le i)
--       ⊎ᵖ-Lub (inr (g , g-dir , g-inr)) .has-lub .least (inr ub') le = E.⋃-least g g-dir ub' λ j → happly g-inr j ▶ le j


--   DCPOs-has-coproducts : Coproduct (DCPOs _ _) D E
--   DCPOs-has-coproducts = coprod
--     where
--       open Coproduct
--       open is-coproduct
--       open D⊎ᵖE
--       open Subcat-hom
      
--       coprod : Coproduct (DCPOs _ _) D E
--       coprod .coapex .fst = D.poset ⊎ᵖ E.poset
--       coprod .coapex .snd = _⊎ᵖ_is-dcpo
--       coprod .in₀ = to-scott-directed inl λ where 
--         s dir x lub .fam≤lub → lub .D.fam≤lub
--         s dir x lub .least (inl ub') le → lub .D.least ub' le
--         s dir x lub .least (inr ub') le → absurd {A = Lift _ ⊥} (∥-∥-rec! (λ i → le i .Lift.lower) (dir .elt))
        
--       coprod .in₁ = to-scott-directed inr λ where
--         s dir x lub .fam≤lub → lub .E.fam≤lub
--         s dir x lub .least (inl ub') le → absurd {A = Lift _ ⊥} (∥-∥-rec! (λ i → le i .Lift.lower) (dir .elt))
--         s dir x lub .least (inr ub') le → lub .E.least ub' le
        
--       coprod .has-is-coproduct .is-coproduct.[_,_] {Q = Q} f g = 
--         to-scott-directed case λ s dir lub il → ∥-∥-rec₂! (λ i dir' → to-lub i s dir lub il dir') (dir .elt) (⊎-directed→one-sided-directed dir)
--           where 
--             module Q where
--               open DCPO Q public
--               open Order.Diagram.Lub poset public
            
--             Case = Matchᵖ (f .hom) (g .hom)
--             case = apply Case
--             case-≤ = Case .pres-≤
            
--             to-lub : {Ix : Type o} → Ix → ∀ s dir lub il → is-one-sided-directed {P = D.poset} {Q = E.poset} s → Q.is-lub (case ⊙ s) (case lub)
--             to-lub i s dir (inl lub) il (inl (h , _ , h-inl)) .fam≤lub j = case-≤ {x = s j} {y = inl lub} (il .fam≤lub j)
--             to-lub i s dir (inl lub) il (inl (h , _ , h-inl)) .least ub' il' = {!   !}

--             to-lub i s dir (inl lub) il (inr (h , _ , h-inr)) .fam≤lub j = absurd* (happly h-inr j ▶ il .fam≤lub j)
--             to-lub i s dir (inl lub) il (inr (h , _ , h-inr)) .least ub' = {!  !}
--             to-lub i s dir (inr lub) il one-side .fam≤lub = {!   !}
--             to-lub i s dir (inr lub) il one-side .least = {!   !}
--               -- to-lub (inl (f , f-dir , f-inl)) .fam≤lub j with s j | recall s j
--               -- ... | inl x | ⟪ eq ⟫ = {!   !}
--               -- ... | inr x | ⟪ eq ⟫ = absurd (inl≠inr (sym (happly f-inl j) ∙ eq))
--               -- to-lub (inl (f , f-dir , f-inl)) .least = {!   !}
--               -- to-lub (inr x) = {!   !}
            


--         -- to-scott-directed (Matchᵖ (f .hom) (g .hom) .hom) λ {Ix} s dir x lub → ∥-∥-rec₂! (λ i → to-lub {Ix} i s dir x lub) (dir .elt) (⊎-directed→one-sided-directed {s = s} dir)
--         -- where
--         --   module Q where
--         --     open DCPO Q public
--         --     open Order.Diagram.Lub poset public

--         --   to-lub : {Ix : Type o} (i : Ix) → ∀ s dir x lub → is-one-sided-directed s → _
--         --   to-lub i s dir (inl x) lub w .fam≤lub j = Matchᵖ (f .hom) (g .hom) .pres-≤ {s j} {inl x} (lub .fam≤lub j)
--         --   to-lub i s dir (inl x) lub (inl all , all-dir) .least ub' le = {!  !}
--         --     where

--         --       lemma : f # all i .fst Q.≤ ub'
--         --       lemma = ap (Matchᵖ (f .hom) (g .hom) .hom) (all i .snd) Q.▶ le i

--         --   to-lub i s dir (inl x) lub (inr all , all-dir) .least ub' le = {!   !}
--         --   to-lub i s dir (inr x) lub w = {!   !}
          
--       coprod .has-is-coproduct .in₀∘factor = {!   !}
--       coprod .has-is-coproduct .in₁∘factor = {!   !}
--       coprod .has-is-coproduct .unique = {!   !}
  

--   DCPOs-initial : Initial (DCPOs o ℓ)
--   DCPOs-initial .bot .fst = Posets-initial .bot
--   DCPOs-initial .bot .snd .directed-lubs f dir = ∥-∥-rec! (λ i → absurd (f i .Lift.lower)) (dir .elt)
--     where open Order.Diagram.Lub (𝟘ᵖ {o} {ℓ})
--   DCPOs-initial .has⊥ x .centre = to-scott-directed (λ ()) λ s dir _ _ → ∥-∥-rec! (λ i → absurd (s i .Lift.lower)) (dir .elt) 
--     where open Order.Diagram.Lub (x .fst)
--   DCPOs-initial .has⊥ x .paths f = ext λ ()
-- ```
             
                
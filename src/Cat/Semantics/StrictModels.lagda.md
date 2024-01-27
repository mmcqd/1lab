```agda

open import Cat.Prelude
open import Cat.Semantics.NaturalModel
open import Cat.Instances.StrictCat
open import Cat.Functor.Base
open import Cat.Instances.Functor
open import Cat.Functor.Solver
import Cat.Morphism

open Precategory
open Functor
open _=>_
open Model-hom

module Cat.Semantics.StrictModels where


private unquoteDecl eqv = declare-record-iso eqv (quote Model-hom)
-- module Eqv {o h} {N M : Natural-model o h} = Equiv (Iso→Equiv (eqv {o} {h} {N} {M}))

M-id : ∀ {o h} {M : Natural-model o h} → Model-hom M M
M-id {M = M} = hom where
  module M = Natural-model M
  hom : Model-hom _ _
  hom .F = Id
  hom .F-tp A = A
  hom .F-tm A .η Δ x = x
  hom .F-tm A .is-natural Δ Γ γ = refl
  hom .pres-∅ = M.id-iso
  hom .pres-⨾ = M.id-iso
  hom .pres-`⊤ = refl
  hom .pres-`× = refl
  hom .pres-`→ = refl

_M∘_ : ∀ {o h} {N M L : Natural-model o h} → Model-hom N M → Model-hom M L → Model-hom N L
_M∘_ {N = N} {M = M} {L = L} f g = hom where
  module N = Natural-model N
  module M = Natural-model M
  module L = Natural-model L
  module f = Model-hom f
  module g = Model-hom g
    
  hom : Model-hom _ _
  hom .F = g.F F∘ f.F
  hom .F-tp = g.F-tp ⊙ f.F-tp
  hom .F-tm A .η Δ x = g.F-tm (f.F-tp A) .η _ (f.F-tm A .η _ x)
  hom .F-tm A .is-natural Δ Γ γ = ext λ x → (ap (g.F-tm (f.F-tp A) .η (f.₀ Γ)) (f.F-tm A .is-natural _ _ γ #ₚ x)) ∙ (g.F-tm (f.F-tp A) .is-natural _ _ (f.₁ γ) #ₚ f .F-tm A .η Δ x)
  hom .pres-∅ = (F-map-iso g.F f.pres-∅) L.∘Iso g.pres-∅
  hom .pres-⨾ = F-map-iso g.F f.pres-⨾ L.∘Iso g.pres-⨾
  hom .pres-`⊤ = (ap g.F-tp f.pres-`⊤) ∙ g.pres-`⊤
  hom .pres-`× = (ap g.F-tp f.pres-`×) ∙ g.pres-`×
  hom .pres-`→ = (ap g.F-tp f.pres-`→) ∙ g.pres-`→

M-idl : ∀ {o h} {N M : Natural-model o h} (f : Model-hom N M) → M-id M∘ f ≡ f
M-idl {M = M} f = Model-hom-path F∘-idr refl (λ A Δ x → refl) (M.elimr (f .F .F-id)) λ Δ A → M.elimr (f .F .F-id) where
  module M = Natural-model M

M-idr : ∀ {o h} {N M : Natural-model o h} (f : Model-hom N M) → f M∘ M-id ≡ f
M-idr {M = M} f = Model-hom-path F∘-idl refl (λ A Δ x → refl) (M.idl _) λ Δ A → M.idl _ where
  module M = Natural-model M

M-assoc : ∀ {o h} {N M L K : Natural-model o h} (f : Model-hom N M) (g : Model-hom M L) (h : Model-hom L K) → (f M∘ g) M∘ h ≡ f M∘ (g M∘ h)
M-assoc {K = K} f g h = Model-hom-path F∘-assoc refl (λ A Δ x → refl) (K.pushr (h.F-∘ _ _)) λ Δ A → K.pushr (h.F-∘ _ _) where
  module h = Model-hom h
  module K = Natural-model K

Model-hom-is-set : ∀ {o h} {N : Natural-model o h} {M : Natural-model o h} → is-set (M .Natural-model.Ctx .Ob) → is-set (Model-hom N M)
Model-hom-is-set {N = N} {M} Ob-set = Iso→is-hlevel 2 eqv $
  Σ-is-hlevel 2 (Functor-is-set Ob-set) λ _ → hlevel!
  where
    module N = Natural-model N
    module M = Natural-model M

Strict-models : ∀ o h → Precategory _ _
Strict-models o h .Ob = Σ[ M ∈ Natural-model o h ] is-set (M .Natural-model.Ctx .Ob)
Strict-models o h .Hom (N , _) (M , _) = Model-hom N M
Strict-models o h .Hom-set (N , _) (M , M-strict) = Model-hom-is-set M-strict
Strict-models o h .id = M-id
Strict-models o h ._∘_ f g = g M∘ f
Strict-models o h .idr = M-idl
Strict-models o h .idl = M-idr
Strict-models _ _ .assoc f g h = M-assoc _ _ _

   
``` 
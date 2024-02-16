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
open Strict-model-hom

module Cat.Semantics.StrictModels where

M-id : ∀ {o h} {M : Strict-model o h} → Strict-model-hom M M
M-id {M = M} = hom where
  module M = Strict-model M
  hom : Strict-model-hom _ _
  hom .F = Id
  hom .F-tp A = A
  hom .F-tm A .η Δ x = x
  hom .F-tm A .is-natural Δ Γ γ = refl
  hom .pres-∅ = refl
  hom .pres-⨾ = refl
  hom .pres-`⊤ = refl
  hom .pres-`× = refl
  hom .pres-`→ = refl

_M∘_ : ∀ {o h} {N M L : Strict-model o h} → Strict-model-hom N M → Strict-model-hom M L → Strict-model-hom N L
_M∘_ {N = N} {M = M} {L = L} f g = hom where
  module N = Strict-model N
  module M = Strict-model M
  module L = Strict-model L
  module f = Strict-model-hom f
  module g = Strict-model-hom g
    
  hom : Strict-model-hom _ _
  hom .F = g.F F∘ f.F
  hom .F-tp = g.F-tp ⊙ f.F-tp
  hom .F-tm A .η Δ x = g.F-tm (f.F-tp A) .η _ (f.F-tm A .η _ x)
  hom .F-tm A .is-natural Δ Γ γ = ext λ x → (ap (g.F-tm (f.F-tp A) .η (f.₀ Γ)) (f.F-tm A .is-natural _ _ γ #ₚ x)) ∙ (g.F-tm (f.F-tp A) .is-natural _ _ (f.₁ γ) #ₚ f .F-tm A .η Δ x)
  hom .pres-∅ = (ap g.₀ f.pres-∅) ∙ g.pres-∅
  hom .pres-⨾ = (ap g.₀ f.pres-⨾) ∙ g.pres-⨾
  hom .pres-`⊤ = (ap g.F-tp f.pres-`⊤) ∙ g.pres-`⊤
  hom .pres-`× = (ap g.F-tp f.pres-`×) ∙ g.pres-`×
  hom .pres-`→ = (ap g.F-tp f.pres-`→) ∙ g.pres-`→



M-idl : ∀ {o h} {N M : Strict-model o h} (f : Strict-model-hom N M) → M-id M∘ f ≡ f
M-idl {M = M} f = Strict-model-hom-path F∘-idr refl (λ A Δ x → refl) where
  module M = Strict-model M

M-idr : ∀ {o h} {N M : Strict-model o h} (f : Strict-model-hom N M) → f M∘ M-id ≡ f
M-idr {M = M} f = Strict-model-hom-path F∘-idl refl (λ A Δ x → refl) where
  module M = Strict-model M

M-assoc : ∀ {o h} {N M L K : Strict-model o h} (f : Strict-model-hom N M) (g : Strict-model-hom M L) (h : Strict-model-hom L K) → (f M∘ g) M∘ h ≡ f M∘ (g M∘ h)
M-assoc {K = K} f g h = Strict-model-hom-path F∘-assoc refl (λ A Δ x → refl) where
  module h = Strict-model-hom h
  module K = Strict-model K



Model-hom-is-set : ∀ {o h} {N M : Strict-model o h} → is-set (Strict-model-hom N M)
Model-hom-is-set {N = N} {M}  = Iso→is-hlevel 2 eqv $
  Σ-is-hlevel 2 (Functor-is-set M.has-is-strict) λ _ → hlevel!
  where
    unquoteDecl eqv = declare-record-iso eqv (quote Strict-model-hom)
    module N = Strict-model N
    module M = Strict-model M


Strict-models : ∀ o h → Precategory _ _
Strict-models o h .Ob = Strict-model o h
Strict-models o h .Hom = Strict-model-hom
Strict-models o h .Hom-set _ _ = Model-hom-is-set
Strict-models o h .id = M-id
Strict-models o h ._∘_ f g = g M∘ f
Strict-models o h .idr = M-idl
Strict-models o h .idl = M-idr
Strict-models o h .assoc _ _ _ = M-assoc _ _ _

 
``` 
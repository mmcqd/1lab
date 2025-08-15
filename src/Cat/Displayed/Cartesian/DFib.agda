
open import Cat.Prelude
open import Cat.Reasoning
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Cartesian.Discrete
open import Cat.Displayed.Functor
open import Cat.Displayed.Base
open import Cat.Displayed.Reasoning as DR
open import Cat.Displayed.Fibre
open import Cat.Displayed.Total renaming (∫ to ∫' ; πᶠ to πᶠ' ; ∫ᶠ to ∫ᶠ')
open import Cat.Functor.Adjoint
open import Cat.Displayed.Adjoint
open import Cat.Displayed.Instances.Slice
open import Cat.Functor.Equivalence
open import Cat.Displayed.Composition
open import Cat.Displayed.Instances.Pullback
open import Cat.Instances.Slice
open import Cat.Diagram.Pullback
open import Cat.Instances.Functor
open import Cat.Displayed.Instances.Product
open import Cat.Displayed.Instances.FullSubDisplayed
open import Cat.Diagram.Terminal
open import Cat.Displayed.Instances.Identity
open import Cat.Displayed.Instances.Lift
open import Cat.Displayed.Instances.Lifting
import Cat.Displayed.Morphism as DM

module Cat.Displayed.Cartesian.DFib where

DFib-Ob : ∀ {o ℓ} → Precategory o ℓ → ∀ o' ℓ' → Type _
DFib-Ob 𝒮 o' ℓ' = Σ (Displayed 𝒮 o' ℓ') is-discrete-cartesian-fibration

∫ : ∀ {o ℓ o' ℓ'} {𝒮 : Precategory o ℓ} → DFib-Ob 𝒮 o' ℓ' → Precategory _ _
∫ (A , _) = ∫' A

πᶠ : ∀ {o ℓ o' ℓ'} {𝒮 : Precategory o ℓ} (A : DFib-Ob 𝒮 o' ℓ') → Functor (∫ A) 𝒮 
πᶠ (A , _) = πᶠ' A




module DFib-Ob {o ℓ o' ℓ'} {𝒮 : Precategory o ℓ} ((A , A*) : DFib-Ob 𝒮 o' ℓ') where
  open Displayed A public
  open DR A public
  open Cartesian-fibration A (discrete→cartesian A A*) public
  open is-discrete-cartesian-fibration A* hiding (_^*_ ; π*) public

record DFib-functor 
  {ob ℓb oc ℓc ox ℓx oy ℓy} {B : Precategory ob ℓb} {C : Precategory oc ℓc}
  (F : Functor B C) 
  (x : DFib-Ob B ox ℓx) (y : DFib-Ob C oy ℓy) : Type (ob ⊔ ℓb ⊔ oc ⊔ ℓc ⊔ ox ⊔ ℓx ⊔ oy ⊔ ℓy) where
  constructor hom
  field
    fun : Displayed-functor F (x .fst) (y .fst)

  open Displayed-functor fun public

open DFib-functor public

module _ 
  {ob ℓb oc ℓc od ℓd oe ℓe} 
  {B : Precategory ob ℓb} {C : Precategory oc ℓc} 
  {D : DFib-Ob B od ℓd} {E : DFib-Ob C oe ℓe} 
  {F : Functor B C}
  (F' : DFib-functor F D E)
   where

  ∫ᶠ : Functor (∫ D) (∫ E)
  ∫ᶠ = ∫ᶠ' (F' .fun)

Vertical-DFib-functor 
  : ∀ {o ℓ ox ℓx oy ℓy} {B : Precategory o ℓ}
  → (x : DFib-Ob B ox ℓx) (y : DFib-Ob B oy ℓy)
  → Type _
Vertical-DFib-functor = DFib-functor Id

module _ 
  {o ℓ ox ℓx oy ℓy} {A B : Precategory o ℓ}
  {F : Functor A B} 
  {ℰ : DFib-Ob A ox ℓx} {ℱ : DFib-Ob B oy ℓy} where
  private
    module A = Precategory A
    module ℰ = DFib-Ob ℰ
    module ℱ = DFib-Ob ℱ
    unquoteDecl eqv = declare-record-iso eqv (quote DFib-functor)
    unquoteDecl eqv' = declare-record-iso eqv' (quote Displayed-functor)


  open Functor
  open Displayed-functor
  DFib-functor-pathp 
    : {G : Functor A B} 
    → {F' : DFib-functor F ℰ ℱ} {G' : DFib-functor G ℰ ℱ}
    → (p : F ≡ G)
    → (q0 : ∀ {x} → (x' : ℰ.Ob[ x ]) → PathP (λ i → ℱ.Ob[ p i .F₀ x ]) (F' .fun .F₀' x') (G' .fun .F₀' x'))
    → (q1 : ∀ {x y x' y'} {f : A.Hom x y} → (f' : ℰ.Hom[ f ] x' y')
        → PathP (λ i → ℱ.Hom[ p i .F₁ f ] (q0 x' i) (q0 y' i)) (F' .fun .F₁' f') (G' .fun .F₁' f'))
    → PathP (λ i → DFib-functor (p i) ℰ ℱ) F' G'
  DFib-functor-pathp {F' = (hom F')} {G' = (hom G')} p q0 q1 i .fun = Displayed-functor-pathp {F' = F'} {G' = G'} p q0 q1 i

  instance
    DFib-functor-set : ∀ {n} → H-Level (DFib-functor F ℰ ℱ) (2 + n)
    DFib-functor-set = basic-instance 2 (Iso→is-hlevel 2 eqv (Displayed-functor-is-set ℱ.fibre-set))

module _ {o ℓ} (𝒮 : Precategory o ℓ) o' ℓ' where
 

 
  open is-discrete-cartesian-fibration

  
  DFib : Precategory _ _
  DFib .Precategory.Ob = Σ (Displayed 𝒮 o' ℓ') is-discrete-cartesian-fibration
  DFib .Precategory.Hom A B = Vertical-DFib-functor A B
  DFib .Precategory.Hom-set _ _ = hlevel 2
  DFib .Precategory.id = hom Id'
  DFib .Precategory._∘_ (hom f) (hom g) = hom (f ∘V g)
  DFib .Precategory.idr _ = DFib-functor-pathp refl (λ _ → refl) (λ _ → refl)
  DFib .Precategory.idl _ =  DFib-functor-pathp refl (λ _ → refl) (λ _ → refl)
  DFib .Precategory.assoc _ _ _ =  DFib-functor-pathp refl (λ _ → refl) (λ _ → refl)



module _ 
  {oa ℓa ob ℓb o' ℓ'} 
  {A : Precategory oa ℓa} {B : Precategory ob ℓb}
  where
  private
    module A = Precategory A
    module B = Precategory B

  open Functor
  open _=>_
  open Displayed-functor
  open is-discrete-cartesian-fibration

  -- There should be a pseudofunctor 𝐃𝐅𝐢𝐛 : Cat ^op → Cat
  -- Which sends a category A the category (DFib A) of discrete fibrations over A
  -- And a functor F : B → A to a functor F ^* : DFib A → DFib B
  -- (I think?) the 2-cell structure is trivial because discrete fibrations have propositional Homs


  private
    infix 100 _^*
    _^* : Functor B A → Functor (DFib A o' ℓ') (DFib B o' ℓ')
    (F ^*) .F₀ (X , X*) = Change-of-base F X , Change-of-base-discrete-fibration _ _ X*
    (F ^*) .F₁ {x = x , x*} {y = y , y*} f = hom G where
      open is-discrete-cartesian-fibration y*
      module f = DFib-functor f
      G : Vertical-functor _ _
      G .F₀' = f.₀'
      G .F₁' = f.₁'
      G .F-id' = prop!
      G .F-∘' = prop!
    (F ^*) .F-id = DFib-functor-pathp refl (λ _ → refl) (λ _ → refl)
    (F ^*) .F-∘ _ _ = DFib-functor-pathp refl (λ _ → refl) (λ _ → refl)

  ^*-natural : {F G : Functor B A} → G => F → F ^* => G ^*
  ^*-natural {F} {G} n .η E = hom H where
    module F = Functor F
    module G = Functor G
    module n = _=>_ n
    module E = DFib-Ob E
    H : Vertical-functor ((F ^*) .F₀ E .fst) ((G ^*) .F₀ E .fst)
    H .F₀' {x} x' = (n.η x) E.^* x'
    H .F₁' {a = a} {b} {f} {a'} {b'} f' = E.^*-hom _ (
        G.₁ f E.^* (n.η b E.^* b') ≡˘⟨ E.^*-∘ _ _ _ ⟩ 
        ⌜ n.η b A.∘ G.₁ f ⌝ E.^* b' ≡⟨ ap! (n.is-natural _ _ _) ⟩ 
        (F.₁ f A.∘ n.η a) E.^* b' ≡⟨ E.^*-∘ _ _ _ ⟩
        n.η a E.^* ⌜ F.₁ f E.^* b' ⌝ ≡⟨ ap! (E.^*-lift _ f') ⟩
        n.η a E.^* a' ∎       
      )
    H .F-id' = prop!
    H .F-∘' = prop!
  ^*-natural n .is-natural D E f = 
    DFib-functor-pathp refl 
      (λ x' → E.^*-lift _ (f.₁' (D.π* _ x')))
      (λ _ → is-prop→pathp (λ _ → hlevel 1) _ _)
    where
      module D = DFib-Ob D
      module E = DFib-Ob E
      module n = _=>_ n
      module f = DFib-functor f



  Base-change : Functor (Cat[ B , A ] ^op) Cat[ DFib A o' ℓ' , DFib B o' ℓ' ]
  Base-change .F₀ = _^*
  Base-change .F₁ = ^*-natural
  Base-change .F-id = ext p where
    module _ E where
      module E = DFib-Ob E
      p : _
      p = DFib-functor-pathp refl E.^*-id (λ _ → is-prop→pathp (λ _ → hlevel 1) _ _)
  Base-change .F-∘ _ _ = ext p where
    module _ E where
      module E = DFib-Ob E
      p : _
      p = DFib-functor-pathp refl (E.^*-∘ _ _) (λ _ → is-prop→pathp (λ _ → hlevel 1) _ _)

  infix 100 _DFib^*
 
  _DFib^* : Functor B A → Functor (DFib A o' ℓ') (DFib B o' ℓ')
  _DFib^* = _^*

module _ 
  {oa ℓa}
  {A : Precategory oa ℓa}
  o' ℓ'
  where
  open _=>_
  open Displayed-functor

  -- The DFib pseudofunctor is cartesian... I think
  
  id^*=>id : _DFib^* {o' = o'} {ℓ'} (Id {C = A}) => Id
  id^*=>id .η A .fun .F₀' = λ x' → x'
  id^*=>id .η A .fun .F₁' = λ z → z
  id^*=>id .η A .fun .F-id' = transport-refl _
  id^*=>id .η A .fun .F-∘' = transport-refl _
  id^*=>id .is-natural _ _ _ = DFib-functor-pathp refl (λ _ → refl) (λ _ → refl)
  
  id=>id^* : Id => _DFib^* {o' = o'} {ℓ'} (Id {C = A})
  id=>id^* .η A .fun .F₀' = λ x' → x'
  id=>id^* .η A .fun .F₁' = λ z → z
  id=>id^* .η A .fun .F-id' = sym $ transport-refl _
  id=>id^* .η A .fun .F-∘' = sym $ transport-refl _
  id=>id^* .is-natural _ _ _ = DFib-functor-pathp refl (λ _ → refl) (λ _ → refl)

  id^* : _DFib^* {o' = o'} {ℓ'} (Id {C = A}) ≅ⁿ Id 
  id^* .to = id^*=>id
  id^* .from = id=>id^*
  id^* .inverses = record { invl = ext (λ _ → DFib-functor-pathp refl (λ _ → refl) (λ _ → refl)) ; invr = ext (λ _ → DFib-functor-pathp refl (λ _ → refl) (λ _ → refl)) }


module _ 
  {o ℓ } (𝒮 : Precategory o ℓ) o' ℓ'
  (let module DFib𝒮 = Cat.Reasoning (DFib 𝒮 o' ℓ')) 
  where

  open Terminal
  DFib-terminal : Terminal (DFib 𝒮 o' ℓ')
  DFib-terminal .top = Lift-disp (IdD 𝒮) o' ℓ' , record { fibre-set = λ _ → hlevel 2 ; cart-lift = λ _ _ → hlevel 0 }
  DFib-terminal .has⊤ x .centre = hom (record { F₀' = λ _ → lift tt ; F₁' = λ _ → lift tt ; F-id' = refl ; F-∘' = refl })
  DFib-terminal .has⊤ x .paths f = DFib-functor-pathp refl (λ _ → refl) (λ _ → refl)

  open is-discrete-cartesian-fibration
  open Cartesian-lift
  open is-cartesian
  open Displayed-functor

  -- We know that Slice (DFib 𝒮 o' ℓ') A ≃ DFib (∫ A) o' ℓ' 
  -- So we just define slices directly as such
  DFib/ : Displayed (DFib 𝒮 o' ℓ') _ _
  DFib/ .Displayed.Ob[_] A = DFib (∫ A) o' ℓ' .Precategory.Ob
  DFib/ .Displayed.Hom[_] f A B = DFib-functor (∫ᶠ f) A B
  DFib/ .Displayed.Hom[_]-set _ _ (_ , B*) = hlevel 2
  DFib/ .Displayed.id' = hom ∫ᶠId'
  DFib/ .Displayed._∘'_ (hom f) (hom g) = hom (f ∫ᶠ∘V g)
  DFib/ .Displayed.idr' _ = DFib-functor-pathp _ (λ _ → refl) (λ _ → refl)
  DFib/ .Displayed.idl' _ = DFib-functor-pathp _ (λ _ → refl) (λ _ → refl)
  DFib/ .Displayed.assoc' _ _ _ = DFib-functor-pathp _ (λ _ → refl) (λ _ → refl)

  
module _ 
  {o ℓ} {𝒮 : Precategory o ℓ} {o' ℓ'}
  (let module DFib𝒮 = Cat.Reasoning (DFib 𝒮 o' ℓ')) 
  where
  open is-discrete-cartesian-fibration
  open Cartesian-lift
  open is-cartesian
  open Displayed-functor

  _DFib×_ : DFib𝒮.Ob → DFib𝒮.Ob → DFib𝒮.Ob
  (A , A*) DFib× (B , B*) = (A D× B) , D×-discrete A* B*


  -- We could get this by going through some equivalences, but easier to just define it directly
  DFib/-cartesian : Cartesian-fibration (DFib/ 𝒮 o' ℓ')
  DFib/-cartesian f y' .x' = ((∫ᶠ f) DFib^*) · y'
  DFib/-cartesian f (y' , y'*) .lifting = hom (Change-of-base-functor (∫ᶠ f) y')
  DFib/-cartesian f (y' , y'*) .cartesian .universal {u' = u' , _} g F' = hom F where
    module y' = DFib-Ob (y' , y'*)
    F : Displayed-functor (∫ᶠ g) u' (Change-of-base (∫ᶠ f) y')
    F .F₀' = F' .F₀'
    F .F₁' = F' .F₁'
    F .F-id' = is-prop→pathp (λ i → hlevel 1) _ _
    F .F-∘' = is-prop→pathp (λ i → hlevel 1) _ _
  DFib/-cartesian f y' .cartesian .commutes m h' = 
    DFib-functor-pathp refl (λ _ → refl) (λ _ → refl)
  DFib/-cartesian f y' .cartesian .unique _ p =
    DFib-functor-pathp refl (λ x'' → ap (λ z → z .F₀' x'') p) (λ f' → apd (λ _ z → z .F₁' f') p)


  private module DFib/ = Displayed (DFib/ 𝒮 o' ℓ')

  DFibΣ : (A : DFib𝒮.Ob) → DFib/.Ob[ A ] → DFib𝒮.Ob
  DFibΣ (A , A*) (B , B*) = (A D∘ B) , discrete-∘ A* B*


  is-representable : (A : DFib𝒮.Ob) → DFib/.Ob[ A ] → Type _
  is-representable A A' = Σ[ δ ∈ Functor (∫ A) (∫ A') ] πᶠ A' ⊣ δ

module Make-DFib/ {o ℓ} (𝒮 : Precategory o ℓ) o' ℓ' where
  open Displayed (DFib/ 𝒮 o' ℓ') public
  open Cartesian-fibration (DFib/ 𝒮 o' ℓ') DFib/-cartesian public
  open DM (DFib/ 𝒮 o' ℓ') public





{-

  module _ {A B X : DFib.Ob} (F : DFib.Hom A X) (G : DFib.Hom B X) where
    open Pullback
    open is-pullback
    open is-discrete-cartesian-fibration

    private
      module F = Displayed-functor F
      module G = Displayed-functor G
      module A = DFib-Ob A
      module B = DFib-Ob B
      module X = DFib-Ob X


    DFib-pullback : Displayed 𝒮 o' ℓ'
    DFib-pullback = Restrict (A .fst D× B .fst) λ (a , b) → F.₀' a ≡ G.₀' b

    DFib-pullback* : is-discrete-cartesian-fibration DFib-pullback
    DFib-pullback* = Restrict-discrete (D×-discrete (A .snd) (B .snd)) (λ _ → hlevel 1) $ λ {x y} {f} {(a , b)} p →
        F.₀' (f A.^* a) ≡˘⟨ X.^*-lift f (F.₁' (A.π* _ _)) ⟩ 
        f X.^* ⌜ F.₀' a ⌝ ≡⟨ ap! p ⟩
        f X.^* (G.₀' b) ≡⟨ X.^*-lift f (G.₁' (B.π* _ _)) ⟩
        G.₀' (f B.^* b) ∎
  
    DFib-has-pullbacks : Pullback (DFib 𝒮 o' ℓ') {A} {B} {X} F G
    DFib-has-pullbacks .apex = DFib-pullback , DFib-pullback*
    DFib-has-pullbacks .p₁ = RestrictF Fst'
    DFib-has-pullbacks .p₂ = RestrictF Snd'
    DFib-has-pullbacks .has-is-pb .square = 
      Vertical-functor-path 
        snd
        (λ _ → is-prop→pathp (λ _ → hlevel 1) _ _)
    DFib-has-pullbacks .has-is-pb .universal {p₁' = p₁'} {p₂'} p = ExtendF (Pair' p₁' p₂') λ x' → 
      ap (λ z → z .F₀' x') p
    DFib-has-pullbacks .has-is-pb .p₁∘universal = Vertical-functor-path (λ _ → refl) (λ _ → refl)
    DFib-has-pullbacks .has-is-pb .p₂∘universal = Vertical-functor-path (λ _ → refl) (λ _ → refl)
    DFib-has-pullbacks .has-is-pb .unique a b = 
      Vertical-functor-path 
        (λ x' → Σ-prop-path! (ap (λ z → z .F₀' x') a ,ₚ ap (λ z → z .F₀' x') b)) 
        (λ f' → ap (λ z → z .F₁' f') a ,ₚ ap (λ z → z .F₁' f') b)
  

  open Cartesian-lift
  open is-cartesian

  DFib-slices-cartesian : Cartesian-fibration (Slices (DFib 𝒮 o' ℓ'))
  DFib-slices-cartesian = Codomain-fibration _ DFib-has-pullbacks

-}


-- module _ 
--   {o ℓ o' ℓ'} {𝒮 : Precategory o ℓ} 
--   (let module DFib𝒮 = Cat.Reasoning (DFib 𝒮 o' ℓ')) 
--   (A : DFib𝒮.Ob) 
--   where



  -- private
  --   module A = DFib-Ob A
  --   module DFib𝒮/A = Cat.Reasoning (Slice (DFib 𝒮 o' ℓ') A)
  --   module DFib∫A = Cat.Reasoning (DFib (∫ A) o' ℓ')

  -- open /-Hom
  -- open Functor
  -- open Displayed-functor


  -- f : Functor (Slice (DFib 𝒮 o' ℓ') A) (DFib (∫ A) o' ℓ')
  -- f .F₀ (cut {B , B*} map) .fst = Change-of-base (πᶠ A) B
  -- f .F₀ (cut {B , B*} map) .snd = Change-of-base-discrete-fibration _ _ B*
  -- f .F₁ {x = x} {y = y} f = hom F where
  --   open is-discrete-cartesian-fibration (y ./-Obj.domain .snd)
  --   F : Vertical-functor _ _
  --   F .F₀' = f .map .F₀'
  --   F .F₁' = f .map .F₁'
  --   F .F-id' = prop!
  --   F .F-∘' = prop!
  -- f .F-id = DFib-functor-pathp refl (λ _ → refl) (λ _ → refl)
  -- f .F-∘ _ _ = DFib-functor-pathp refl (λ _ → refl) (λ _ → refl)

  -- g : Functor (DFib (∫ A) o' ℓ') (Slice (DFib 𝒮 o' ℓ') A)
  -- g .F₀ B ./-Obj.domain = DFibΣ A B
  -- g .F₀ B ./-Obj.map = hom πᵈ
  -- g .F₁ (hom F) ./-Hom.map = hom D∘⟨-, F ⟩
  -- g .F₁ F ./-Hom.commutes = DFib-functor-pathp refl (λ _ → refl) (λ _ → refl)
  -- g .F-id = ext (DFib-functor-pathp refl (λ _ → refl) (λ _ → refl))
  -- g .F-∘ f g = ext (DFib-functor-pathp refl (λ _ → refl) (λ _ → refl))


module _ 
  {o ℓ o' ℓ'} {𝒮 : Precategory o ℓ} 
  where

  private module DFib𝒮 = Cat.Reasoning (DFib 𝒮 o' ℓ')

  open /-Hom
  open Functor
  open Displayed-functor

  DFib/→Slices : Vertical-functor (DFib/ 𝒮 o' ℓ') (Slices (DFib 𝒮 o' ℓ'))
  DFib/→Slices .F₀' {A} A' = cut {domain = DFibΣ A A'} (hom πᵈ)
  DFib/→Slices .F₁' {f = (hom F)} (hom F') = slice-hom (hom D∘⟨ F , F' ⟩) (DFib-functor-pathp refl (λ _ → refl) (λ _ → refl))
  DFib/→Slices .F-id' = Slice-path _ (DFib-functor-pathp refl (λ _ → refl) (λ _ → refl))
  DFib/→Slices .F-∘' = Slice-path _ (DFib-functor-pathp refl (λ _ → refl) (λ _ → refl))

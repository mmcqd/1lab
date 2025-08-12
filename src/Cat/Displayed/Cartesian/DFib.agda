
open import Cat.Prelude
open import Cat.Reasoning
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Cartesian.Discrete
open import Cat.Displayed.Functor
open import Cat.Displayed.Base
open import Cat.Displayed.Reasoning as DR
open import Cat.Displayed.Fibre
open import Cat.Displayed.Total
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
open import Cat.Instances.StrictCat

module Cat.Displayed.Cartesian.DFib where


module _ {o ℓ} (𝒮 : Precategory o ℓ) o' ℓ' where

  open is-discrete-cartesian-fibration

  
  DFib : Precategory _ _
  DFib .Precategory.Ob = Σ (Displayed 𝒮 o' ℓ') is-discrete-cartesian-fibration
  DFib .Precategory.Hom (A , _) (B , _) = Vertical-functor A B
  DFib .Precategory.Hom-set _ (_ , B*) = Vertical-functor-is-set (B* .fibre-set)
  DFib .Precategory.id = Id'
  DFib .Precategory._∘_ = _∘V_
  DFib .Precategory.idr _ = Vertical-functor-path (λ _ → refl) (λ _ → refl)
  DFib .Precategory.idl _ = Vertical-functor-path (λ _ → refl) (λ _ → refl)
  DFib .Precategory.assoc _ _ _ = Vertical-functor-path (λ _ → refl) (λ _ → refl)

module _ {o ℓ o' ℓ'} {𝒮 : Precategory o ℓ} where

  private 
    module 𝒮 = Cat.Reasoning 𝒮
    module DFib𝒮 = Cat.Reasoning (DFib 𝒮 o' ℓ')

  module DFib-Ob ((A , A*) : DFib𝒮.Ob) where
    open Displayed A public
    open DR A public
    open Cartesian-fibration A (discrete→cartesian A A*) public
    open is-discrete-cartesian-fibration A* hiding (_^*_ ; π*) public


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
  -- Equivalently, discrete fibrations are "bi-displayed" over the bicategory Cat


  private
    infix 100 _^*
    _^* : Functor B A → Functor (DFib A o' ℓ') (DFib B o' ℓ')
    (F ^*) .F₀ (X , X*) = Change-of-base F X , Change-of-base-discrete-fibration _ _ X*
    (F ^*) .F₁ {x = x , x*} {y = y , y*} f = G where
      open is-discrete-cartesian-fibration y*
      module f = Displayed-functor f
      G : Vertical-functor _ _
      G .F₀' = f.₀'
      G .F₁' = f.₁'
      G .F-id' = prop!
      G .F-∘' = prop!
    (F ^*) .F-id = Vertical-functor-path (λ _ → refl) (λ _ → refl)
    (F ^*) .F-∘ _ _ = Vertical-functor-path (λ _ → refl) (λ _ → refl)

    ^*-natural : {F G : Functor B A} → G => F → F ^* => G ^*
    ^*-natural {F} {G} n .η E = H where
      module F = Functor F
      module G = Functor G
      module n = _=>_ n
      module E = DFib-Ob E
      H : Vertical-functor ((F ^*) .F₀ E .fst) ((G ^*) .F₀ E .fst)
      H .F₀' {x} = n.η x E.^*_
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
      Vertical-functor-path 
        (λ x' → E.^*-lift _ (f.₁' (D.π* _ x')))
        (λ _ → is-prop→pathp (λ _ → hlevel 1) _ _)
      where
        module D = DFib-Ob D
        module E = DFib-Ob E
        module n = _=>_ n
        module f = Displayed-functor f



  Base-change : Functor (Cat[ B , A ] ^op) Cat[ DFib A o' ℓ' , DFib B o' ℓ' ]
  Base-change .F₀ = _^*
  Base-change .F₁ = ^*-natural
  Base-change .F-id = ext p where
    module _ E where
      module E = DFib-Ob E
      p : _
      p = Vertical-functor-path-prop! E.^*-id
  Base-change .F-∘ _ _ = ext p where
    module _ E where
      module E = DFib-Ob E
      p : _
      p = Vertical-functor-path-prop! (E.^*-∘ _ _)

  infix 100 _DFib^*
  _DFib^* : Functor B A → Functor (DFib A o' ℓ') (DFib B o' ℓ')
  _DFib^* = _^*


module _ 
  {o ℓ } (𝒮 : Precategory o ℓ) o' ℓ'
  (let module DFib𝒮 = Cat.Reasoning (DFib 𝒮 o' ℓ')) 
  where

  open Terminal
  DFib-terminal : Terminal (DFib 𝒮 o' ℓ')
  DFib-terminal .top = Lift-disp (IdD 𝒮) o' ℓ' , record { fibre-set = λ _ → hlevel 2 ; cart-lift = λ _ _ → hlevel 0 }
  DFib-terminal .has⊤ x .centre = record { F₀' = λ _ → lift tt ; F₁' = λ _ → lift tt ; F-id' = refl ; F-∘' = refl }
  DFib-terminal .has⊤ x .paths f = Vertical-functor-path (λ _ → refl) (λ _ → refl)

  open is-discrete-cartesian-fibration
  open Cartesian-lift
  open is-cartesian
  open Displayed-functor

  -- We know that Slice (DFib 𝒮 o' ℓ') A ≃ DFib (∫ A) o' ℓ' 
  -- So we just define slices directly as such
  DFib/ : Displayed (DFib 𝒮 o' ℓ') _ _
  DFib/ .Displayed.Ob[_] (A , A*) = DFib (∫ A) o' ℓ' .Precategory.Ob
  DFib/ .Displayed.Hom[_] f (A , A*) (B , B*) = Displayed-functor (∫ᶠ f) A B
  DFib/ .Displayed.Hom[_]-set _ _ (_ , B*) = Displayed-functor-is-set (B* .fibre-set)
  DFib/ .Displayed.id' = ∫ᶠId'
  DFib/ .Displayed._∘'_ = _∫ᶠ∘V_
  DFib/ .Displayed.idr' _ = Displayed-functor-pathp _ (λ _ → refl) (λ _ → refl)
  DFib/ .Displayed.idl' _ = Displayed-functor-pathp _ (λ _ → refl) (λ _ → refl)
  DFib/ .Displayed.assoc' _ _ _ = Displayed-functor-pathp _ (λ _ → refl) (λ _ → refl)


  
module _ 
  {o ℓ} {𝒮 : Precategory o ℓ} {o' ℓ'}
  (let module DFib𝒮 = Cat.Reasoning (DFib 𝒮 o' ℓ')) 
  where
  open is-discrete-cartesian-fibration
  open Cartesian-lift
  open is-cartesian
  open Displayed-functor

  -- We could get this by going through some equivalences, but easier to just define it directly
  DFib/-cartesian : Cartesian-fibration (DFib/ 𝒮 o' ℓ')
  DFib/-cartesian f y' .x' = ((∫ᶠ f) DFib^*) · y'
  DFib/-cartesian f (y' , y'*) .lifting = Change-of-base-functor (∫ᶠ f) y'
  DFib/-cartesian f (y' , y'*) .cartesian .universal {u' = u' , _} g F' = F where
    module y' = DFib-Ob (y' , y'*)
    F : Displayed-functor (∫ᶠ g) u' (Change-of-base (∫ᶠ f) y')
    F .F₀' = F' .F₀'
    F .F₁' = F' .F₁'
    F .F-id' = is-prop→pathp (λ i → hlevel 1) _ _
    F .F-∘' = is-prop→pathp (λ i → hlevel 1) _ _
  DFib/-cartesian f y' .cartesian .commutes m h' = 
    Displayed-functor-pathp refl (λ _ → refl) (λ _ → refl)
  DFib/-cartesian f y' .cartesian .unique _ p =
    Displayed-functor-pathp refl (λ x'' → ap (λ z → z .F₀' x'') p) (λ f' → apd (λ _ z → z .F₁' f') p)


  private module DFib/ = Displayed (DFib/ 𝒮 o' ℓ')

  _DFib/∘_ : (A : DFib𝒮.Ob) → DFib/.Ob[ A ] → DFib𝒮.Ob
  (A , A*) DFib/∘ (B , B*) = (A D∘ B) , discrete-∘ A* B*


  -- is-representable : ∀ {A B} → DFib𝒮.Hom A B → Type _
  -- is-representable {A , _} {B , _} f = Σ[ δ ∈ Functor (∫ B) (∫ A) ] ∫ᶠ f ⊣ δ


  is-representable : (A : DFib𝒮.Ob) → DFib/.Ob[ A ] → Type _
  is-representable (A , _) (A' , _) = Σ[ δ ∈ Functor (∫ A) (∫ A') ] πᶠ A' ⊣ δ
   
  -- is-representable : (A : DFib𝒮.Ob) → DFib/.Ob[ A ] → Type _
  -- is-representable (A , _) (A' , _) = 
  --   Σ[ δ ∈ Functor (∫ A) 𝒮 ] 
  --   Σ[ δ' ∈ Lifting (A D∘ A') δ ] 
  --   ∫ᶠ πᵈ ⊣ Lifting→Functor _ δ'
   



  

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


module _ 
  {o ℓ o' ℓ'} {𝒮 : Precategory o ℓ} 
  (let module DFib𝒮 = Cat.Reasoning (DFib 𝒮 o' ℓ')) 
  ((A , A*) : DFib𝒮.Ob) 
  where



  private
    module A = Displayed A
    module DFib𝒮/A = Cat.Reasoning (Slice (DFib 𝒮 o' ℓ') (A , A*))
    module DFib∫A = Cat.Reasoning (DFib (∫ A) o' ℓ')

  open /-Hom
  open Functor
  open Displayed-functor


  f : Functor (Slice (DFib 𝒮 o' ℓ') (A , A*)) (DFib (∫ A) o' ℓ')
  f .F₀ (cut {B , B*} map) .fst = Change-of-base (πᶠ A) B
  f .F₀ (cut {B , B*} map) .snd = Change-of-base-discrete-fibration _ _ B*
  f .F₁ {x = x} {y = y} f = F where
    open is-discrete-cartesian-fibration (y ./-Obj.domain .snd)
    F : Vertical-functor _ _
    F .F₀' = f .map .F₀'
    F .F₁' = f .map .F₁'
    F .F-id' = prop!
    F .F-∘' = prop!
  f .F-id = Vertical-functor-path (λ _ → refl) (λ _ → refl)
  f .F-∘ _ _ = Vertical-functor-path (λ _ → refl) (λ _ → refl)

  g : Functor (DFib (∫ A) o' ℓ') (Slice (DFib 𝒮 o' ℓ') (A , A*))
  g .F₀ (B , B*) ./-Obj.domain = A D∘ B , discrete-∘ A* B*
  g .F₀ (B , B*) ./-Obj.map = πᵈ
  g .F₁ F ./-Hom.map = D∘⟨-, F ⟩
  g .F₁ F ./-Hom.commutes = Vertical-functor-path (λ _ → refl) (λ _ → refl)
  g .F-id = ext (Vertical-functor-path (λ _ → refl) (λ _ → refl))
  g .F-∘ f g = ext (Vertical-functor-path (λ _ → refl) (λ _ → refl))


-}
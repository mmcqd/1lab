```agda

open import Cat.Displayed.Univalence.Reasoning
open import Cat.Displayed.Univalence
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Cartesian.Discrete 
open import Cat.Displayed.Base
open import Cat.Displayed.Path
open import Cat.Prelude

import Cat.Reasoning as Cr
import Cat.Displayed.Reasoning as Dr
import Cat.Displayed.Morphism as Dm

module Cat.Displayed.Cartesian.Discrete.Reasoning
  {o ℓ o' ℓ'} 
  {B : Precategory o ℓ} 
  {E : Displayed B o' ℓ'} 
  (E* : is-discrete-cartesian-fibration E) 
  where
```

Discrete fibrations have a number of nice properties.

```agda
  private
    module B = Cr B
    open module E = Dr E

  open Dm E
  open is-discrete-cartesian-fibration E*
  open Inverses[_]

  instance
    ≅[]-is-prop : ∀ {n} {a b a' b'} {i : a B.≅ b} → H-Level (a' ≅[ i ] b') (1 + n)
    ≅[]-is-prop = basic-instance 1 $
      Iso→is-hlevel 1 eqv₁ $ 
      Σ-is-hlevel 1 (hlevel 1) λ _ → 
      Σ-is-hlevel 1 (hlevel 1) λ _ → 
      Iso→is-hlevel 1 eqv₂ (hlevel 1)
      where
        unquoteDecl eqv₁ = declare-record-iso eqv₁ (quote _≅[_]_)
        unquoteDecl eqv₂ = declare-record-iso eqv₂ (quote Inverses[_])
    

  ob[_] : ∀ {a b} (f : B.Hom b a) → Ob[ a ] → Ob[ b ]
  ob[ f ] a' = f ^* a'

  ob[_]-equiv : ∀ {x y} (f : x B.≅ y) → is-equiv ob[ f .B.from ]
  ob[_]-equiv {x} {y} f = is-iso→is-equiv (iso (f .B.to ^*_) invl invr) 
    where
      invl : _
      invl x = (sym $ ^*-∘ _ _ _) ∙∙ ap (_^* x) (f .B.invl) ∙∙ ^*-id _
      
      invr : _
      invr x =(sym $ ^*-∘ _ _ _) ∙∙ ap (_^* x) (f .B.invr) ∙∙ ^*-id _


  ≅→equiv : ∀ {x y} (f : x B.≅ y) → Ob[ x ] ≃ Ob[ y ]
  ≅→equiv f = ob[ f .B.from ] , ob[ f ]-equiv

  _≡[_]ob_ : ∀ {a b} → Ob[ a ] → a B.≅ b → Ob[ b ] → Type _
  _≡[_]ob_ a' p b' = Hom[ p .B.from ] b' a' 


  singl-hom-is-prop : ∀ {x y x'} (f : x B.≅ y) → is-prop (Σ[ y' ∈ Ob[ y ] ] x' ≡[ f ]ob y')
  singl-hom-is-prop {x} {y} {x'} f = Equiv→is-hlevel 1 eqv (is-contr→is-prop Singleton-is-contr) 
    where
      eqv : (Σ[ y' ∈ Ob[ y ] ] Hom[ f .B.from ] y' x') ≃ Singleton (f .B.from ^* x') 
      eqv = Σ-ap (_ , id-equiv) λ y' → Equiv.inverse (^*-hom _ , ^*-hom-is-equiv _)

  sym-≡[]ob : ∀ {x y x' y'} (f : x B.≅ y) → x' ≡[ f ]ob y' → y' ≡[ f B.Iso⁻¹ ]ob x'
  sym-≡[]ob {x' = x'} {y' = y'} f p = 
      ^*-hom _ $ 
      has-prop-fibres→injective (f .B.from ^*_) (λ x → is-contr→is-prop $ ob[ f ]-equiv .is-eqv x) $
        f .B.from ^* (f .B.to ^* y')    ≡˘⟨ ^*-∘ _ _ _ ⟩ 
        ⌜ f .B.to B.∘ f .B.from ⌝ ^* y' ≡⟨ ap! (f .B.invl) ⟩ 
        B.id ^* y'                      ≡⟨ ^*-id _ ⟩
        y'                              ≡˘⟨ ^*-lift _ p ⟩
        (f .B.from ^* x') ∎

  ≡[]ob→≅[] 
    : ∀ {x y x' y'} (f : x B.≅ y)
    → x' ≡[ f ]ob y'  
    → x' ≅[ f ] y'
  ≡[]ob→≅[] f p = make-iso[ _ ] (sym-≡[]ob f p) p prop! prop!

  discrete→is-category-displayed : is-category-displayed E
  discrete→is-category-displayed {y = y} f x' = Iso→is-hlevel 1 eqv (singl-hom-is-prop f)
    where
      eqv : Iso (Σ Ob[ y ] (x' ≅[ f ]_  )) (Σ[ y' ∈ Ob[ y ] ] (Hom[ f .B.from ] y' x'))
      eqv .fst (y' , p) = y' , p .from'
      eqv .snd .is-iso.from (y' , p) = y' , ≡[]ob→≅[] f p
      eqv .snd .is-iso.rinv _ = refl
      eqv .snd .is-iso.linv _ = refl ,ₚ prop!
```

We can develop an analogue of our `hom[_]` calculus for displayed *objects*.

```agda
  


  opaque
    ob-coh[_] : ∀ {a b} (p : a B.≅ b) (a' : Ob[ a ]) → a' ≡[ p ]ob ob[ p .B.from ] a'
    ob-coh[ p ] a' = ^*-hom _ refl

    ob-coh[_]⁻ : ∀ {a b} (p : a B.≅ b) (a' : Ob[ a ]) → ob[ p .B.from ] a' ≡[ p B.Iso⁻¹ ]ob a'
    ob-coh[ p ]⁻ a' = sym-≡[]ob p (ob-coh[ p ] a')


    from-pathp[]ob 
      : ∀ {a b a' b'} (p : a B.≅ b)
      → a' ≡[ p ]ob b' → ob[ p .B.from ] a' ≡ b'
    from-pathp[]ob _ = ^*-lift _

    to-pathp[]ob
      : ∀ {a b a' b'} (p : a B.≅ b)
      → ob[ p .B.from ] a' ≡ b' → a' ≡[ p ]ob b'
    to-pathp[]ob _ = ^*-hom _

    from-pathp[]ob⁻
      : ∀ {a b a' b'} (p : a B.≅ b)
      → a' ≡[ p ]ob b' → a' ≡ ob[ p .B.to ] b'
    from-pathp[]ob⁻ {a' = a'} {b' = b'} p p' = 
      sym (^*-lift _ (sym-≡[]ob p p'))

    to-pathp[]ob⁻
      : ∀ {a b a' b'} (p : a B.≅ b)
      → a' ≡ ob[ p .B.to ] b' → a' ≡[ p ]ob b'
    to-pathp[]ob⁻ {a' = a'} {b' = b'} p p' = 
      sym-≡[]ob (p B.Iso⁻¹) $ ^*-hom _ (sym p')

    ob-cast[] 
      : ∀ {a b a' b'}
      → (p : a B.≅ b) 
      → (q : a B.≅ b)
      → (p .B.to ≡ q .B.to)
      → a' ≡[ p ]ob b'
      → a' ≡[ q ]ob b'
    ob-cast[] {a' = a'} {b' = b'} p q w p' = 
      subst (λ f → Hom[ f ] b' a') (ap B.from $ B.≅-path {f = p} {g = q} w) p'

    syntax ob-cast[] p w = ob-cast[ w ] p


    _≡[]ob⟨_⟩_
      : ∀ {a b c b' c'} 
      → {f : B.Hom b a} {g : B.Hom c b}
      → (a' : Ob[ a ]) 
      → Hom[ f ] b' a'
      → Hom[ g ] c' b'
      → Hom[ f B.∘ g ] c' a' 
    a' ≡[]ob⟨ p' ⟩ q' = p' ∘' q'

    _≡[_]ob˘⟨_⟩_
      : ∀ {a b c b' c'}  {g : B.Hom c b}
      → (a' : Ob[ a ]) 
      → (f : a B.≅ b)
      → Hom[ f .B.to ] a' b'
      → Hom[ g ] c' b'
      → Hom[ f .B.from B.∘ g ] c' a'
    a' ≡[ f ]ob˘⟨ p' ⟩ q' = sym-≡[]ob (f B.Iso⁻¹) p' ∘' q'
    
    infixr 2 _≡[]ob⟨_⟩_ _≡[_]ob˘⟨_⟩_

    _∎ob 
      : ∀ {a} (a' : Ob[ a ]) 
      → a' ≡[ B.id-iso ]ob a'
    _∎ob a' = id'

    ≡→≡[]ob 
      : ∀ {a} {a₁ a₂ : Ob[ a ]} 
      → a₁ ≡ a₂
      → a₁ ≡[ B.id-iso ]ob a₂
    ≡→≡[]ob {a₁ = a₁} {a₂ = a₂} p = 
      subst (λ z → Hom[ B.id ] z a₁) p id'


    -- _∙[]ob_ 
    --   : ∀ {a b c a' b' c'} 
    --   → Σ (a B.≅ b) (a' ≡[_]ob b')
    --   → Σ (b B.≅ c) (b' ≡[_]ob c')
    --   → Σ (a B.≅ c) (a' ≡[_]ob c')
    -- _∙[]ob_ {a' = a'} {b' = b'} {c' = c'} (p , p') (q , q') =
    --   (p B.∙Iso q) , p' ∘' q'

    -- _≡[]ob⟨_⟩_
    --   : ∀ {a b c b' c'} 
    --   → (a' : Ob[ a ]) 
    --   → Σ (a B.≅ b) (a' ≡[_]ob b')
    --   → Σ (b B.≅ c) (b' ≡[_]ob c')
    --   → Σ (a B.≅ c) (a' ≡[_]ob c')
    -- a' ≡[]ob⟨ p' ⟩ q' = p' ∙[]ob q'


    -- _≡[]ob˘⟨_⟩_
    --   : ∀ {a b c b' c'} 
    --   → (a' : Ob[ a ]) 
    --   → Σ (b B.≅ a) (b' ≡[_]ob a')
    --   → Σ (b B.≅ c) (b' ≡[_]ob c')
    --   → Σ (a B.≅ c) (a' ≡[_]ob c')
    -- a' ≡[]ob˘⟨ (p , p') ⟩ q' = (p B.Iso⁻¹ , sym-≡[]ob p p') ∙[]ob q'
    
    -- _∎ob 
    --   : ∀ {a} (a' : Ob[ a ]) 
    --   → Σ (a B.≅ a) (a' ≡[_]ob a')
    -- _∎ob a' = B.id-iso , id'

    -- infixr 2 _≡[]ob⟨_⟩_ _≡[]ob˘⟨_⟩_

``` 
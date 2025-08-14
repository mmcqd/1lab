open import Cat.Prelude
open import Cat.Displayed.Base
open import Cat.Bi.Base
open import Cat.Bi.Displayed.Base
open import Cat.Displayed.Cartesian
open import Cat.Displayed.Cartesian.Discrete
open import Cat.Displayed.Functor.Naturality
open import Cat.Displayed.Instances.DisplayedFunctor
open import Cat.Displayed.Morphism
open import Cat.Displayed.Functor


module Cat.Bi.Displayed.Cartesian
  {o oh ℓh o' oh' ℓh'} {B : Prebicategory o oh ℓh} (E : Bidisplayed B o' oh' ℓh')
  where

open Prebicategory B
open Bidisplayed E

record is-bicartesian {A B A' B'} (f : A ↦ B) (f' : A' [ f ]↦ B') : Type {!   !} where
  no-eta-equality
  field
    universal : ∀ {U U'} (m : U ↦ A) (h' : U' [ f ⊗ m ]↦ B') → U' [ m ]↦ A'
    commutes : ∀ {U U'} (m : U ↦ A) (h' : U' [ f ⊗ m ]↦ B')
            → {! f' ⊗' universal m h'   !} ≅[ {!   !} ]ⁿ {!   !} 

--     universal : ∀ {u u'} (m : Hom u a) (h' : Hom[ f ∘ m ] u' b') → Hom[ m ] u' a'
--     commutes  : ∀ {u u'} (m : Hom u a) (h' : Hom[ f ∘ m ] u' b')
--               → f' ∘' universal m h' ≡ h'
--     unique    : ∀ {u u'} {m : Hom u a} {h' : Hom[ f ∘ m ] u' b'}
--               → (m' : Hom[ m ] u' a') → f' ∘' m' ≡ h' → m' ≡ universal m h'


-- record
--   is-cartesian {a b a' b'} (f : Hom a b) (f' : Hom[ f ] a' b') : Type (o ⊔ ℓ ⊔ o' ⊔ ℓ')
--   where
--   no-eta-equality
-- ```

-- More specifically, let $u : \cB$ and $u'$ be over $u$, and suppose
-- that we have a map $m : u \to a$ (below, in violet), and a map $h' : u'
-- \to_{fm} b'$ lying over the composite $fm$ (in red). The universal property
-- of a Cartesian map says that we have a universal factorisation of $h'$
-- through a map $u' \to a'$ (in green, marked $\exists!$).

-- ~~~{.quiver}
-- \[\begin{tikzcd}
--   \textcolor{rgb,255:red,124;green,50;blue,189}{u'} \\
--   & {a'} && {b'} \\
--   \textcolor{rgb,255:red,124;green,50;blue,189}{u} \\
--   & a && b
--   \arrow["{f'}"', from=2-2, to=2-4]
--   \arrow["f", from=4-2, to=4-4]
--   \arrow[lies over, from=2-2, to=4-2]
--   \arrow[lies over, from=2-4, to=4-4]
--   \arrow["m"', color={rgb,255:red,124;green,50;blue,189}, from=3-1, to=4-2]
--   \arrow[lies over, color={rgb,255:red,124;green,50;blue,189}, from=1-1, to=3-1]
--   \arrow["{h'}", color={rgb,255:red,204;green,51;blue,51}, curve={height=-12pt}, from=1-1, to=2-4]
--   \arrow["{\exists!}"', color={rgb,255:red,36;green,202;blue,28}, dashed, from=1-1, to=2-2]
-- \end{tikzcd}\]
-- ~~~

-- ```agda
--   field
--     universal : ∀ {u u'} (m : Hom u a) (h' : Hom[ f ∘ m ] u' b') → Hom[ m ] u' a'
--     commutes  : ∀ {u u'} (m : Hom u a) (h' : Hom[ f ∘ m ] u' b')
--               → f' ∘' universal m h' ≡ h'
--     unique    : ∀ {u u'} {m : Hom u a} {h' : Hom[ f ∘ m ] u' b'}
--               → (m' : Hom[ m ] u' a') → f' ∘' m' ≡ h' → m' ≡ universal m h'
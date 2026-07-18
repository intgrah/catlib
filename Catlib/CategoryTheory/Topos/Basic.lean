/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Closed.Types
public import Mathlib.CategoryTheory.Sites.CartesianClosed
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Topos.Sheaf
public import Catlib.CategoryTheory.Subobject.Classifier.Types

/-!
# Elementary topos

An elementary topos is a CCC with finite limits and a subobject classifier.

## References

* [S. MacLane and I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]

-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits

class ElementaryTopos (C : Type u) [Category.{v} C] extends
    CartesianMonoidalCategory C, MonoidalClosed C where
  [hasFiniteLimits : HasFiniteLimits C]
  [hasSubobjectClassifier : HasSubobjectClassifier C]

attribute [instance 100] ElementaryTopos.hasFiniteLimits
  ElementaryTopos.hasSubobjectClassifier

instance : ElementaryTopos (Type u) where
  toCartesianMonoidalCategory := inferInstance
  toMonoidalClosed := inferInstance

noncomputable instance {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C] :
    MonoidalClosed (C ⥤ Type w) :=
  let e : SmallModel C ⥤ Type w ≌ C ⥤ Type w :=
    Functor.asEquivalence ((Functor.whiskeringLeft _ _ _).obj (equivSmallModel _).functor)
  cartesianClosedOfEquiv e

noncomputable instance {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C] :
    ElementaryTopos (Cᵒᵖ ⥤ Type w) where
  toCartesianMonoidalCategory := inferInstance
  toMonoidalClosed := inferInstance

noncomputable instance {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [EssentiallySmall.{w} C] [HasSheafify J (Type w)] : ElementaryTopos (Sheaf J (Type w)) where
  toCartesianMonoidalCategory := inferInstance
  toMonoidalClosed := inferInstanceAs (MonoidalClosed (Sheaf J (Type w)))

end CategoryTheory

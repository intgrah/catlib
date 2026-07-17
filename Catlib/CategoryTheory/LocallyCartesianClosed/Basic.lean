/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour, Emily Riehl
-/
module

public import Mathlib.CategoryTheory.LocallyCartesianClosed.ExponentiableMorphism
public import Mathlib.CategoryTheory.LocallyCartesianClosed.Sections
public import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian

/-!
# Locally cartesian closed categories

There are several equivalent definitions of locally cartesian closed categories. For instance
the following two definitions are equivalent:

1. A locally cartesian closed category is a category `C` such that for every object `I`
the slice category `Over I` is cartesian closed.

2. Equivalently, a locally cartesian closed category is a category with pullbacks where
all morphisms `f` are exponentiable, that is the base change functor `Over.pullback f`
has a right adjoint for every morphisms `f : I ⟶ J`. This latter condition is equivalent to
exponentiability of `Over.mk f` – morphism `f` considered as an object of `Over J`.
The right adjoint of `Over.pullback f` is called the pushforward functor.

In this file we prove the equivalence of these definitions.

## Implementation notes

- The type class `ChosenPushforwards` provides pushforward functors, that is right adjoints to
  the chosen pullback functor, for every morphism in the category.

- `ChosenPushforwards.cartesianClosedOver` provides the cartesian closed structure of the slices
  from an instance of `ChosenPushforwards` on the category.

- The type class `LocallyCartesianClosed` extends `ChosenPushforwards` with the extra data carrying
  the witness of cartesian closedness of the slice categories. As such when instantiating a
  `LocallyCartesianClosed` structure, the cartesian closed structure of the slices will be filled
  in automatically. See `LocallyCartesianClosed.ofChosenPushforwards` and
  `LocallyCartesianClosed.ofCartesianClosedOver`.

  The advantage we obtain from this implementation is that when using a
  `LocallyCartesianClosed` structure, both the pushforward functor and the cartesian closedness
  of slices are automatically available, whereas for proving locally cartesian closedness proving
  only one of these two conditions is sufficient.

## Main results

- `exponentiableOverMk` shows that the exponentiable structure on a morphism `f` makes
the object `Over.mk f` in the appropriate slice category exponentiable.

- `ofExponentiable` shows that an exponentiable object in a slice category gives rise to an
exponentiable morphism.

- `CartesianClosedOver.chosenPushforwards` shows that a category with cartesian closed slices
has pushforwards along all morphisms.

- Conversely, `ChosenPushforwards.cartesianClosedOver` shows that, in a category with pushforwards
along all morphisms, the slice categories are cartesian closed.

- `LocallyCartesianClosed.cartesianClosed` proves that a locally cartesian closed category with a
terminal object is cartesian closed.

- `LocallyCartesianClosed.overLocallyCartesianClosed` shows that the slices of a locally cartesian
closed category are locally cartesian closed.

- `toOverUnitMonoidal` equips `toOverUnit : C ⥤ Over (𝟙_ C)` with a strong monoidal structure.

### References

The content here is based on the formalization of polynomial functors project at the
Trimester "Prospect of Formal Mathematics" at the Hausdorff Institute (HIM) in Bonn.

You can find the polynomial functors project at https://github.com/sinhp/Poly

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category MonoidalCategory CartesianMonoidalCategory

variable {C : Type u₁} [Category.{v₁} C]

attribute [local instance] ChosenPullbacksAlong.cartesianMonoidalCategoryOver

namespace ChosenPullbacksAlong

variable {Y Z X : C} (g : Z ⟶ X) [ChosenPullbacksAlong g]

@[reassoc (attr := simp)]
theorem fst'_naturality {U V : Over X} (p : V ⟶ U) :
    (Over.map g).map ((pullback g).map p) ≫ fst' U.hom g = fst' V.hom g ≫ p := by
  have := (mapPullbackAdj g).counit.naturality p
  rw [fst', fst']
  simp only [Functor.id_map, Functor.comp_map] at this
  exact this

@[reassoc (attr := simp)]
theorem pullback_map_left_fst {U V : Over X} (p : V ⟶ U) :
    ((pullback g).map p).left ≫ fst U.hom g = fst V.hom g ≫ p.left :=
  congr_arg CommaMorphism.left <| fst'_naturality g p

@[reassoc (attr := simp)]
theorem pullback_map_left_snd {U V : Over X} (f : V ⟶ U) :
    ((pullback g).map f).left ≫ ChosenPullbacksAlong.snd U.hom g =
      ChosenPullbacksAlong.snd V.hom g :=
  Over.w ((pullback g).map f)

end ChosenPullbacksAlong

namespace ChosenPullbacks

open ChosenPullbacksAlong

/-- The binary fan provided by `fst` and `snd`. -/
def binaryFan (T Y Z : C) (h : Limits.IsTerminal T)
    [ChosenPullbacksAlong <| h.from Z] :
    Limits.BinaryFan Y Z :=
  Limits.BinaryFan.mk (P := pullbackObj (h.from Y) (h.from Z)) (fst _ _) (snd _ _)

@[simp]
theorem binaryFan_pt {T Y Z : C} {h : Limits.IsTerminal T}
    [ChosenPullbacksAlong <| h.from Z] :
    (binaryFan T Y Z h).pt = pullbackObj (h.from Y) (h.from Z) :=
  rfl

@[simp]
theorem binaryFan_fst {T Y Z : C} {h : Limits.IsTerminal T}
    [ChosenPullbacksAlong <| h.from Z] :
    (binaryFan T Y Z h).fst = fst (h.from Y) (h.from Z) :=
  rfl

@[simp]
theorem binaryFan_snd {T Y Z : C} {h : Limits.IsTerminal T}
    [ChosenPullbacksAlong <| h.from Z] :
    (binaryFan T Y Z h).snd = snd (h.from Y) (h.from Z) :=
  rfl

/-- The binary fan constructed via the chosen pullback along the morphism from `Z` to the terminal
object is a binary product. -/
def binaryFanIsBinaryProduct (T Y Z : C) (h : Limits.IsTerminal T)
    [ChosenPullbacksAlong <| h.from Z] :
    Limits.IsLimit (binaryFan T Y Z h) :=
  Limits.BinaryFan.IsLimit.mk (binaryFan T Y Z h)
    (fun a b => lift a b)
    (by simp)
    (by simp)
    (fun f g m h₁ h₂ => by cat_disch)

/-- A cartesian monoidal category structure on `C` induced by chosen pullbacks and a terminal
object `T`. -/
@[instance_reducible]
def cartesianMonoidalCategory (T : C) (h : Limits.IsTerminal T) [ChosenPullbacks C] :
    CartesianMonoidalCategory C :=
  ofChosenFiniteProducts (C := C)
    ⟨Limits.asEmptyCone T, h⟩
    (fun Y Z ↦ ⟨_, binaryFanIsBinaryProduct T Y Z h⟩)

variable {X : C}

/-- The push-pull object `(Over.map Z.hom).obj ((pullback Z.hom).obj Y)` is isomorphic to the
cartesian product `Y ⊗ Z` in the slice category `Over X`.
Note: The monoidal structure of `Over X` is the one induced by the chosen pullbacks, namely
the one provided by `cartesianMonoidalCategoryOver`.
-/
@[simps!, implicit_reducible]
def mapPullbackIsoProd [ChosenPullbacks C] (Y Z : Over X) :
    (Over.map Z.hom).obj ((pullback Z.hom).obj Y) ≅ Y ⊗ Z :=
  Iso.refl _

@[simp]
lemma mapPullbackIsoProd_hom [ChosenPullbacks C] {Y Z : Over X} :
    (mapPullbackIsoProd Y Z).hom = 𝟙 _ :=
  rfl

/-- The pull-push composition `pullback Z.hom ⋙ map Z.hom` is naturally isomorphic
to the right tensor product functor `_ ⊗ Z` in the slice category `Over X`. -/
def pullbackMapNatIsoTensorRight [ChosenPullbacks C] (Z : Over X) :
    pullback Z.hom ⋙ Over.map Z.hom ≅ tensorRight Z :=
  NatIso.ofComponents
    (fun Y => mapPullbackIsoProd Y Z)
    (by
      intro Y' Y f
      change (pullback Z.hom ⋙ Over.map Z.hom).map f ≫
          𝟙 ((pullback Z.hom ⋙ Over.map Z.hom).obj Y) =
        𝟙 ((pullback Z.hom ⋙ Over.map Z.hom).obj Y') ≫ (tensorRight Z).map f
      rw [Category.comp_id, Category.id_comp]
      ext
      apply Over.tensorObj_ext
      · exact (pullback_map_left_fst Z.hom f).trans (Over.whiskerRight_left_fst f).symm
      · exact (pullback_map_left_snd Z.hom f).trans (Over.whiskerRight_left_snd f).symm)

@[simp]
theorem pullbackMapNatIsoTensorRight_hom_app [ChosenPullbacks C] {Y : Over X} (Z : Over X) :
    (pullbackMapNatIsoTensorRight Z).hom.app Y = 𝟙 _ := by
  cat_disch

/-- If `C` has chosen pullbacks, then `Over X` also has chosen pullbacks. -/
@[simps]
instance chosenPullbacksOver [ChosenPullbacks C] :
    ChosenPullbacks (Over X) := fun {Y Z : Over X} g => {
  pullback := Y.iteratedSliceForward ⋙ pullback g.left ⋙ Z.iteratedSliceBackward
  mapPullbackAdj :=
    Z.iteratedSliceEquiv.toAdjunction.comp (mapPullbackAdj g.left) |>.comp
        Y.iteratedSliceEquiv.symm.toAdjunction |>.ofNatIsoLeft
      (Functor.associator _ _ _ ≪≫
        Over.iteratedSliceEquivOverMapIso g)
  }

end ChosenPullbacks

section ToOverUnit

variable (C) [CartesianMonoidalCategory C] [ChosenPullbacks C]

noncomputable instance : (toOverUnit C).IsEquivalence :=
  (equivToOverUnit C).isEquivalence_inverse

/-- `toOverUnit : C ⥤ Over (𝟙_ C)` is strong monoidal: as the inverse of the equivalence
`equivToOverUnit` it preserves finite products, and a finite-product-preserving functor between
cartesian monoidal categories is monoidal. -/
@[instance_reducible]
noncomputable def toOverUnitMonoidal : (toOverUnit C).Monoidal :=
  .ofChosenFiniteProducts _

end ToOverUnit

namespace ExponentiableMorphism

open BraidedCategory ChosenPullbacksAlong ChosenPullbacks

attribute [local instance] BraidedCategory.ofCartesianMonoidalCategory

/-- A exponentiable morphism is an exponentiable object in the slice category of its codomain. -/
@[implicit_reducible]
def exponentiableOverMk [ChosenPullbacks C] {X I : C}
    (f : X ⟶ I) [ExponentiableMorphism f] :
    Closed (Over.mk f) where
  rightAdj := pullback f ⋙ pushforward f
  adj := .ofNatIsoLeft (F := pullback f ⋙ Over.map f)
    ((pullbackPushforwardAdj f).comp (mapPullbackAdj f))
    ((pullbackMapNatIsoTensorRight <| Over.mk f) ≪≫ (tensorLeftIsoTensorRight _).symm)

instance [CartesianMonoidalCategory C] [ChosenPullbacks C] (X : C) [Closed X] :
    ChosenPullbacksAlong (curryRightUnitorHom X) := by
  infer_instance

/-- If `X : Over I` is an exponentiable object then `X.hom : X.left ⟶ I` is an exponentiable
morphism. Here the pushforward functor along a morphism `f : I ⟶ J` is defined by the way of the
section functor `Over (Over.mk f) ⥤ Over J`. -/
@[implicit_reducible]
def ofExponentiable [ChosenPullbacks C] {I : C} (X : Over I)
    [Closed X] :
    ExponentiableMorphism X.hom :=
  ⟨X.iteratedSliceEquiv.inverse ⋙ Over.sections X,
    .ofNatIsoLeft
      (Adjunction.comp (Over.toOverSectionsAdj X) (Over.mk X.hom).iteratedSliceEquiv.toAdjunction)
      (toOverIteratedSliceForwardIsoPullback X.hom)⟩

end ExponentiableMorphism

variable (C)

/-- A category has `ChosenPushforwards` if every morphism is exponentiable. -/
class ChosenPushforwards [ChosenPullbacks C] where
  /-- A function assigning to every morphism `f : I ⟶ J` an exponentiable structure. -/
  exponentiable {I J : C} (f : I ⟶ J) : ExponentiableMorphism f := by infer_instance

namespace ChosenPushforwards

variable {C} [ChosenPullbacks C] [ChosenPushforwards C]

/-- In a category where pushforwards exists along all morphisms, every slice category `Over I` is
cartesian closed. -/
instance cartesianClosedOver (I : C) :
    MonoidalClosed (Over I) where
  closed X :=
    have := ChosenPushforwards.exponentiable X.hom
    ExponentiableMorphism.exponentiableOverMk X.hom

end ChosenPushforwards

namespace CartesianClosedOver

variable {C} [ChosenPullbacks C] {I J : C} [MonoidalClosed (Over J)]

instance (f : I ⟶ J) : ExponentiableMorphism f :=
  .ofExponentiable (Over.mk f)

/-- A category with cartesian closed slices has chosen pushforwards along all morphisms. -/
instance chosenPushforwards [Π (I : C), MonoidalClosed (Over I)] : ChosenPushforwards C where
  exponentiable f := ExponentiableMorphism.ofExponentiable (Over.mk f)

end CartesianClosedOver

open ChosenPushforwards

/-- A category with `ChosenPullbacks` is locally cartesian closed if every morphism in it
is exponentiable and all the slices are cartesian closed. -/
class LocallyCartesianClosed [ChosenPullbacks C] extends ChosenPushforwards C where
  /-- every slice category `Over I` is cartesian closed. This is filled in by default. -/
  cartesianClosedOver : Π (I : C), MonoidalClosed (Over I) := cartesianClosedOver

namespace LocallyCartesianClosed

variable {C} [ChosenPullbacks C]

/-- A category with pushforwards along all morphisms is locally cartesian closed. -/
instance ofChosenPushforwards [ChosenPushforwards C] : LocallyCartesianClosed C where

/-- A category with cartesian closed slices is locally cartesian closed. -/
instance ofCartesianClosedOver [Π (I : C), MonoidalClosed (Over I)] :
    LocallyCartesianClosed C where

variable [LocallyCartesianClosed C]

/-- Every morphism in a locally cartesian closed category is exponentiable. -/
instance exponentiableMorphism {I J : C} (f : I ⟶ J) : ExponentiableMorphism f :=
  ChosenPushforwards.exponentiable f

/-- A locally cartesian closed category with a terminal object is cartesian closed. -/
@[implicit_reducible]
noncomputable def cartesianClosed (T : C) (h : Limits.IsTerminal T) :
    letI := ChosenPullbacks.cartesianMonoidalCategory T h
    MonoidalClosed C :=
  letI := ChosenPullbacks.cartesianMonoidalCategory T h
  cartesianClosedOfEquiv <| equivToOverUnit C

/-- The slices of a locally cartesian closed category are locally cartesian closed. -/
@[implicit_reducible]
noncomputable def overLocallyCartesianClosed (I : C) : LocallyCartesianClosed (Over I) := by
  apply (config := { allowSynthFailures := true }) ofCartesianClosedOver
  intro X
  exact cartesianClosedOfEquiv X.iteratedSliceEquiv.symm

end LocallyCartesianClosed

end CategoryTheory

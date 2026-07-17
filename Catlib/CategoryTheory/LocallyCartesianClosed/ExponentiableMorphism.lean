/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour, Mario Carneiro, Jeremy Chen
-/
module

public import Catlib.CategoryTheory.LocallyCartesianClosed.BeckChevalley
public import Mathlib.CategoryTheory.Adjunction.Lifting.Right
public import Mathlib.CategoryTheory.Limits.Constructions.Equalizers
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-!
# Pullbacks of exponentiable morphisms are exponentiable

We show that the unit components of the adjunction `Over.map F ⊣ pullback F` are regular
monomorphisms, and deduce via the adjoint triangle theorem that any pullback of an
exponentiable morphism is exponentiable.
-/

@[expose] public section

namespace CategoryTheory

open Category Functor Adjunction Limits ChosenPullbacksAlong

universe v u

variable {C : Type u} [Category.{v} C]

namespace ChosenPullbacksAlong

variable {A B : C} (F : A ⟶ B) [ChosenPullbacksAlong F] (X : Over A)

/-- The unit components of the adjunction `Over.map F ⊣ pullback F` are regular
monomorphisms: on base-category components the fork is split by the first projections of
the chosen pullbacks, and `Over.forget` reflects the equalizer. -/
noncomputable def unitAppRegularMono : RegularMono ((mapPullbackAdj F).unit.app X) where
  Z := (Over.map F ⋙ pullback F).obj ((Over.map F ⋙ pullback F).obj X)
  left := (Over.map F ⋙ pullback F).map ((mapPullbackAdj F).unit.app X)
  right := (mapPullbackAdj F).unit.app ((Over.map F ⋙ pullback F).obj X)
  w := ((mapPullbackAdj F).unit.naturality ((mapPullbackAdj F).unit.app X)).symm
  isLimit :=
    isLimitOfIsLimitForkMap (Over.forget A) _ (IsSplitEqualizer.isEqualizer
      { leftRetraction := fst ((Over.map F).obj X).hom F
        rightRetraction := fst ((Over.map F).obj ((Over.map F ⋙ pullback F).obj X)).hom F
        condition := (congrArg CommaMorphism.left
          ((mapPullbackAdj F).unit.naturality ((mapPullbackAdj F).unit.app X))).symm
        ι_leftRetraction := unit_app_left_fst F X
        bottom_rightRetraction := unit_app_left_fst F ((Over.map F ⋙ pullback F).obj X)
        top_rightRetraction :=
          pullback_map_left_fst F ((Over.map F).map ((mapPullbackAdj F).unit.app X)) })

end ChosenPullbacksAlong

namespace ExponentiableMorphism

/-- Any pullback of an exponentiable morphism is exponentiable. -/
@[implicit_reducible]
noncomputable def ofIsPullback [ChosenPullbacks C] {P I J K : C} {fst : P ⟶ I} {snd : P ⟶ K}
    {f : I ⟶ J} {g : K ⟶ J} (H : IsPullback fst snd f g) [ExponentiableMorphism g] :
    ExponentiableMorphism fst :=
  haveI : HasBinaryProducts (Over I) := Over.ConstructProducts.over_binaryProduct_of_pullback
  haveI : HasEqualizers (Over I) := hasEqualizers_of_hasPullbacks_and_binary_products
  haveI : (ChosenPullbacksAlong.pullback fst ⋙ Over.map snd).IsLeftAdjoint :=
    (((mapPullbackAdj f).comp (pullbackPushforwardAdj g)).ofNatIsoLeft
      (pullbackMapIsoSquare H.flip).symm).isLeftAdjoint
  haveI : (ChosenPullbacksAlong.pullback fst).IsLeftAdjoint :=
    isLeftAdjoint_triangle_lift (ChosenPullbacksAlong.pullback fst) (mapPullbackAdj snd)
      (unitAppRegularMono snd)
  { pushforward := (ChosenPullbacksAlong.pullback fst).rightAdjoint
    pullbackPushforwardAdj := Adjunction.ofIsLeftAdjoint _ }

end ExponentiableMorphism

end CategoryTheory

/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Catlib.CategoryTheory.LocallyCartesianClosed.Basic

/-!
# Locally cartesian closed cartesian monoidal categories are cartesian closed

AKA, LCCCMCs are CCCs
-/

@[expose] public section

namespace CategoryTheory.LocallyCartesianClosed

open MonoidalCategory CartesianMonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [ChosenPullbacks C]

@[implicit_reducible]
noncomputable def monoidalClosed [LocallyCartesianClosed C]
    [cmcGiven : CartesianMonoidalCategory C] : MonoidalClosed C :=
  @cartesianClosedOfEquiv C _
    (ChosenPullbacks.cartesianMonoidalCategory (𝟙_ C) isTerminalTensorUnit) C _ cmcGiven
    Equivalence.refl (cartesianClosed (𝟙_ C) isTerminalTensorUnit)

end CategoryTheory.LocallyCartesianClosed

/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.CategoryTheory.Adjunction.Comma
public import Mathlib.CategoryTheory.Functor.KanExtension.Basic

/-!
# Kan extensions along discrete inclusion

- `Discrete.lan` sends a family `F` to `fun c => Σ d, (d ⟶ c) × F ⟨d⟩`;
- `Discrete.ran` sends a family `F` to `fun c => Π d, (c ⟶ d) → F ⟨d⟩`.
-/

@[expose] public section

namespace CategoryTheory.Discrete

open Functor

universe v u

variable (C : Type u) [Category.{v} C]

abbrev inclusion : Discrete C ⥤ C := Discrete.functor id

/-- Left Kan extension given by coend formula `Σ d, (d ⟶ c) × F ⟨d⟩`. -/
@[simps]
def lan : (Discrete C ⥤ Type max u v) ⥤ (C ⥤ Type max u v) where
  obj F :=
    { obj c := Σ d : C, (d ⟶ c) × F.obj ⟨d⟩
      map g := ↾fun ⟨d, f, x⟩ => ⟨d, f ≫ g, x⟩ }
  map α := { app c := ↾fun ⟨d, f, x⟩ => ⟨d, f, α.app ⟨d⟩ x⟩ }

/-- Righ Kan extension functor given by end formula `Π d, (c ⟶ d) → F ⟨d⟩`. -/
@[simps]
def ran : (Discrete C ⥤ Type max u v) ⥤ (C ⥤ Type max u v) where
  obj F :=
    { obj c := Π d : C, (c ⟶ d) → F.obj ⟨d⟩
      map g := ↾fun x d h => x d (g ≫ h) }
  map α := { app c := ↾fun x d h => α.app ⟨d⟩ (x d h) }

def lanAdjunction : lan C ⊣ (whiskeringLeft (Discrete C) C (Type max u v)).obj (inclusion C) :=
  .mkOfUnitCounit
    { unit :=
        { app F :=
            { app c := ↾fun x => ⟨c.as, 𝟙 c.as, x⟩
              naturality := by
                intro ⟨c⟩ ⟨c'⟩ ⟨⟨h⟩⟩
                obtain rfl : c = c' := h
                simp }
          naturality := by intros; rfl }
      counit :=
        { app X :=
            { app c := ↾fun ⟨d, f, x⟩ => X.map f x
              naturality := by
                intro c c' g
                ext ⟨d, f, x⟩
                exact X.map_comp_apply f g x }
          naturality := by
            intro X Y f
            ext c ⟨d, g, x⟩
            exact (NatTrans.naturality_apply f g x).symm }
      left_triangle := by
        ext F c ⟨d, f, x⟩
        change (⟨d, 𝟙 d ≫ f, x⟩ : Σ d : C, (d ⟶ c) × F.obj ⟨d⟩) = ⟨d, f, x⟩
        rw [Category.id_comp]
      right_triangle := by
        ext X c x
        exact X.map_id_apply c.as x }

def ranAdjunction : (whiskeringLeft (Discrete C) C (Type max u v)).obj (inclusion C) ⊣ ran C :=
  .mkOfUnitCounit
    { unit :=
        { app X :=
            { app c := ↾fun x d h => X.map h x
              naturality := by
                intro c c' g
                ext x
                funext d h
                exact (X.map_comp_apply g h x).symm }
          naturality := by
            intro X Y f
            ext c x
            funext d h
            exact (NatTrans.naturality_apply f h x).symm }
      counit :=
        { app F :=
            { app c := ↾fun x => x c.as (𝟙 c.as)
              naturality := by
                intro ⟨c⟩ ⟨c'⟩ ⟨⟨h⟩⟩
                obtain rfl : c = c' := h
                simp }
          naturality := by intros; rfl }
      left_triangle := by
        ext X c x
        exact X.map_id_apply c.as x
      right_triangle := by
        ext F c x
        funext d h
        exact congrArg (x d) (Category.comp_id h) }

variable {C} (F : Discrete C ⥤ Type max u v)

instance isLeftKanExtension :
    (lan C).obj F |>.IsLeftKanExtension <| (lanAdjunction C).unit.app F :=
  ⟨⟨mkInitialOfLeftAdjoint _ (lanAdjunction C) F⟩⟩

instance isRightKanExtension :
    (ran C).obj F |>.IsRightKanExtension <| (ranAdjunction C).counit.app F :=
  ⟨⟨mkTerminalOfRightAdjoint _ (ranAdjunction C) F⟩⟩

end CategoryTheory.Discrete

/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Functor.TwoSquare
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Discrete.Basic

/-!
# Cartesian natural transformations

A natural transformation is cartesian if all its naturality squares are pullbacks. We prove
closure under vertical and horizontal composition, whiskering, and `TwoSquare` pasting, and
show that a cartesian transformation over a domain with a terminal object is an isomorphism
as soon as its component at the terminal object is.
-/

@[expose] public section

namespace CategoryTheory.NatTrans

open Limits Functor

universe v' u' v u

variable {J : Type v'} [Category.{u'} J] {C : Type u} [Category.{v} C]
variable {D : Type*} [Category D]

/-- A natural transformation is *cartesian* if all its naturality squares are pullbacks. -/
def IsCartesian {F G : J ⥤ C} (α : F ⟶ G) : Prop :=
  ∀ ⦃i j : J⦄ (f : i ⟶ j), IsPullback (F.map f) (α.app i) (α.app j) (G.map f)

theorem isCartesian_of_isIso {F G : J ⥤ C} (α : F ⟶ G) [IsIso α] : IsCartesian α :=
  fun _ _ f => IsPullback.of_vert_isIso ⟨NatTrans.naturality _ f⟩

theorem isIso_of_isCartesian [HasTerminal J] {F G : J ⥤ C} (α : F ⟶ G) (hα : IsCartesian α)
    [IsIso (α.app (⊤_ J))] : IsIso α :=
  have := fun j => (hα (terminal.from j)).isIso_snd_of_isIso
  NatIso.isIso_of_isIso_app α

theorem isCartesian_of_discrete {ι : Type*} {F G : Discrete ι ⥤ C} (α : F ⟶ G) :
    IsCartesian α := by
  rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩
  exact IsPullback.of_horiz_isIso ⟨α.naturality ⟨⟨rfl⟩⟩⟩

theorem isCartesian_of_isPullback_to_terminal [HasTerminal J] {F G : J ⥤ C} (α : F ⟶ G)
    (pb : ∀ j, IsPullback (F.map (terminal.from j)) (α.app j) (α.app (⊤_ J))
      (G.map (terminal.from j))) :
    IsCartesian α := by
  intro i j f
  apply IsPullback.of_right
    (h₁₂ := F.map (terminal.from j))
    (h₂₂ := G.map (terminal.from j))
  · simpa [← F.map_comp, ← G.map_comp] using pb i
  · exact α.naturality f
  · exact pb j

namespace IsCartesian

theorem comp {F G H : J ⥤ C} {α : F ⟶ G} {β : G ⟶ H} (hα : IsCartesian α)
    (hβ : IsCartesian β) : IsCartesian (α ≫ β) :=
  fun _ _ f => (hα f).paste_vert (hβ f)

theorem whiskerRight {F G : J ⥤ C} {α : F ⟶ G} (hα : IsCartesian α) (H : C ⥤ D)
    [∀ (i j : J) (f : j ⟶ i), PreservesLimit (cospan (α.app i) (G.map f)) H] :
    IsCartesian (whiskerRight α H) :=
  fun _ _ f => (hα f).map H

theorem whiskerLeft {K : Type*} [Category K] {F G : J ⥤ C} {α : F ⟶ G}
    (hα : IsCartesian α) (H : K ⥤ J) : IsCartesian (whiskerLeft H α) :=
  fun _ _ f => hα (H.map f)

theorem hcomp {K : Type*} [Category K] {F G : J ⥤ C} {M N : C ⥤ K} {α : F ⟶ G} {β : M ⟶ N}
    (hα : IsCartesian α) (hβ : IsCartesian β)
    [∀ (i j : J) (f : j ⟶ i), PreservesLimit (cospan (α.app i) (G.map f)) M] :
    IsCartesian (NatTrans.hcomp α β) := by
  have hc := (hα.whiskerRight M).comp (hβ.whiskerLeft G)
  intro i j f
  convert hc f using 2 <;>
    exact (NatTrans.hcomp_eq_whiskerLeft_comp_whiskerRight α β).trans
      (whiskerLeft_comp_whiskerRight α β)

open TwoSquare

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} C₄]
  {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {B : C₃ ⥤ C₄}
variable {C₅ : Type u₅} {C₆ : Type u₆} {C₇ : Type u₇} {C₈ : Type u₈}
  [Category.{v₅} C₅] [Category.{v₆} C₆] [Category.{v₇} C₇] [Category.{v₈} C₈]
  {T' : C₂ ⥤ C₅} {R' : C₅ ⥤ C₆} {B' : C₄ ⥤ C₆} {L' : C₃ ⥤ C₇} {R'' : C₄ ⥤ C₈} {B'' : C₇ ⥤ C₈}

theorem vComp {w : TwoSquare T L R B} {w' : TwoSquare B L' R'' B''}
    [∀ (i j : C₁) (f : j ⟶ i), PreservesLimit (cospan (w.app i) ((L ⋙ B).map f)) R''] :
    IsCartesian w → IsCartesian w' → IsCartesian (w ≫ᵥ w') :=
  fun cw cw' =>
    (isCartesian_of_isIso _).comp <|
    (cw.whiskerRight _).comp <|
    (isCartesian_of_isIso _).comp <|
    (cw'.whiskerLeft _).comp <|
    (isCartesian_of_isIso _)

theorem hComp {w : TwoSquare T L R B} {w' : TwoSquare T' R R' B'}
    [∀ (i j : C₁) (f : j ⟶ i), PreservesLimit (cospan (w.app i) ((L ⋙ B).map f)) B'] :
    IsCartesian w → IsCartesian w' → IsCartesian (w ≫ₕ w') :=
  fun cw cw' =>
    (isCartesian_of_isIso _).comp <|
    (cw'.whiskerLeft _).comp <|
    (isCartesian_of_isIso _).comp <|
    (cw.whiskerRight _).comp <|
    (isCartesian_of_isIso _)

section Mates

variable {E : Type u₅} {F : Type u₆} [Category.{v₅} E] [Category.{v₆} F]
  {G : C₁ ⥤ E} {H : C₂ ⥤ F} {L₁ : C₁ ⥤ C₂} {R₁ : C₂ ⥤ C₁} {L₂ : E ⥤ F} {R₂ : F ⥤ E}

/-- The mate of a cartesian square is cartesian, provided the unit and counit being
pasted in are and the right adjoint `R₂` preserves the relevant pullbacks. -/
theorem mateEquiv (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) {α : TwoSquare G L₁ L₂ H}
    (hα : IsCartesian α.natTrans) (hε : IsCartesian adj₁.counit)
    (hη : IsCartesian adj₂.unit)
    [∀ (i j : C₁) (f : j ⟶ i), PreservesLimit (cospan (α.app i) ((L₁ ⋙ H).map f)) R₂]
    [∀ (i j : C₂) (f : j ⟶ i),
      PreservesLimit (cospan (adj₁.counit.app i) ((𝟭 C₂).map f)) (H ⋙ R₂)] :
    IsCartesian (CategoryTheory.mateEquiv adj₁ adj₂ α).natTrans :=
  (isCartesian_of_isIso _).comp <|
  (hη.whiskerLeft _).comp <|
  (isCartesian_of_isIso _).comp <|
  ((isCartesian_of_isIso _).whiskerLeft _).comp <|
  ((hα.whiskerRight _).whiskerLeft _).comp <|
  ((isCartesian_of_isIso _).whiskerLeft _).comp <|
  (isCartesian_of_isIso _).comp <|
  (hε.whiskerRight _).comp
  (isCartesian_of_isIso _)

/-- The inverse mate of a cartesian square is cartesian, provided the unit and counit
being pasted in are and the left adjoint `L₂` preserves the relevant pullbacks. -/
theorem mateEquiv_symm (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) {α : TwoSquare R₁ H G R₂}
    (hα : IsCartesian α.natTrans) (hη : IsCartesian adj₁.unit)
    (hε : IsCartesian adj₂.counit)
    [∀ (i j : C₁) (f : j ⟶ i),
      PreservesLimit (cospan (adj₁.unit.app i) ((L₁ ⋙ R₁).map f)) (G ⋙ L₂)]
    [∀ (i j : C₁) (f : j ⟶ i), PreservesLimit
      (cospan ((Functor.whiskerLeft L₁ α.natTrans).app i) ((L₁ ⋙ (H ⋙ R₂)).map f)) L₂] :
    IsCartesian ((CategoryTheory.mateEquiv adj₁ adj₂).symm α).natTrans :=
  (isCartesian_of_isIso _).comp <|
  (hη.whiskerRight _).comp <|
  (isCartesian_of_isIso _).comp <|
  (isCartesian_of_isIso _).comp <|
  ((hα.whiskerLeft _).whiskerRight _).comp <|
  (isCartesian_of_isIso _).comp <|
  (isCartesian_of_isIso _).comp <|
  (hε.whiskerLeft _).comp
  (isCartesian_of_isIso _)

end Mates

end IsCartesian

end CategoryTheory.NatTrans

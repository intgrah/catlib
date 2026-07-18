/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Catlib.CategoryTheory.Category.Inj.Defs
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Data.Finite.Prod

/-!
# Category of finite types and injections

`FinInj`
-/

@[expose] public section

namespace CategoryTheory

universe u

/-- Category of finite types and injections -/
abbrev FinInj := ObjectProperty.FullSubcategory (C := Inj.{u}) Finite

namespace FinInj

abbrev of (X : Type u) [Finite X] : FinInj :=
  ⟨X, inferInstance⟩

instance instCoeSort : CoeSort FinInj (Type u) :=
  ⟨fun X ↦ X.obj⟩

instance : Inhabited FinInj :=
  ⟨of PEmpty⟩

instance {X : FinInj} : Finite X :=
  X.property

@[simps!]
abbrev incl : FinInj ⥤ Inj := ObjectProperty.ι _

instance : incl.Full := ObjectProperty.full_ι _
instance : incl.Faithful := ObjectProperty.faithful_ι _

abbrev homMk {X Y : FinInj.{u}} (e : ↥X ↪ ↥Y) : X ⟶ Y :=
  InducedCategory.homMk (Inj.Hom.ofEmbedding e)

abbrev emb {X Y : FinInj.{u}} (f : X ⟶ Y) : ↥X ↪ ↥Y :=
  f.hom.emb

@[ext]
lemma hom_ext {X Y : FinInj.{u}} {f g : X ⟶ Y} (h : ∀ x, emb f x = emb g x) : f = g :=
  ObjectProperty.hom_ext _ (Inj.Hom.ext (Function.Embedding.ext h))

end FinInj

end CategoryTheory

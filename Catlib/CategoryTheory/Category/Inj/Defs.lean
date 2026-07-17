/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.Logic.Embedding.Basic

/-! # Category of types and injections

Objects are types and morphisms are `Function.Embedding`
-/

@[expose] public section

namespace CategoryTheory

universe u

/-- Type synonym for `Type u` with different category instance -/
def Inj := Type u

namespace Inj
variable {X Y Z : Inj.{u}}

@[ext]
structure Hom (X Y : Inj.{u}) : Type u where
  /-- Build a morphism from an embedding -/
  ofEmbedding ::
  /-- Get the embedding from a morphism -/
  emb : X ↪ Y

initialize_simps_projections Hom (as_prefix emb)

instance instLargeCategory : LargeCategory Inj where
  Hom := Hom
  id X := .ofEmbedding (.refl X)
  comp f g := .ofEmbedding (f.emb.trans g.emb)

namespace Hom

@[simp] protected lemma emb_id (X : Inj.{u}) : emb (𝟙 X) = .refl X := rfl
@[simp] protected lemma emb_comp (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).emb = f.emb.trans g.emb := rfl

theorem emb_id_apply (x : X) : emb (𝟙 X) x = x := rfl

theorem emb_comp_apply (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g).emb x = g.emb (f.emb x) := rfl

end Hom

end Inj

end CategoryTheory

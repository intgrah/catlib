/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Data.Finset.Insert
public import Mathlib.GroupTheory.GroupAction.Support

/-!
# Nominal sets

A type `α` with an action of `Perm 𝔸` is nominal when every element is supported,
in the sense of `MulAction.Supports`, by a finite set of atoms.

## Main definitions

* `Nominal 𝔸 α`: the `Perm 𝔸`-action on `α` is finitely supported.
-/

@[expose] public section

open Equiv MulAction

variable (𝔸 α : Type*)

/-- A `Perm 𝔸`-action is nominal when every element is supported by a finite set
of atoms. -/
class Nominal [MulAction (Perm 𝔸) α] : Prop where
  finset_support (x : α) : ∃ s : Finset 𝔸, Supports (Perm 𝔸) (↑s : Set 𝔸) x

instance Equiv.Perm.nominal : Nominal 𝔸 𝔸 where
  finset_support a :=
    ⟨{a}, supports_of_mem (Perm 𝔸) (Finset.mem_coe.mpr (Finset.mem_singleton_self a))⟩

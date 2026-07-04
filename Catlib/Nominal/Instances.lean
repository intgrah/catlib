/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Catlib.Nominal.Supp

/-!
# Nominal instances for products and sums
-/

@[expose] public section

open Equiv MulAction

variable {𝔸 α β : Type*} [MulAction (Perm 𝔸) α] [MulAction (Perm 𝔸) β]

theorem Nominal.of_forall_smul_eq (h : ∀ (π : Perm 𝔸) (x : α), π • x = x) :
    Nominal 𝔸 α :=
  ⟨fun x => ⟨∅, fun π _ => h π x⟩⟩

instance Prod.nominal [DecidableEq 𝔸] [Nominal 𝔸 α] [Nominal 𝔸 β] : Nominal 𝔸 (α × β) where
  finset_support p := by
    have ⟨s, hs⟩ := ‹Nominal 𝔸 α›.finset_support p.1
    have ⟨t, ht⟩ := ‹Nominal 𝔸 β›.finset_support p.2
    refine ⟨s ∪ t, ?_⟩
    rw [Finset.coe_union]
    exact (hs.mono Set.subset_union_left).prodMk (ht.mono Set.subset_union_right)

instance Sum.nominal [Nominal 𝔸 α] [Nominal 𝔸 β] : Nominal 𝔸 (α ⊕ β) where
  finset_support
    | .inl x =>
      have ⟨s, hs⟩ := Nominal.finset_support x
      ⟨s, hs.sumInl⟩
    | .inr y =>
      have ⟨s, hs⟩ := Nominal.finset_support y
      ⟨s, hs.sumInr⟩

namespace Nominal

variable (𝔸) [Infinite 𝔸]

theorem supp_atom [DecidableEq 𝔸] (a : 𝔸) : supp 𝔸 a = {a} := by
  apply Finset.Subset.antisymm
  · exact supp_subset
      (supports_of_mem (Perm 𝔸) (Finset.mem_coe.mpr (Finset.mem_singleton_self a)))
  · rw [Finset.singleton_subset_iff]
    by_contra ha
    have ⟨b, hb, hba⟩ := exists_fresh a ({a} : Finset 𝔸)
    have hswap : swap a b • a = a := Fresh.swap_smul ha hb
    have hab : b = a := (swap_apply_left a b).symm.trans hswap
    exact hba (hab ▸ Finset.mem_singleton_self a)

theorem supp_prodMk [DecidableEq 𝔸] [Nominal 𝔸 α] [Nominal 𝔸 β] (x : α) (y : β) :
    supp 𝔸 (x, y) = supp 𝔸 x ∪ supp 𝔸 y := by
  apply Finset.Subset.antisymm
  · apply supp_subset
    rw [Finset.coe_union]
    exact ((supp_supports 𝔸 x).mono Set.subset_union_left).prodMk
      ((supp_supports 𝔸 y).mono Set.subset_union_right)
  · refine Finset.union_subset (supp_subset fun π hπ => ?_) (supp_subset fun π hπ => ?_)
    · exact congrArg Prod.fst (supp_supports 𝔸 (x, y) π hπ)
    · exact congrArg Prod.snd (supp_supports 𝔸 (x, y) π hπ)

variable {𝔸} in
theorem fresh_prodMk_iff [DecidableEq 𝔸] [Nominal 𝔸 α] [Nominal 𝔸 β] {a : 𝔸} {x : α}
    {y : β} : a ♯ (x, y) ↔ a ♯ x ∧ a ♯ y := by
  simp only [Fresh, supp_prodMk, Finset.mem_union, not_or]

theorem supp_sumInl [Nominal 𝔸 α] [Nominal 𝔸 β] (x : α) :
    supp 𝔸 (Sum.inl x : α ⊕ β) = supp 𝔸 x := by
  apply Finset.Subset.antisymm
  · exact supp_subset (supp_supports 𝔸 x).sumInl
  · refine supp_subset fun π hπ => ?_
    have h := supp_supports 𝔸 (Sum.inl x : α ⊕ β) π hπ
    rw [Sum.smul_inl] at h
    exact Sum.inl.inj h

theorem supp_sumInr [Nominal 𝔸 α] [Nominal 𝔸 β] (y : β) :
    supp 𝔸 (Sum.inr y : α ⊕ β) = supp 𝔸 y := by
  apply Finset.Subset.antisymm
  · exact supp_subset (supp_supports 𝔸 y).sumInr
  · refine supp_subset fun π hπ => ?_
    have h := supp_supports 𝔸 (Sum.inr y : α ⊕ β) π hπ
    rw [Sum.smul_inr] at h
    exact Sum.inr.inj h

end Nominal

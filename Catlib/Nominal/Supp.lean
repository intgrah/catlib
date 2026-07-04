/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Catlib.Nominal.Defs
public import Mathlib.Algebra.Group.Action.Prod
public import Mathlib.Algebra.Group.Action.Sum
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.Order.Bounds.Defs
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Lattice.Basic

/-!
# Least supports

Supports for a `Perm 𝔸`-action are closed under intersection,
`MulAction.Supports.inter`. Consequently the supports of an element of a nominal set have a
least element, `Nominal.supp`.

## References

* A. M. Pitts, *Nominal Sets: Names and Symmetry in Computer Science*, Cambridge
  University Press, 2013.
-/

@[expose] public section

open Equiv

namespace MulAction

section Group

variable {G α β : Type*} [Group G] [MulAction G α] [MulAction G β] {s : Set α} {b : β}
variable {p q : G}

@[to_additive]
theorem Supports.smul_eq_smul (hb : Supports G s b) (h : ∀ a ∈ s, p • a = q • a) :
    p • b = q • b := by
  have hfix : (q⁻¹ * p) • b = b := hb _ fun a ha => by rw [mul_smul, h a ha, inv_smul_smul]
  rw [← mul_inv_cancel_left q p, mul_smul, hfix]

open scoped Pointwise in
@[to_additive]
theorem Supports.smul' (g : G) (hb : Supports G s b) : Supports G (g • s) (g • b) := by
  intro g' hg'
  have hfix : (g⁻¹ * g' * g) • b = b := hb _ fun a ha => by
    rw [mul_smul, mul_smul, hg' (Set.smul_mem_smul_set ha), inv_smul_smul]
  rw [← mul_smul, ← mul_inv_cancel_left g (g' * g), ← mul_assoc g⁻¹ g' g, mul_smul, hfix]

@[to_additive]
theorem supports_iff_fixingSubgroup_le_stabilizer :
    Supports G s b ↔ fixingSubgroup G s ≤ stabilizer G b := by
  simp [Supports, SetLike.le_def, mem_fixingSubgroup_iff]

end Group

section SMul

variable {G γ α β : Type*} [SMul G γ] [SMul G α] [SMul G β] {s : Set γ} {x : α}

@[to_additive]
theorem Supports.map (hx : Supports G s x) (f : α → β)
    (hf : ∀ (g : G) (y : α), f (g • y) = g • f y) : Supports G s (f x) :=
  fun g hg => by rw [← hf, hx g hg]

@[to_additive]
theorem Supports.prodMk {b : α} {c : β} (hb : Supports G s b) (hc : Supports G s c) :
    Supports G s (b, c) :=
  fun g hg => by rw [Prod.smul_mk, hb g hg, hc g hg]

@[to_additive]
theorem Supports.sumInl {b : α} (hb : Supports G s b) : Supports G s (Sum.inl b : α ⊕ β) :=
  fun g hg => by rw [Sum.smul_inl, hb g hg]

@[to_additive]
theorem Supports.sumInr {c : β} (hc : Supports G s c) : Supports G s (Sum.inr c : α ⊕ β) :=
  fun g hg => by rw [Sum.smul_inr, hc g hg]

end SMul

section Perm

variable {𝔸 α : Type*} [DecidableEq 𝔸] [MulAction (Perm 𝔸) α]
variable {s t u : Set 𝔸} {x : α} {a b c : 𝔸}

private theorem Supports.swap_smul (h : Supports (Perm 𝔸) s x) (ha : a ∉ s)
    (hb : b ∉ s) : swap a b • x = x :=
  h _ fun _ hd =>
    swap_apply_of_ne_of_ne (ne_of_mem_of_not_mem hd ha) (ne_of_mem_of_not_mem hd hb)

private theorem swap_smul_conj (hab : a ≠ b) (hcb : c ≠ b)
    (hac : swap a c • x = x) (hcb' : swap c b • x = x) : swap a b • x = x := by
  rw [← swap_mul_swap_mul_swap hcb.symm hab.symm, swap_comm c a, swap_comm b c, mul_smul,
    mul_smul, hac, hcb', hac]

private theorem swap_smul_inter [Infinite 𝔸] (hs : s.Finite) (ht : t.Finite)
    (hsx : Supports (Perm 𝔸) s x) (htx : Supports (Perm 𝔸) t x)
    (ha : a ∉ s ∩ t) (hb : b ∉ s ∩ t) : swap a b • x = x := by
  have hS : (s ∪ t ∪ {a, b}).Finite := (hs.union ht).union (Set.toFinite _)
  have ⟨c, hc⟩ := hS.infinite_compl.nonempty
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
    not_or] at hc
  have ⟨⟨hcs, hct⟩, _, hcb⟩ := hc
  by_cases has : a ∈ s
  · have hat : a ∉ t := fun h => ha ⟨has, h⟩
    by_cases hbt : b ∈ t
    · have hbs : b ∉ s := fun h => hb ⟨h, hbt⟩
      exact swap_smul_conj (ne_of_mem_of_not_mem has hbs) hcb
        (htx.swap_smul hat hct) (hsx.swap_smul hcs hbs)
    · exact htx.swap_smul hat hbt
  · by_cases hbs : b ∈ s
    · have hbt : b ∉ t := fun h => hb ⟨hbs, h⟩
      by_cases hat : a ∈ t
      · exact swap_smul_conj (ne_of_mem_of_not_mem hbs has).symm hcb
          (hsx.swap_smul has hcs) (htx.swap_smul hct hbt)
      · exact htx.swap_smul hat hbt
    · exact hsx.swap_smul has hbs

private theorem exists_smul_eq_eqOn {π : Perm 𝔸}
    (hsw : ∀ a b, a ∉ u → b ∉ u → swap a b • x = x) (hπ : ∀ c ∈ u, π c = c) (D : Finset 𝔸) :
    ∃ ρ : Perm 𝔸, ρ • x = x ∧ (∀ c ∈ u, ρ c = c) ∧ ∀ d ∈ D, ρ d = π d := by
  induction D using Finset.induction_on with
  | empty => exact ⟨1, one_smul _ _, fun _ _ => rfl, nofun⟩
  | insert d D' hd ih =>
    have ⟨ρ', hρ'x, hρ'u, hρ'D⟩ := ih
    by_cases hfe : ρ' d = π d
    · refine ⟨ρ', hρ'x, hρ'u, ?_⟩
      intro e he
      rcases Finset.mem_insert.mp he with rfl | he'
      · exact hfe
      · exact hρ'D e he'
    · have hdu : d ∉ u := fun h => hfe (by rw [hρ'u d h, hπ d h])
      have heu : π d ∉ u := fun h => hdu (π.injective (hπ (π d) h) ▸ h)
      have hfu : ρ' d ∉ u := fun h => hdu (ρ'.injective (hρ'u (ρ' d) h) ▸ h)
      refine ⟨swap (ρ' d) (π d) * ρ', ?_, ?_, ?_⟩
      · rw [mul_smul, hρ'x, hsw _ _ hfu heu]
      · intro e he
        rw [Perm.mul_apply, hρ'u e he, swap_apply_of_ne_of_ne
          (ne_of_mem_of_not_mem he hfu) (ne_of_mem_of_not_mem he heu)]
      · intro e he
        rcases Finset.mem_insert.mp he with rfl | he'
        · rw [Perm.mul_apply, swap_apply_left]
        · rw [Perm.mul_apply, hρ'D e he']
          apply swap_apply_of_ne_of_ne
          · rw [← hρ'D e he']
            exact ρ'.injective.ne (ne_of_mem_of_not_mem he' hd)
          · exact π.injective.ne (ne_of_mem_of_not_mem he' hd)

theorem swap_smul_smul (π : Perm 𝔸) (a c : 𝔸) (x : α) :
    swap (π a) (π c) • π • x = π • swap a c • x := by
  rw [← mul_smul, ← mul_swap_eq_swap_mul, mul_smul]

/-- Transport a swap along a change of fresh name. -/
theorem Supports.swap_swap_smul {d : 𝔸} (hs : Supports (Perm 𝔸) s x)
    (hc : c ∉ s) (hd : d ∉ s) (hca : c ≠ a) (hda : d ≠ a) :
    swap a d • x = swap c d • swap a c • x := by
  rw [← mul_smul]
  apply hs.smul_eq_smul
  intro e he
  rw [Perm.smul_def, Perm.smul_def, Perm.mul_apply]
  have hec : e ≠ c := ne_of_mem_of_not_mem he hc
  have hed : e ≠ d := ne_of_mem_of_not_mem he hd
  by_cases hea : e = a
  · subst hea
    simp only [swap_apply_left]
  · rw [swap_apply_of_ne_of_ne hea hed, swap_apply_of_ne_of_ne hea hec,
      swap_apply_of_ne_of_ne hec hed]

/-- Supports are closed under intersection. -/
theorem Supports.inter [Infinite 𝔸] (hs : s.Finite) (ht : t.Finite)
    (hsx : Supports (Perm 𝔸) s x) (htx : Supports (Perm 𝔸) t x) :
    Supports (Perm 𝔸) (s ∩ t) x := by
  intro π hπ
  have hsw a b (ha : a ∉ s ∩ t) (hb : b ∉ s ∩ t) : swap a b • x = x :=
    swap_smul_inter hs ht hsx htx ha hb
  have ⟨ρ, hρx, _, hρD⟩ := exists_smul_eq_eqOn hsw hπ hs.toFinset
  have heq : π • x = ρ • x := hsx.smul_eq_smul fun a ha => by
    rw [Perm.smul_def, Perm.smul_def, hρD a (hs.mem_toFinset.mpr ha)]
  rw [heq, hρx]

end Perm

end MulAction

namespace Nominal

open MulAction

variable {𝔸 α : Type*} [Infinite 𝔸] [MulAction (Perm 𝔸) α] [Nominal 𝔸 α]

section
variable (𝔸)

open scoped Classical in
theorem exists_isLeast_supports (x : α) :
    ∃ s : Finset 𝔸, IsLeast {t : Finset 𝔸 | Supports (Perm 𝔸) (t : Set 𝔸) x} s := by
  have hex : ∃ n, ∃ s : Finset 𝔸, s.card = n ∧ Supports (Perm 𝔸) (s : Set 𝔸) x :=
    have ⟨s, hs⟩ := Nominal.finset_support x
    ⟨s.card, s, rfl, hs⟩
  have ⟨s, hcard, hs⟩ := Nat.find_spec hex
  refine ⟨s, hs, fun t ht => ?_⟩
  have hst : Supports (Perm 𝔸) (↑(s ∩ t) : Set 𝔸) x := by
    rw [Finset.coe_inter]
    exact hs.inter s.finite_toSet t.finite_toSet ht
  have hmin : Nat.find hex ≤ (s ∩ t).card := Nat.find_min' hex ⟨s ∩ t, rfl, hst⟩
  have hcap : s ∩ t = s :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left (hcard ▸ hmin)
  exact hcap ▸ Finset.inter_subset_right

/-- The least finite support of an element of a nominal set. -/
noncomputable def supp (x : α) : Finset 𝔸 :=
  (exists_isLeast_supports 𝔸 x).choose

theorem isLeast_supp (x : α) :
    IsLeast {t : Finset 𝔸 | Supports (Perm 𝔸) (t : Set 𝔸) x} (supp 𝔸 x) :=
  (exists_isLeast_supports 𝔸 x).choose_spec

theorem supp_supports (x : α) : Supports (Perm 𝔸) (supp 𝔸 x : Set 𝔸) x :=
  (isLeast_supp 𝔸 x).1

end

theorem supp_subset {s : Finset 𝔸} {x : α} (h : Supports (Perm 𝔸) (s : Set 𝔸) x) :
    supp 𝔸 x ⊆ s :=
  (isLeast_supp 𝔸 x).2 h

theorem mem_supp_iff {a : 𝔸} {x : α} :
    a ∈ supp 𝔸 x ↔ ∀ s : Finset 𝔸, Supports (Perm 𝔸) (s : Set 𝔸) x → a ∈ s :=
  ⟨fun ha _ hs => supp_subset hs ha, fun h => h _ (supp_supports 𝔸 x)⟩

variable [DecidableEq 𝔸] in
open scoped Pointwise in
theorem supp_smul (π : Perm 𝔸) (x : α) :
    supp 𝔸 (π • x) = π • supp 𝔸 x := by
  apply Finset.Subset.antisymm
  · apply supp_subset
    rw [Finset.coe_smul_finset]
    exact (supp_supports 𝔸 x).smul' π
  · rw [Finset.smul_finset_subset_iff]
    apply supp_subset
    rw [Finset.coe_smul_finset]
    have h := (supp_supports 𝔸 (π • x)).smul' π⁻¹
    rwa [inv_smul_smul] at h

/-- An atom is fresh for an element of a nominal set when it lies outside its support.
`𝔸` is implicit, determined by the atom, unlike `supp` where nothing determines it. -/
def Fresh (a : 𝔸) (x : α) : Prop :=
  a ∉ supp 𝔸 x

@[inherit_doc] scoped infix:50 " ♯ " => Nominal.Fresh

theorem fresh_iff {a : 𝔸} {x : α} :
    a ♯ x ↔ ∃ s : Finset 𝔸, Supports (Perm 𝔸) (s : Set 𝔸) x ∧ a ∉ s :=
  ⟨fun h => ⟨supp 𝔸 x, supp_supports 𝔸 x, h⟩,
    fun ⟨_, hs, has⟩ h => has (supp_subset hs h)⟩

theorem exists_fresh (x : α) (avoid : Finset 𝔸) : ∃ a, a ♯ x ∧ a ∉ avoid := by
  have ⟨a, ha⟩ := ((supp 𝔸 x).finite_toSet.union avoid.finite_toSet).infinite_compl.nonempty
  rw [Set.mem_compl_iff, Set.mem_union, Finset.mem_coe, Finset.mem_coe] at ha
  exact ⟨a, fun h => ha (Or.inl h), fun h => ha (Or.inr h)⟩

variable [DecidableEq 𝔸] {a b : 𝔸} {x : α}

theorem Fresh.swap_smul (ha : a ♯ x) (hb : b ♯ x) : swap a b • x = x :=
  (supp_supports 𝔸 x).swap_smul ha hb

theorem swap_smul_ne (ha : a ∈ supp 𝔸 x) (hb : b ∉ supp 𝔸 x) : swap a b • x ≠ x := by
  intro heq
  have hba := Finset.smul_mem_smul_finset (a := swap a b) ha
  rw [Perm.smul_def, swap_apply_left, ← supp_smul, heq] at hba
  exact hb hba

theorem mem_supp_iff_infinite_swap : a ∈ supp 𝔸 x ↔ {b | swap a b • x ≠ x}.Infinite := by
  constructor
  · intro ha
    apply Set.Infinite.mono (s := (supp 𝔸 x)ᶜ)
    · exact fun b hb => swap_smul_ne ha fun h => hb (Finset.mem_coe.mpr h)
    · exact (supp 𝔸 x).finite_toSet.infinite_compl
  · intro hinf
    by_contra ha
    refine hinf (Set.Finite.subset (supp 𝔸 x ∪ {a}).finite_toSet fun b hb => ?_)
    by_contra hbmem
    rw [Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.coe_singleton,
      Set.mem_singleton_iff, not_or] at hbmem
    exact hb (Fresh.swap_smul ha hbmem.left)

end Nominal

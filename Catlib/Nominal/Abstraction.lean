/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Catlib.Nominal.Instances

/-!
# Name abstraction

The name abstraction `Nominal.Abstraction 𝔸 α` of a nominal set `α`: the quotient of
`𝔸 × α` identifying `(a, x)` and `(b, y)` whenever `swap a c • x = swap b c • y` for a
fresh name `c`. This is α-equivalence of a single binder, and `Abstraction 𝔸 α` is the
nominal set of α-equivalence classes.

## References

* A. M. Pitts, *Nominal Sets: Names and Symmetry in Computer Science*, Cambridge
  University Press, 2013.
-/

@[expose] public section

open MulAction
open Equiv

namespace Nominal

variable {𝔸 α : Type*} [DecidableEq 𝔸] [Infinite 𝔸]
variable [MulAction (Perm 𝔸) α] [Nominal 𝔸 α]
variable {a b c d : 𝔸} {x y : α}

private theorem swap_rename (hc : c ♯ x) (hd : d ♯ x) (hca : c ≠ a) (hda : d ≠ a) :
    swap a d • x = swap c d • swap a c • x :=
  (supp_supports 𝔸 x).swap_swap_smul hc hd hca hda

private theorem swap_rename' (hc : c ♯ x) (hca : c ≠ a) (hb : b = a ∨ b ♯ x) :
    swap a b • x = swap c b • swap a c • x := by
  by_cases hba : b = a
  · subst hba
    rw [swap_self, ← Perm.one_def, one_smul, ← mul_smul, swap_comm b c, swap_mul_self, one_smul]
  · exact swap_rename hc (hb.resolve_left hba) hca hba

/-- Two pairs are related when swapping their bound names for a common fresh name yields
equal elements. -/
def Abstraction.Rel : 𝔸 × α → 𝔸 × α → Prop
  | (a, x), (b, y) =>
    ∃ c, c ♯ x ∧ c ♯ y ∧ c ≠ a ∧ c ≠ b ∧ swap a c • x = swap b c • y

namespace Abstraction

theorem Rel.swap_smul_eq (h : Rel (a, x) (b, y)) (hdx : d ♯ x) (hdy : d ♯ y)
    (hda : d ≠ a) (hdb : d ≠ b) : swap a d • x = swap b d • y := by
  have ⟨c, hcx, hcy, hca, hcb, hswap⟩ := h
  rw [swap_rename hcx hdx hca hda, hswap, ← swap_rename hcy hdy hcb hdb]

theorem Rel.refl : ∀ p : 𝔸 × α, Rel p p
  | (a, x) =>
    have ⟨c, hc, hca⟩ := exists_fresh x {a}
    have hne : c ≠ a := Finset.notMem_singleton.mp hca
    ⟨c, hc, hc, hne, hne, rfl⟩

theorem Rel.symm : ∀ {p q : 𝔸 × α}, Rel p q → Rel q p
  | (_, _), (_, _), ⟨c, hcx, hcy, hca, hcb, h⟩ => ⟨c, hcy, hcx, hcb, hca, h.symm⟩

theorem Rel.trans : ∀ {p q r : 𝔸 × α}, Rel p q → Rel q r → Rel p r
  | (a, x), (b, y), (e, z), h₁, h₂ => by
    have ⟨c, hc, hcav⟩ := exists_fresh (x, y, z) {a, b, e}
    have ⟨hcx, hcyz⟩ := fresh_prodMk_iff.mp hc
    have ⟨hcy, hcz⟩ := fresh_prodMk_iff.mp hcyz
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcav
    have ⟨hca, hcb, hce⟩ := hcav
    exact ⟨c, hcx, hcz, hca, hce,
      (h₁.swap_smul_eq hcx hcy hca hcb).trans (h₂.swap_smul_eq hcy hcz hcb hce)⟩

instance setoid (𝔸 α : Type*) [DecidableEq 𝔸] [Infinite 𝔸] [MulAction (Perm 𝔸) α]
    [Nominal 𝔸 α] : Setoid (𝔸 × α) :=
  ⟨Rel, Rel.refl, Rel.symm, Rel.trans⟩

end Abstraction

/-- The name abstraction of a nominal set: pairs of a bound name and an element, up to
fresh renaming of the bound name. -/
def Abstraction (𝔸 α : Type*) [DecidableEq 𝔸] [Infinite 𝔸] [MulAction (Perm 𝔸) α]
    [Nominal 𝔸 α] : Type _ :=
  Quotient (Abstraction.setoid 𝔸 α)

namespace Abstraction

/-- Abstract the name `a` in the element `x`. -/
def mk (a : 𝔸) (x : α) : Abstraction 𝔸 α :=
  ⟦(a, x)⟧

theorem mk_eq_mk : mk a x = mk b y ↔ Rel (a, x) (b, y) :=
  Quotient.eq

instance : MulAction (Perm 𝔸) (Abstraction 𝔸 α) where
  smul π := Quotient.map (fun p => (π p.1, π • p.2)) (by
    intro (a, x) (b, y) ⟨c, hcx, hcy, hca, hcb, hswap⟩
    refine ⟨π c, ?_, ?_, π.injective.ne hca, π.injective.ne hcb, ?_⟩
    · rw [Fresh, supp_smul]
      exact fun h => hcx (Finset.smul_mem_smul_finset_iff π |>.mp h)
    · rw [Fresh, supp_smul]
      exact fun h => hcy (Finset.smul_mem_smul_finset_iff π |>.mp h)
    · rw [swap_smul_smul π a c x, hswap, ← swap_smul_smul π b c y])
  one_smul q := by
    cases q using Quotient.ind with | _ p =>
    exact congrArg (⟦·⟧) (Prod.ext rfl (one_smul _ p.2))
  mul_smul π σ q := by
    cases q using Quotient.ind with | _ p =>
    exact congrArg (⟦·⟧) (Prod.ext (Perm.mul_apply π σ p.1) (mul_smul π σ p.2))

@[simp]
theorem smul_mk (π : Perm 𝔸) (a : 𝔸) (x : α) : π • mk a x = mk (π a) (π • x) :=
  rfl

theorem mk_right_inj : mk a x = mk a y ↔ x = y := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  have ⟨d, _, _, _, _, hs⟩ := mk_eq_mk.mp h
  exact MulAction.injective (swap a d) hs

/-- Alpha renaming: abstracting a fresh name in the renamed element gives the same
abstraction. -/
theorem mk_swap (hc : c ♯ x) (hca : c ≠ a) : mk c (swap a c • x) = mk a x := by
  rw [mk_eq_mk]
  have ⟨d, hd, hdav⟩ := exists_fresh (x, swap a c • x) {a, c}
  have ⟨hdx, hdcx⟩ := fresh_prodMk_iff.mp hd
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hdav
  have ⟨hda, hdc⟩ := hdav
  exact ⟨d, hdcx, hdx, hdc, hda, (swap_rename hc hdx hca hda).symm⟩

instance : Nominal 𝔸 (Abstraction 𝔸 α) where
  finset_support q := by
    cases q using Quotient.ind with | _ p =>
    refine ⟨supp 𝔸 p.2 ∪ {p.1}, fun π hπ => ?_⟩
    have hfix : π p.1 = p.1 := hπ (by
      rw [Finset.coe_union]
      exact Set.mem_union_right _ (Finset.mem_coe.mpr (Finset.mem_singleton_self _)))
    have hx : π • p.2 = p.2 := by
      apply (supp_supports 𝔸 p.2).mono (t := ↑(supp 𝔸 p.2 ∪ {p.1})) ?_ π hπ
      rw [Finset.coe_union]
      exact Set.subset_union_left
    exact congrArg (⟦·⟧) (Prod.ext hfix hx)

theorem supp_mk (a : 𝔸) (x : α) : supp 𝔸 (mk a x) = supp 𝔸 x \ {a} := by
  apply Finset.Subset.antisymm
  · apply supp_subset
    intro π hπ
    have hπs : ∀ s ∈ supp 𝔸 x \ {a}, π s = s := fun s hs => hπ (Finset.mem_coe.mpr hs)
    have hπa : π a ∉ supp 𝔸 x \ {a} := fun h => by
      rw [π.injective (hπs (π a) h)] at h
      exact (Finset.mem_sdiff.mp h).2 (Finset.mem_singleton_self a)
    have hagree : ∀ s ∈ (↑(supp 𝔸 x) : Set 𝔸), π • s = swap a (π a) • s := by
      intro s hs
      rw [Perm.smul_def, Perm.smul_def]
      by_cases hsa : s = a
      · subst hsa
        rw [swap_apply_left]
      · have hss : s ∈ supp 𝔸 x \ {a} :=
          Finset.mem_sdiff.mpr ⟨Finset.mem_coe.mp hs, Finset.notMem_singleton.mpr hsa⟩
        have hsπa : s ≠ π a := fun h => hπa (h ▸ hss)
        rw [hπs s hss, swap_apply_of_ne_of_ne hsa hsπa]
    rw [smul_mk, (supp_supports 𝔸 x).smul_eq_smul hagree]
    by_cases hpa : π a = a
    · rw [hpa, swap_self, ← Perm.one_def, one_smul]
    · exact mk_swap (fun hmem =>
        hπa (Finset.mem_sdiff.mpr ⟨hmem, Finset.notMem_singleton.mpr hpa⟩)) hpa
  · intro b hb
    have ⟨hbs, hba'⟩ := Finset.mem_sdiff.mp hb
    have hba : b ≠ a := Finset.notMem_singleton.mp hba'
    by_contra hfresh
    have ⟨c, hc, hcav⟩ := exists_fresh (x, mk a x) {a, b}
    have ⟨hcx, hcmk⟩ := fresh_prodMk_iff.mp hc
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcav
    have ⟨hca, hcb⟩ := hcav
    have hswap : swap b c • mk a x = mk a x := Fresh.swap_smul hfresh hcmk
    rw [smul_mk, swap_apply_of_ne_of_ne (Ne.symm hba) (Ne.symm hca)] at hswap
    exact swap_smul_ne hbs hcx (mk_right_inj.mp hswap)

theorem fresh_mk_left (a : 𝔸) (x : α) : a ♯ mk a x := by
  rw [Fresh, supp_mk]
  exact fun h => (Finset.mem_sdiff.mp h).2 (Finset.mem_singleton_self a)

private theorem fresh_mk_cases {b : 𝔸} (h : b ♯ mk a x) : b = a ∨ b ♯ x := by
  rw [Fresh, supp_mk] at h
  by_cases hba : b = a
  · exact Or.inl hba
  · exact Or.inr fun hmem =>
      h (Finset.mem_sdiff.mpr ⟨hmem, Finset.notMem_singleton.mpr hba⟩)

theorem Rel.concretion_congr {b : 𝔸} :
    ∀ {p q : 𝔸 × α}, Abstraction.Rel p q → b ♯ mk p.1 p.2 →
      swap p.1 b • p.2 = swap q.1 b • q.2
  | (a, x), (a', x'), h, hb => by
    have hb' : b ♯ mk a' x' := mk_eq_mk.mpr h ▸ hb
    have ⟨c, hc, hcav⟩ := exists_fresh (x, x') {a, a'}
    have ⟨hcx, hcx'⟩ := fresh_prodMk_iff.mp hc
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcav
    have ⟨hca, hca'⟩ := hcav
    rw [swap_rename' hcx hca (fresh_mk_cases hb), swap_rename' hcx' hca' (fresh_mk_cases hb'),
      h.swap_smul_eq hcx hcx' hca hca']

/-- Concretion: instantiate the bound name of an abstraction at a fresh atom. -/
def concretion (y : Abstraction 𝔸 α) (b : 𝔸) : b ♯ y → α :=
  Quotient.hrecOn y (fun p _ => swap p.1 b • p.2) fun _ _ hpq =>
    Function.hfunext (congrArg (Fresh b) (Quotient.sound hpq)) fun h _ _ =>
      heq_of_eq (Rel.concretion_congr hpq h)

@[simp]
theorem concretion_mk {b : 𝔸} (h : b ♯ mk a x) :
    concretion (mk a x) b h = swap a b • x :=
  rfl

theorem concretion_mk_left (h : a ♯ mk a x) : concretion (mk a x) a h = x := by
  rw [concretion_mk, swap_self, ← Perm.one_def, one_smul]

theorem exists_mk_fresh {β : Type*} [MulAction (Perm 𝔸) β] [Nominal 𝔸 β]
    (y : Abstraction 𝔸 α) (c : β) : ∃ a x, a ♯ c ∧ y = mk a x := by
  cases y using Quotient.ind with | _ p =>
  have ⟨a₀, x₀⟩ := p
  have ⟨b, hb, hbav⟩ := exists_fresh (x₀, c) {a₀}
  have ⟨hbx₀, hbc⟩ := fresh_prodMk_iff.mp hb
  refine ⟨b, swap a₀ b • x₀, hbc, ?_⟩
  change mk a₀ x₀ = _
  exact (mk_swap hbx₀ (Finset.notMem_singleton.mp hbav)).symm

/-- Strong induction for abstractions: the bound name may be assumed fresh for any
finitely supported context `c`, i.e. the Barendregt variable convention. -/
@[elab_as_elim]
theorem inductionOn_fresh {β : Type*} [MulAction (Perm 𝔸) β] [Nominal 𝔸 β]
    {motive : Abstraction 𝔸 α → Prop} (y : Abstraction 𝔸 α) (c : β)
    (mk_fresh : ∀ a x, a ♯ c → motive (mk a x)) : motive y := by
  have ⟨a, x, hfresh, hy⟩ := exists_mk_fresh y c
  exact hy ▸ mk_fresh a x hfresh

theorem mk_concretion (y : Abstraction 𝔸 α) (b : 𝔸) (h : b ♯ y) :
    mk b (concretion y b h) = y := by
  cases y using Quotient.ind with | _ p =>
  have ⟨a, x⟩ := p
  by_cases hba : b = a
  · subst hba
    exact congrArg (mk b) (concretion_mk_left h)
  · have hbfx : b ♯ x := (fresh_mk_cases h).resolve_left hba
    change mk b (concretion (mk a x) b h) = mk a x
    rw [concretion_mk h]
    exact mk_swap hbfx hba

section Lift

variable {β : Type*} [MulAction (Perm 𝔸) β] [Nominal 𝔸 β]

theorem supp_apply_subset (f : 𝔸 → α → β)
    (hf : ∀ (π : Perm 𝔸) (a : 𝔸) (x : α), f (π a) (π • x) = π • f a x) (a : 𝔸) (x : α) :
    supp 𝔸 (f a x) ⊆ {a} ∪ supp 𝔸 x := by
  apply supp_subset
  have hpair : Supports (Perm 𝔸) (↑({a} ∪ supp 𝔸 x) : Set 𝔸) (a, x) := by
    have h := supp_supports 𝔸 (a, x)
    rwa [supp_prodMk, supp_atom] at h
  exact Supports.map hpair (fun p => f p.1 p.2) fun π p => hf π p.1 p.2

theorem Rel.lift_congr (f : 𝔸 → α → β)
    (hf : ∀ (π : Perm 𝔸) (a : 𝔸) (x : α), f (π a) (π • x) = π • f a x)
    (fcb : ∀ (a : 𝔸) (x : α), a ♯ f a x) :
    ∀ {p q : 𝔸 × α}, Abstraction.Rel p q → f p.1 p.2 = f q.1 q.2
  | (a, x), (a', x'), h => by
    have ⟨c, hc, hcav⟩ := exists_fresh (x, x') {a, a'}
    have ⟨hcx, hcx'⟩ := fresh_prodMk_iff.mp hc
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcav
    have ⟨hca, hca'⟩ := hcav
    have hkey : swap a c • x = swap a' c • x' := h.swap_smul_eq hcx hcx' hca hca'
    have hcf : ∀ (b : 𝔸) (y : α), c ∉ supp 𝔸 y → c ≠ b → c ♯ f b y := by
      intro b y hcy hcb hmem
      rcases Finset.mem_union.mp (supp_apply_subset f hf b y hmem) with h1 | h2
      · exact hcb (Finset.mem_singleton.mp h1)
      · exact hcy h2
    calc f a x
      _ = swap a c • f a x := (Fresh.swap_smul (fcb a x) (hcf a x hcx hca)).symm
      _ = f c (swap a c • x) := by rw [← hf, swap_apply_left]
      _ = f c (swap a' c • x') := by rw [hkey]
      _ = swap a' c • f a' x' := by rw [← hf, swap_apply_left]
      _ = f a' x' := Fresh.swap_smul (fcb a' x') (hcf a' x' hcx' hca')

/-- Freshness recursion: an equivariant function satisfying the freshness condition for
binders descends to abstractions. -/
def lift (f : 𝔸 → α → β)
    (hf : ∀ (π : Perm 𝔸) (a : 𝔸) (x : α), f (π a) (π • x) = π • f a x)
    (fcb : ∀ (a : 𝔸) (x : α), a ♯ f a x) : Abstraction 𝔸 α → β :=
  Quotient.lift (fun p => f p.1 p.2) fun _ _ h => Rel.lift_congr f hf fcb h

@[simp]
theorem lift_mk (f : 𝔸 → α → β)
    (hf : ∀ (π : Perm 𝔸) (a : 𝔸) (x : α), f (π a) (π • x) = π • f a x)
    (fcb : ∀ (a : 𝔸) (x : α), a ♯ f a x) (a : 𝔸) (x : α) :
    lift f hf fcb (mk a x) = f a x :=
  rfl

end Lift

end Abstraction

end Nominal

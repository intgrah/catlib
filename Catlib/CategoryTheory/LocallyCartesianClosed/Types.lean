/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Jeremy Chen
-/
module

public import Catlib.CategoryTheory.LocallyCartesianClosed.Basic
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# The category of types is locally cartesian closed

Given a map `f : E ⟶ B` between types, the pullback functor `Over B ⥤ Over E` is realized on
the explicit pullback types `Limits.Types.PullbackObj`, and its right adjoint sends `p : T ⟶ E`
to the sigma type `pushforwardObj f T` of fiberwise sections of `p`. Both functors and both
adjunctions are computable, giving `ChosenPullbacks (Type u)` and
`ChosenPushforwards (Type u)`, and therefore `LocallyCartesianClosed (Type u)`.
-/

@[expose] public section

universe u

namespace TypeCat

open CategoryTheory Limits
open ConcreteCategory (congr_hom)

variable {E B : Type u} (f : E ⟶ B)

/-- The object part of the pushforward functor along `f : E ⟶ B` in types: the sigma type
which sends `b : B` to the subtype of sections of `T.hom` over the fiber `f ⁻¹' {b}`. -/
abbrev pushforwardObj (T : Over E) : Type u :=
  Σ (b : B), { g : f ⁻¹' {b} → T.left // ∀ e, T.hom (g e) = e.1 }

/-- Extensionality lemma for the fiberwise section types `pushforwardObj f T`. -/
@[ext (iff := false)]
lemma pushforwardObj_ext {T : Over E} {t t' : pushforwardObj f T}
    (h₁ : t.1 = t'.1) (h₂ : ∀ (e : E) (he : f e = t.1),
      t.2.1 ⟨e, he⟩ = t'.2.1 ⟨e, by simp [h₁, he]⟩) : t = t' := by
  have ⟨t, g, _⟩ := t
  have ⟨t', g', _⟩ := t'
  obtain rfl : t = t' := h₁
  obtain rfl : g = g' := by ext; apply h₂
  rfl

/-- The category of types has chosen pullbacks, realized on the explicit pullback types
`Limits.Types.PullbackObj`. -/
instance chosenPullbacks : ChosenPullbacks (Type u) := fun {B E} f =>
  { pullback :=
      { obj S := Over.mk (Y := Types.PullbackObj S.hom f) (↾fun x ↦ x.1.2)
        map {S S'} φ := Over.homMk (↾fun x ↦ ⟨⟨φ.left x.1.1, x.1.2⟩, by
          have h := congr_hom (Over.w φ) x.1.1
          simp only [comp_apply] at h
          exact h.trans x.2⟩) }
    mapPullbackAdj := .mkOfHomEquiv
      { homEquiv A S :=
        { toFun u := Over.homMk (↾fun a ↦ ⟨⟨u.left a, A.hom a⟩, by
            have h := congr_hom (Over.w u) a
            simp only [comp_apply, Over.map_obj_hom] at h
            exact h.trans (comp_apply _ _ _)⟩)
          invFun v := Over.homMk (↾fun a ↦ (v.left a).1.1) (by
            ext a
            have h := congr_hom (Over.w v) a
            simp only [comp_apply, Over.mk_hom] at h
            exact (v.left a).2.trans (congrArg f h))
          left_inv _ := rfl
          right_inv v := by
            ext a
            have h := congr_hom (Over.w v) a
            simp only [comp_apply, Over.mk_hom] at h
            exact Subtype.ext (Prod.ext rfl h.symm) } } }

/-- The category of types has chosen pushforwards: the pushforward along `f : E ⟶ B` is given
by the fiberwise section types `pushforwardObj f T`. In particular `Type u` is locally
cartesian closed. -/
instance chosenPushforwards : ChosenPushforwards (Type u) where
  exponentiable {E B} f :=
    { pushforward :=
        { obj T := Over.mk (Y := pushforwardObj f T) (↾Sigma.fst)
          map {T T'} φ := Over.homMk (↾fun t ↦ ⟨t.1, fun e ↦ φ.left (t.2.1 e), fun e ↦ by
            have h := congr_hom (Over.w φ) (t.2.1 e)
            simp only [comp_apply] at h
            exact h.trans (t.2.2 e)⟩) }
      pullbackPushforwardAdj := .mkOfHomEquiv
        { homEquiv S T :=
          { toFun φ := Over.homMk (↾fun s ↦ ⟨S.hom s,
              fun x ↦ φ.left ((⟨⟨s, x.1⟩, x.2.symm⟩ : Types.PullbackObj S.hom f)),
              fun x ↦ by
                have h := congr_hom (Over.w φ)
                  ((⟨⟨s, x.1⟩, x.2.symm⟩ : Types.PullbackObj S.hom f))
                simp only [comp_apply] at h
                exact h.trans rfl⟩)
            invFun ψ := Over.homMk
              (↾fun x ↦ (((ψ.left (x : Types.PullbackObj S.hom f).1.1) :
                  pushforwardObj f T).2.1
                ⟨(x : Types.PullbackObj S.hom f).1.2, by
                  have h := congr_hom (Over.w ψ) (x : Types.PullbackObj S.hom f).1.1
                  simp only [comp_apply, Over.mk_hom] at h
                  exact (h.trans (x : Types.PullbackObj S.hom f).2).symm⟩))
              (by
                ext x
                exact ((ψ.left (x : Types.PullbackObj S.hom f).1.1) :
                  pushforwardObj f T).2.2 _)
            left_inv φ := by
              ext x
              exact congrArg φ.left (Subtype.ext rfl)
            right_inv ψ := by
              ext s
              apply pushforwardObj_ext
              · intro e he
                rfl
              · have h := congr_hom (Over.w ψ) s
                simp only [comp_apply, Over.mk_hom] at h
                exact h.symm } } }

end TypeCat

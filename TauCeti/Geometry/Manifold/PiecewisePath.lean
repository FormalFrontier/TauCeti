/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Basic

/-!
# Piecewise smooth paths in a manifold

This file defines piecewise `C^n` regularity for a path on a compact real interval using a finite
strict partition. The predicate retains the partition only existentially. Thus two proofs using
different partitions are proofs of the same property of the underlying path, rather than distinct
bundled paths carrying irrelevant partition data.

## Main definitions

* `TauCeti.Manifold.IsPiecewiseContMDiffOn`: a path is `C^n` on the pieces of some finite strict
  partition of `[a, b]`.

## Main results

* `TauCeti.Manifold.IsPiecewiseContMDiffOn.continuousOn`: piecewise `C^n` regularity implies
  continuity on the whole interval.

This is the metric-independent finite-partition regularity API used in Layer 0 of the Hopf--Rinow
roadmap.

## References

* M. P. do Carmo, *Riemannian Geometry*, Chapter 1, Definition 2.9 and Chapter 7, Section 2.
-/

public section

open Set
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Manifold

universe u

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ∞ω} {γ : ℝ → M} {a b : ℝ}

/-- A path is piecewise `C^n` on `[a, b]` if there is a nonempty finite strict partition from
`a` to `b` such that the path is `C^n` on every closed piece. The partition has `k + 1` pieces
and `k + 2` vertices, so the definition includes the one-piece case but excludes a vacuous
zero-piece witness.

The partition is existential data because it witnesses a property of `γ`; it is not part of the
identity of a path. In particular, refining a partition does not create a different object. -/
@[expose] def IsPiecewiseContMDiffOn (I : ModelWithCorners ℝ E H) (n : ℕ∞ω)
    (γ : ℝ → M) (a b : ℝ) : Prop :=
  ∃ (k : ℕ) (τ : Fin (k + 2) → ℝ),
    τ 0 = a ∧
      τ (Fin.last (k + 1)) = b ∧
      (∀ i : Fin (k + 1), τ i.castSucc < τ i.succ) ∧
      ∀ i : Fin (k + 1),
        ContMDiffOn (modelWithCornersSelf ℝ ℝ) I n γ (Icc (τ i.castSucc) (τ i.succ))

/-- The endpoints of a piecewise smooth path are strictly ordered. -/
theorem IsPiecewiseContMDiffOn.lt (h : IsPiecewiseContMDiffOn I n γ a b) : a < b := by
  obtain ⟨k, τ, rfl, rfl, hτ, -⟩ := h
  exact (Fin.strictMono_iff_lt_succ.mpr hτ) Fin.last_pos'

/-- A `C^n` path on a nondegenerate interval is piecewise `C^n`, witnessed by the partition
consisting only of its two endpoints. -/
theorem IsPiecewiseContMDiffOn.of_contMDiffOn (hab : a < b)
    (hγ : ContMDiffOn (modelWithCornersSelf ℝ ℝ) I n γ (Icc a b)) :
    IsPiecewiseContMDiffOn I n γ a b := by
  let τ : Fin 2 → ℝ := ![a, b]
  refine ⟨0, τ, ?_, ?_, ?_, ?_⟩
  · simp [τ]
  · simp [τ]
  · intro i
    fin_cases i
    simpa [τ] using hab
  · intro i
    fin_cases i
    simpa [τ] using hγ

/-- Restricting the requested differentiability order preserves piecewise smoothness. -/
theorem IsPiecewiseContMDiffOn.of_le {m : ℕ∞ω} (h : IsPiecewiseContMDiffOn I n γ a b)
    (hmn : m ≤ n) : IsPiecewiseContMDiffOn I m γ a b := by
  obtain ⟨k, τ, hτa, hτb, hτ, hγ⟩ := h
  exact ⟨k, τ, hτa, hτb, hτ, fun i ↦ (hγ i).of_le hmn⟩

/-- Continuity glues across a finite ordered partition. This is the induction underlying
`IsPiecewiseContMDiffOn.continuousOn`. -/
private theorem continuousOn_Icc_of_partition
    {r : ℕ} (τ : Fin (r + 1) → ℝ)
    (hτ : ∀ i : Fin r, τ i.castSucc ≤ τ i.succ)
    (hγ : ∀ i : Fin r, ContinuousOn γ (Icc (τ i.castSucc) (τ i.succ))) :
    ContinuousOn γ (Icc (τ 0) (τ (Fin.last r))) := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hτmono : Monotone τ := Fin.monotone_iff_le_succ.mpr hτ
      have hfirst : τ 0 ≤ τ (Fin.last r).castSucc := hτmono (Fin.zero_le _)
      rw [← Fin.succ_last r]
      rw [← Icc_union_Icc_eq_Icc
        hfirst (hτ (Fin.last r))]
      rw [continuousOn_union_iff_of_isClosed isClosed_Icc isClosed_Icc]
      refine ⟨ih (fun i ↦ τ i.castSucc) (fun i ↦ ?_) (fun i ↦ ?_), ?_⟩
      · simpa only [Fin.succ_castSucc] using hτ i.castSucc
      · simpa only [Fin.succ_castSucc] using hγ i.castSucc
      · simpa using hγ (Fin.last r)

/-- Piecewise `C^n` regularity implies continuity on the whole interval. -/
theorem IsPiecewiseContMDiffOn.continuousOn (h : IsPiecewiseContMDiffOn I n γ a b) :
    ContinuousOn γ (Icc a b) := by
  obtain ⟨k, τ, hτa, hτb, hτ, hγ⟩ := h
  rw [← hτa, ← hτb]
  exact continuousOn_Icc_of_partition τ (fun i ↦ (hτ i).le)
    (fun i ↦ (hγ i).continuousOn)

end TauCeti.Manifold

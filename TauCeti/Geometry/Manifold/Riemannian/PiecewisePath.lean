/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Riemannian.PathELength
public import TauCeti.Geometry.Manifold.PiecewisePath

/-!
# Piecewise smooth Riemannian paths

This file extends the metric-independent piecewise smooth path API with Riemannian length results.
It proves that the sum of `Manifold.pathELength` over any ordered partition is the length on the
whole interval. Consequently the sum used to compute the length of a piecewise-`C¹` path is
independent of its witnessing partition and, more generally, of every refinement.

## Main results

* `TauCeti.Manifold.sum_pathELength_eq`: summing `Manifold.pathELength` over an ordered partition
  gives the length on the whole interval.
* `TauCeti.Manifold.sum_pathELength_eq_of_endpoints_eq`: two ordered partitions with the same
  endpoints compute the same length.
* `TauCeti.Manifold.IsPiecewiseContMDiffOn.exists_partition_sum_pathELength_eq`: a piecewise
  smooth path has a witnessing partition whose piece lengths sum to its `pathELength`.

This is the finite-partition part of Layer 0 of the Hopf--Rinow roadmap. It uses Mathlib's
`Manifold.pathELength_add`; no separate notion of Riemannian length is introduced.

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

variable [∀ x : M, ENorm (TangentSpace I x)]

/-- **Path length is additive over every finite ordered partition.** The sum of the lengths of
the restrictions to consecutive pieces is the length over the interval between the first and last
partition points. No regularity hypothesis is needed: this is finite iteration of Mathlib's
`Manifold.pathELength_add`. -/
theorem sum_pathELength_eq {r : ℕ} (τ : Fin (r + 1) → ℝ)
    (hτ : ∀ i : Fin r, τ i.castSucc ≤ τ i.succ) :
    ∑ i : Fin r, Manifold.pathELength I γ (τ i.castSucc) (τ i.succ) =
      Manifold.pathELength I γ (τ 0) (τ (Fin.last r)) := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Fin.sum_univ_castSucc]
      have hfirst :
        (∑ i : Fin r,
          Manifold.pathELength I γ (τ i.castSucc.castSucc) (τ i.castSucc.succ)) =
            Manifold.pathELength I γ (τ 0) (τ (Fin.last r).castSucc) := by
        simpa only [Fin.succ_castSucc, Fin.castSucc_zero] using
          ih (fun i ↦ τ i.castSucc) (fun i ↦ by
            simpa only [Fin.succ_castSucc] using hτ i.castSucc)
      rw [hfirst]
      have hτmono : Monotone τ := Fin.monotone_iff_le_succ.mpr hτ
      have hzero : τ 0 ≤ τ (Fin.last r).castSucc := hτmono (Fin.zero_le _)
      simpa only [Fin.succ_last] using
        Manifold.pathELength_add (I := I) (γ := γ)
          hzero (hτ (Fin.last r))

/-- Ordered finite partitions with the same first and last points give the same sum of piece
lengths. In particular, inserting any finite collection of refinement points leaves the computed
length unchanged. -/
theorem sum_pathELength_eq_of_endpoints_eq
    {r s : ℕ} {τ : Fin (r + 1) → ℝ} {σ : Fin (s + 1) → ℝ}
    (hτ : ∀ i : Fin r, τ i.castSucc ≤ τ i.succ)
    (hσ : ∀ i : Fin s, σ i.castSucc ≤ σ i.succ)
    (h₀ : τ 0 = σ 0) (h₁ : τ (Fin.last r) = σ (Fin.last s)) :
    ∑ i : Fin r, Manifold.pathELength I γ (τ i.castSucc) (τ i.succ) =
      ∑ i : Fin s, Manifold.pathELength I γ (σ i.castSucc) (σ i.succ) := by
  rw [sum_pathELength_eq τ hτ, sum_pathELength_eq σ hσ, h₀, h₁]

/-- A piecewise smooth path admits a strict partition on which it is smooth and whose sum of
piece lengths is exactly its `Manifold.pathELength` on the full interval. This is the form used to
iterate corner smoothing over a partition. -/
theorem IsPiecewiseContMDiffOn.exists_partition_sum_pathELength_eq
    (h : IsPiecewiseContMDiffOn I n γ a b) :
    ∃ (k : ℕ) (τ : Fin (k + 2) → ℝ),
      τ 0 = a ∧
        τ (Fin.last (k + 1)) = b ∧
        (∀ i : Fin (k + 1), τ i.castSucc < τ i.succ) ∧
        (∀ i : Fin (k + 1),
          ContMDiffOn (modelWithCornersSelf ℝ ℝ) I n γ
            (Icc (τ i.castSucc) (τ i.succ))) ∧
        ∑ i : Fin (k + 1), Manifold.pathELength I γ (τ i.castSucc) (τ i.succ) =
          Manifold.pathELength I γ a b := by
  obtain ⟨k, τ, hτa, hτb, hτ, hγ⟩ := h
  refine ⟨k, τ, hτa, hτb, hτ, hγ, ?_⟩
  rw [sum_pathELength_eq τ (fun i ↦ (hτ i).le), hτa, hτb]

end TauCeti.Manifold

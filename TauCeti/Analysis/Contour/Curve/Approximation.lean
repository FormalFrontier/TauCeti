/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Smooth endpoint-preserving approximation of continuous complex curves

Every continuous map from the unit interval to `ℂ` is uniformly approximated, to any positive
tolerance, by a smooth curve on `ℝ` taking the same values at `0` and `1`. The approximants are
Mathlib's Bernstein approximations, read as polynomial functions on all of `ℝ`, which is what makes
their smoothness and their endpoint values immediate.

## Main results

* `TauCeti.Contour.exists_contDiff_eq_endpoints_dist_lt` — the endpoint-preserving smooth
  approximation.

This is the regularization step that lets the merely continuous intermediate paths of a path
homotopy be compared with the piecewise-`C¹` winding number.

## Provenance

The construction and its uniform convergence are Mathlib's `bernsteinApproximation` and
`bernsteinApproximation_uniform`; the polynomials themselves are Mathlib's `bernsteinPolynomial`.
No formal source is vendored.
-/

public section

noncomputable section

open scoped unitInterval

namespace TauCeti.Contour

/-- Mathlib's `n`-th Bernstein approximation of `f`, read as a polynomial function on all of `ℝ`.
Keeping the polynomial off the unit interval makes its smoothness immediate, while
`bernsteinCurve_apply` connects it to Mathlib's uniform approximation theorem. -/
private def bernsteinCurve (n : ℕ) (f : C(I, ℂ)) (t : ℝ) : ℂ :=
  ∑ k : Fin (n + 1), Polynomial.aeval t (bernsteinPolynomial ℝ n k) • f (bernstein.z k)

private theorem bernsteinCurve_apply (n : ℕ) (f : C(I, ℂ)) (t : I) :
    bernsteinCurve n f t = bernsteinApproximation n f t := by
  simp [bernsteinCurve, bernsteinApproximation.apply, bernstein, Polynomial.coe_aeval_eq_eval]

private theorem contDiff_bernsteinCurve (n : ℕ) (f : C(I, ℂ)) :
    ContDiff ℝ ⊤ (bernsteinCurve n f) :=
  ContDiff.sum fun _ _ => (Polynomial.contDiff_aeval _ _).smul_const _

/-- **Endpoint-preserving smooth approximation of a continuous complex path.** Every continuous map
from the unit interval to `ℂ` is uniformly approximated, to any positive tolerance, by a smooth
curve on `ℝ` with the same values at `0` and `1`.

The approximants are Mathlib's Bernstein approximations, read as polynomial functions on `ℝ`; a
consumer needing only piecewise-`C¹` regularity gets it from `IsPiecewiseC1On.of_contDiffOn`. -/
theorem exists_contDiff_eq_endpoints_dist_lt (f : C(I, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ γ : ℝ → ℂ, ContDiff ℝ ⊤ γ ∧ γ 0 = f 0 ∧ γ 1 = f 1 ∧ ∀ t : I, dist (γ t) (f t) < ε := by
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (bernsteinApproximation_uniform f) ε hε
  let n := max N 1
  have hnN : N ≤ n := Nat.le_max_left _ _
  have hn : n ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_right _ _))
  refine ⟨bernsteinCurve n f, contDiff_bernsteinCurve n f, ?_, ?_, ?_⟩
  · exact (bernsteinCurve_apply n f 0).trans (bernsteinApproximation.apply_zero n f)
  · exact (bernsteinCurve_apply n f 1).trans (bernsteinApproximation.apply_one hn f)
  · intro t
    rw [bernsteinCurve_apply]
    exact (ContinuousMap.dist_apply_le_dist t).trans_lt (hN n hnN)

end TauCeti.Contour

end

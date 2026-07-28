module

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
public import Mathlib.RingTheory.Polynomial.Hermite.Basic
public import Mathlib.Analysis.RCLike.Basic
public import TauCeti.Probability.Distributions.Gaussian.PolynomialMemLp

/-!
# `L²` membership of the Hermite polynomials against a Gaussian measure

This file specializes the generic Gaussian/polynomial `L²` membership of
`TauCeti.Probability.Distributions.Gaussian.PolynomialMemLp` to the probabilists' Hermite
polynomials `Polynomial.hermite n`.  The Hermite statement `memLp_hermite_gaussianReal` is target
**A3′** of the `OrthogonalL2Bases` roadmap: the variance-general `L²` membership of the normalized
Hermite polynomials `Hₙ / √(n!)` under `gaussianReal 0 v`, the membership the Gaussian Hermite
Hilbert-basis construction consumes for its `MemLp` obligations.

The scalar-generic cast to `[RCLike 𝕜]` (needed because the roadmap's bases are stated over
`Lp 𝕜 2 μ` uniformly for `𝕜 = ℝ` and `𝕜 = ℂ`) reuses Mathlib's `MemLp.ofReal`, rewriting the
`algebraMap ℝ 𝕜` cast to `RCLike.ofReal`.

The `Polynomial` evaluation API and `MemLp.ofReal` are consumed, not re-derived.
-/

public section

namespace TauCeti

open MeasureTheory ProbabilityTheory Polynomial

open scoped NNReal ENNReal

/-! ## Scalar-generic cast and the Hermite instance -/

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **Target A3′ (variance-general `L²` membership).** The normalized probabilists' Hermite
polynomial `Hₙ / √(n!)`, cast into `𝕜`, is square-integrable against every centred real Gaussian
`gaussianReal 0 v`.  Immediate from `memLp_two_eval_gaussianReal` (Hermite is a polynomial) and the
scalar cast `MemLp.ofReal`. -/
theorem memLp_hermite_gaussianReal (n : ℕ) (v : ℝ≥0) :
    MemLp (fun x => (algebraMap ℝ 𝕜) (aeval x (hermite n) / Real.sqrt (n.factorial))) 2
      (gaussianReal 0 v) := by
  have key : ∀ x : ℝ, aeval x (hermite n) / Real.sqrt (n.factorial)
      = ((hermite n).map (Int.castRingHom ℝ)).eval x * (Real.sqrt (n.factorial))⁻¹ := by
    intro x
    rw [div_eq_mul_inv, Polynomial.aeval_def, algebraMap_int_eq, Polynomial.eval_map]
  simp only [key]
  simpa only [← RCLike.algebraMap_eq_ofReal] using
    ((memLp_two_eval_gaussianReal 0 v _).mul_const _).ofReal (K := 𝕜)

end TauCeti

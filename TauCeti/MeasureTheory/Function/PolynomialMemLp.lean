/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Topology.Algebra.Polynomial

/-!
# Integrability and `L²` membership of polynomials against a finite-moment measure

This file proves that a real polynomial, evaluated pointwise, is integrable and square-integrable
against any measure on `ℝ` all of whose polynomial moments are finite:

* `integrable_eval_of_forall_integrable_pow` — a polynomial is integrable, being a finite linear
  combination of monomials;
* `memLp_two_eval_of_forall_integrable_pow` — a polynomial is in `L²`, since the square of a
  polynomial is again a polynomial (hence integrable), and `memLp_two_iff_integrable_sq`.

Both consume only the moment hypothesis `∀ k, Integrable (x ↦ xᵏ) μ`, with no dependence on the
particular measure, so they apply verbatim to the Gaussian measure (all moments finite by Fernique)
and to the compactly supported Chebyshev measure alike.

Building on the `L²` membership, `polynomialEvalLp` bundles polynomial evaluation, cast into any
`[RCLike 𝕜]` scalar field, as an `ℝ`-linear map `ℝ[X] →ₗ[ℝ] Lp 𝕜 2 μ`.  Being measure- and
scalar-generic, it is the shared construction underlying the Gaussian and Chebyshev orthogonal-basis
targets.
-/

public section

namespace TauCeti

open MeasureTheory Polynomial

variable {μ : Measure ℝ}

/-- A real polynomial is integrable against any measure all of whose polynomial moments are finite.
The polynomial is a finite linear combination of the monomials `x ↦ xᵏ`, each integrable by
hypothesis. -/
theorem integrable_eval_of_forall_integrable_pow
    (hmom : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) μ) (q : ℝ[X]) :
    Integrable (fun x : ℝ => q.eval x) μ := by
  simp_rw [Polynomial.eval_eq_sum_range]
  exact integrable_finsetSum _ fun i _ => (hmom i).const_mul _

/-- A real polynomial is in `L²` against any measure all of whose polynomial moments are finite.
The square of a polynomial is again a polynomial, hence integrable by
`integrable_eval_of_forall_integrable_pow`, and `L²` membership is integrability of the square. -/
theorem memLp_two_eval_of_forall_integrable_pow
    (hmom : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) μ) (q : ℝ[X]) :
    MemLp (fun x : ℝ => q.eval x) 2 μ := by
  rw [memLp_two_iff_integrable_sq (Polynomial.continuous q).aestronglyMeasurable]
  have hsq : (fun x : ℝ => q.eval x ^ 2) = fun x : ℝ => (q ^ 2).eval x := by
    ext x; rw [Polynomial.eval_pow]
  rw [hsq]
  exact integrable_eval_of_forall_integrable_pow hmom (q ^ 2)

/-- A real polynomial evaluation, cast into any `RCLike` scalar field, lies in `L²` against any
measure all of whose polynomial moments are finite. -/
theorem memLp_two_algebraMap_eval_of_forall_integrable_pow {𝕜 : Type*} [RCLike 𝕜]
    (hmom : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) μ) (q : ℝ[X]) :
    MemLp (fun x : ℝ => (algebraMap ℝ 𝕜) (q.eval x)) 2 μ := by
  simpa only [RCLike.algebraMap_eq_ofReal] using
    (memLp_two_eval_of_forall_integrable_pow hmom q).ofReal (K := 𝕜)

/-- Polynomial evaluation, cast into any `RCLike` scalar field, bundled as an `ℝ`-linear map into
`L²` against any measure all of whose polynomial moments are finite. -/
noncomputable def polynomialEvalLp (𝕜 : Type*) [RCLike 𝕜]
    (hmom : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) μ) :
    ℝ[X] →ₗ[ℝ] Lp 𝕜 2 μ where
  toFun q := (memLp_two_algebraMap_eval_of_forall_integrable_pow (𝕜 := 𝕜) hmom q).toLp _
  map_add' q r := by
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall fun x => by simp
  map_smul' a q := by
    rw [← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall fun x => by
      simp [Algebra.smul_def, map_mul]

/-- The `L²` representative of `polynomialEvalLp` is the expected scalar-cast pointwise
evaluation. -/
lemma coeFn_polynomialEvalLp (𝕜 : Type*) [RCLike 𝕜]
    (hmom : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) μ) (q : ℝ[X]) :
    ⇑(polynomialEvalLp 𝕜 hmom q) =ᵐ[μ] fun x : ℝ => (algebraMap ℝ 𝕜) (q.eval x) :=
  MemLp.coeFn_toLp (memLp_two_algebraMap_eval_of_forall_integrable_pow (𝕜 := 𝕜) hmom q)

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
-- Non-public: the Chafaï approximating measures, their tightness, and the Prokhorov extraction are
-- used only inside the proof; the statement mentions none of them.
import TauCeti.Analysis.CompletelyMonotone.Bernstein.Tightness
import TauCeti.MeasureTheory.Measure.Prokhorov

/-!
# Bernstein's theorem: existence of a representing measure

A completely monotone function on `[0, ∞)` is the Laplace transform of a finite positive measure
on `ℝ≥0`.

## Main results

* `TauCeti.exists_isFiniteMeasure_integral_exp_neg_mul_eq_of_isCompletelyMonotone`

## Scope

This is the **existence** half of the Bernstein milestone in
`TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B. Uniqueness of the representing measure
(Laplace-transform injectivity) and the converse direction are not proved here, so the roadmap's
reserved name `bernstein` — stated there as a single `∃!` biconditional — stays free for the
assembly that combines all three.

Finiteness of the representing measure is not an extra hypothesis but a consequence of complete
monotonicity on the *closed* half-line: `IsCompletelyMonotone` builds in `Set.Ici 0`, so `f` takes a
real value at `0`, and the representing measure has total mass `f 0`. On the open half-line alone
the value at `0` need not exist and the representing measure can be infinite — `1/t` is completely
monotone on `(0, ∞)` with representing measure Lebesgue.

## Implementation

`Bernstein/Measures.lean` supplies the Chafaï approximating measures `chafaiRescaled f n` on `ℝ≥0`
and the reconstruction identity `f x - L = ∫ bernsteinKernel n x ∂(chafaiRescaled f n)`, where
`L = lim_{t→∞} f t`. Those measures are uniformly mass-bounded and, by `Bernstein/Tightness.lean`,
tight. The three remaining steps are:

1. extract a weak limit `μ₀` from tightness;
2. pass the reconstruction identity to that limit, replacing the Bernstein kernel by `e^{-xp}`,
   which represents the non-constant part `f - L`;
3. add the atom `L • δ₀`, whose Laplace transform is the constant `L`, to represent `f` itself.

Step 1 uses `finite_measure_cluster_limit` rather than its subsequence form
`finite_measure_subseq_limit`: the latter needs `FirstCountableTopology (FiniteMeasure ℝ≥0)`, and
Mathlib's metrizability instances for spaces of measures are stated for `ProbabilityMeasure`, not
`FiniteMeasure`. No subsequence is actually required — every ingredient is a filter limit, so an
ultrafilter below `atTop` suffices, and being `NeBot` it still gives uniqueness of limits.

## References

* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B (Bernstein theorem milestone).

* D. Chafaï, *Aspects of the Bernstein theorem* (2013) — the approximating measures this proof
  passes to the limit.
* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions* (de Gruyter, 2nd ed. 2012), Ch. 1.
-/

public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology

namespace TauCeti

variable {f : ℝ → ℝ}

/-- **Bernstein's theorem, existence half.** A completely monotone function on `[0, ∞)` is the
Laplace transform of a finite positive measure on `ℝ≥0`.

Uniqueness of that measure is not asserted here; see the module docstring. -/
theorem exists_isFiniteMeasure_integral_exp_neg_mul_eq_of_isCompletelyMonotone
    (hcm : IsCompletelyMonotone f) :
    ∃ μ : Measure ℝ≥0, IsFiniteMeasure μ ∧
      ∀ t : ℝ, 0 ≤ t → f t = ∫ x, Real.exp (-t * (x : ℝ)) ∂μ := by
  obtain ⟨L, C, hL, hL_nn, -, hmass⟩ := chafaiRescaled_prokhorov_mass_bound f hcm
  have hfin : ∀ n, IsFiniteMeasure (chafaiRescaled f n) := fun n => (hmass n).1
  have hmass' : ∀ n, (chafaiRescaled f n) univ ≤ (C : ℝ≥0∞) := fun n => (hmass n).2
  obtain ⟨μ₀, U, hU, hμ₀fin, -, hweak⟩ :=
    finite_measure_cluster_limit (chafaiRescaled f) C hmass'
      (isTightMeasureSet_range_chafaiRescaled hcm)
  haveI : (U : Filter ℕ).NeBot := U.neBot'
  -- The limit represents the non-constant part `f - L`.
  have key : ∀ t : ℝ, 0 ≤ t → f t - L = ∫ p, Real.exp (-(t * (p : ℝ))) ∂μ₀ := by
    intro t ht
    have hlap : Tendsto (fun n => ∫ p, Real.exp (-(t * (p : ℝ))) ∂(chafaiRescaled f n))
        (U : Filter ℕ) (nhds (∫ p, Real.exp (-(t * (p : ℝ))) ∂μ₀)) :=
      chafaiRescaled_tendsto_laplace_integral_of_weak hweak ht
    have herr : Tendsto (fun n => ∫ p : ℝ≥0,
        (bernsteinKernel n t (p : ℝ) - Real.exp (-(t * (p : ℝ))))
          ∂(chafaiRescaled f n)) (U : Filter ℕ) (nhds 0) :=
      (integral_bernsteinKernel_sub_laplaceKernel_tendsto_zero_of_mass_bound
        (C := (C : ℝ)) (chafaiRescaled f)
        (Eventually.of_forall fun n => (hmass' n).trans
          (by simp [ENNReal.ofReal_coe_nnreal])) t ht).mono_left hU
    -- Split the error integral, using that both kernels are bounded continuous.
    have hsplit : ∀ n, ∫ p : ℝ≥0,
        (bernsteinKernel n t (p : ℝ) - Real.exp (-(t * (p : ℝ)))) ∂(chafaiRescaled f n)
          = (∫ p, bernsteinKernel n t (p : ℝ) ∂(chafaiRescaled f n))
            - ∫ p, Real.exp (-(t * (p : ℝ))) ∂(chafaiRescaled f n) := by
      intro n
      haveI := hfin n
      have hb : Integrable (fun p : ℝ≥0 => bernsteinKernel n t (p : ℝ))
          (chafaiRescaled f n) := by
        have h := (bernsteinKernelBoundedContinuous n ht).integrable (chafaiRescaled f n)
        rwa [funext (bernsteinKernelBoundedContinuous_apply n ht)] at h
      have hl : Integrable (fun p : ℝ≥0 => Real.exp (-(t * (p : ℝ))))
          (chafaiRescaled f n) := by
        have h := (laplaceKernelBoundedContinuous ht).integrable (chafaiRescaled f n)
        rwa [funext (laplaceKernelBoundedContinuous_apply ht)] at h
      exact integral_sub hb hl
    -- The Bernstein integral is constantly `f t - L` once `n ≥ 2`.
    have hconst : ∀ᶠ n in (U : Filter ℕ),
        ∫ p, bernsteinKernel n t (p : ℝ) ∂(chafaiRescaled f n) = f t - L := by
      have h2 : ∀ᶠ n in (U : Filter ℕ), 2 ≤ n := hU (eventually_ge_atTop 2)
      filter_upwards [h2] with n hn
      exact chafaiRescaled_integral_bernsteinKernel_eq_sub_tendsto_atTop f hcm n hn t ht L hL
    -- Pass to the limit: `(f t - L) - ∫ laplace → 0`.
    have hdiff : Tendsto (fun n => (f t - L)
        - ∫ p, Real.exp (-(t * (p : ℝ))) ∂(chafaiRescaled f n)) (U : Filter ℕ) (nhds 0) := by
      refine herr.congr' ?_
      filter_upwards [hconst] with n hn
      rw [hsplit n, hn]
    have hlim := hdiff.add hlap
    simp only [sub_add_cancel, zero_add] at hlim
    exact tendsto_nhds_unique tendsto_const_nhds hlim
  -- Add the atom `L · δ₀` to recover `f` itself.
  haveI := hμ₀fin
  refine ⟨μ₀ + L.toNNReal • Measure.dirac 0, inferInstance, fun t ht => ?_⟩
  simp only [neg_mul]
  have hlapint : Integrable (fun p : ℝ≥0 => Real.exp (-(t * (p : ℝ)))) μ₀ := by
    have h := (laplaceKernelBoundedContinuous ht).integrable μ₀
    rwa [funext (laplaceKernelBoundedContinuous_apply ht)] at h
  have hatomint : Integrable (fun p : ℝ≥0 => Real.exp (-(t * (p : ℝ))))
      (L.toNNReal • Measure.dirac 0) := by
    have h := (laplaceKernelBoundedContinuous ht).integrable
      (L.toNNReal • Measure.dirac (0 : ℝ≥0))
    rwa [funext (laplaceKernelBoundedContinuous_apply ht)] at h
  rw [integral_add_measure hlapint hatomint, integral_smul_nnreal_measure, integral_dirac]
  simp only [NNReal.coe_zero, mul_zero, neg_zero, Real.exp_zero, NNReal.smul_def, smul_eq_mul,
    mul_one, Real.coe_toNNReal L hL_nn]
  linarith [key t ht]

end TauCeti

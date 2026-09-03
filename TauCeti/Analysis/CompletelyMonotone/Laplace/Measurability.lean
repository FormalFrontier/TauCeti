/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Laplace.Representation
-- Non-public: the Giry-monad measurability criterion, the outer approximation of closed sets by
-- bounded continuous functions and the Weierstrass approximation theorem are used inside proofs
-- only; none of them appears in a statement below.
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# Measurable families of finite measures on `ℝ≥0`

A finite measure on `ℝ≥0` is determined by its Laplace transform at the natural numbers
(`TauCeti.Measure.ext_of_forall_laplaceTransform_natCast_eq`). This file upgrades that
determinacy statement to a *measurable* one: a family `a ↦ μ a` of finite measures on `ℝ≥0`
is measurable for the Giry σ-algebra as soon as each of the scalar functions
`a ↦ laplaceTransform (μ a) n`, `n : ℕ`, is measurable.

The proof uses the exponential change of variables `p ↦ e^{-p}`, which carries `ℝ≥0` into the
unit interval and turns the Laplace transform at `n` into the `n`-th moment. Weierstrass
approximation then makes `a ↦ ∫ g dμ a` measurable for every continuous `g` on the interval, the
outer approximation of a closed set by bounded continuous functions transfers this to
`a ↦ μ a F` for closed `F`, and the closed sets are a π-system generating the Borel σ-algebra.

Because a *unique* finite measure is attached to each parameter value, no measurable-selection
theorem is involved: the family is whatever it is, and the theorem merely certifies it
measurable. This is what turns a fibrewise Bernstein representation into a kernel, in
`TauCeti/Analysis/CompletelyMonotone/Bernstein/Kernel.lean`.

## Main declarations

* `TauCeti.measurable_of_measurable_laplaceTransform_natCast`: a family of finite measures on
  `ℝ≥0` is measurable when its Laplace transforms at the natural numbers are.

## References

* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*
  (de Gruyter, 2nd ed. 2012), Chapter 1.

* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part C, Milestone 2
  (BCR semigroup--Bochner).
-/

public section

open Filter MeasureTheory Set
open scoped BoundedContinuousFunction ENNReal NNReal Topology

namespace TauCeti

/-! ## The exponential change of variables -/

/-- The exponential change of variables `p ↦ e^{-p}`, viewed as a map from `ℝ≥0` to the unit
interval `[0, 1]`. It is injective with left inverse `TauCeti.negLogNNReal`, and it converts the
Laplace transform of a measure on `ℝ≥0` into the moment sequence of the image measure. -/
private noncomputable def expNegUnitInterval (p : ℝ≥0) : ↥(Set.Icc (0 : ℝ) 1) :=
  ⟨Real.exp (-(p : ℝ)), (Real.exp_pos _).le,
    Real.exp_le_one_iff.2 (neg_nonpos.2 p.coe_nonneg)⟩

/-- The logarithmic change of variables `x ↦ -log x`, truncated to `ℝ≥0`; it is a left inverse of
`TauCeti.expNegUnitInterval`. -/
private noncomputable def negLogNNReal (x : ↥(Set.Icc (0 : ℝ) 1)) : ℝ≥0 :=
  Real.toNNReal (-Real.log (x : ℝ))

/-- The value of the exponential change of variables, as a real number. -/
@[simp]
private lemma coe_expNegUnitInterval (p : ℝ≥0) :
    (expNegUnitInterval p : ℝ) = Real.exp (-(p : ℝ)) :=
  (rfl)

/-- The exponential change of variables is continuous. -/
private lemma continuous_expNegUnitInterval : Continuous expNegUnitInterval :=
  Continuous.subtype_mk
    (Real.continuous_exp.comp (continuous_neg.comp NNReal.continuous_coe)) _

/-- The exponential change of variables is measurable. -/
private lemma measurable_expNegUnitInterval : Measurable expNegUnitInterval :=
  continuous_expNegUnitInterval.measurable

/-- The logarithmic change of variables is measurable. It is not continuous at `0`, which is
harmless: `0` is outside the range of `TauCeti.expNegUnitInterval`. -/
private lemma measurable_negLogNNReal : Measurable negLogNNReal :=
  measurable_real_toNNReal.comp ((Real.measurable_log.comp measurable_subtype_coe).neg)

/-- The logarithmic change of variables is a left inverse of the exponential one. -/
@[simp]
private lemma negLogNNReal_expNegUnitInterval (p : ℝ≥0) :
    negLogNNReal (expNegUnitInterval p) = p := by
  simp [negLogNNReal, Real.log_exp]

/-- The exponential change of variables is undone by pushing the image measure forward along
`TauCeti.negLogNNReal`. -/
private lemma map_negLogNNReal_map_expNegUnitInterval (μ : Measure ℝ≥0) :
    ((μ.map expNegUnitInterval).map negLogNNReal) = μ := by
  rw [Measure.map_map measurable_negLogNNReal measurable_expNegUnitInterval]
  simp [Function.comp_def, Measure.map_id']

/-- Under the exponential change of variables the Laplace transform of `μ` at a natural number
`n` is the `n`-th moment of the image measure. -/
private lemma integral_pow_map_expNegUnitInterval (μ : Measure ℝ≥0) (n : ℕ) :
    ∫ x, ((x : ℝ)) ^ n ∂(μ.map expNegUnitInterval) = laplaceTransform μ n := by
  have hsm : AEStronglyMeasurable (fun x : ↥(Set.Icc (0 : ℝ) 1) => ((x : ℝ)) ^ n)
      (μ.map expNegUnitInterval) := Continuous.aestronglyMeasurable (by fun_prop)
  rw [integral_map measurable_expNegUnitInterval.aemeasurable hsm, laplaceTransform_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [coe_expNegUnitInterval, ← Real.exp_nat_mul]
  congr 1
  ring

/-! ## Measurability of a family from its Laplace transforms -/

/-- A continuous function on the unit interval is integrable against any finite measure. -/
private lemma integrable_of_continuous_Icc {ν : Measure ↥(Set.Icc (0 : ℝ) 1)} [IsFiniteMeasure ν]
    {f : ↥(Set.Icc (0 : ℝ) 1) → ℝ} (hf : Continuous f) : Integrable f ν :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- **Measurability from Laplace transforms.** A family of finite measures on `ℝ≥0` indexed by a
measurable space is measurable for the Giry σ-algebra as soon as each of the functions
`a ↦ laplaceTransform (μ a) n`, for `n : ℕ`, is measurable.

Only the natural-number values of the transforms are used, matching the determinacy statement
`TauCeti.Measure.ext_of_forall_laplaceTransform_natCast_eq`. -/
theorem measurable_of_measurable_laplaceTransform_natCast {α : Type*} [MeasurableSpace α]
    {μ : α → Measure ℝ≥0} [∀ a, IsFiniteMeasure (μ a)]
    (h : ∀ n : ℕ, Measurable fun a => laplaceTransform (μ a) n) :
    Measurable μ := by
  set ν : α → Measure ↥(Set.Icc (0 : ℝ) 1) := fun a => (μ a).map expNegUnitInterval with hνdef
  -- The moments of the image measures are measurable in the parameter.
  have hmom : ∀ n : ℕ, Measurable fun a => ∫ x, ((x : ℝ)) ^ n ∂(ν a) := by
    intro n
    have hrw : (fun a => ∫ x, ((x : ℝ)) ^ n ∂(ν a))
        = fun a => laplaceTransform (μ a) n := by
      funext a
      simpa only [hνdef] using integral_pow_map_expNegUnitInterval (μ a) n
    rw [hrw]
    exact h n
  -- Hence so are the integrals of polynomials.
  have hpoly : ∀ p : Polynomial ℝ, Measurable fun a => ∫ x, p.eval ((x : ℝ)) ∂(ν a) := by
    intro p
    have hrw : (fun a => ∫ x, p.eval ((x : ℝ)) ∂(ν a))
        = fun a => ∑ i ∈ Finset.range (p.natDegree + 1),
            p.coeff i * ∫ x, ((x : ℝ)) ^ i ∂(ν a) := by
      funext a
      simp_rw [Polynomial.eval_eq_sum_range]
      rw [integral_finsetSum _ fun i _ =>
        integrable_of_continuous_Icc
          (f := fun x : ↥(Set.Icc (0 : ℝ) 1) => p.coeff i * ((x : ℝ)) ^ i) (by fun_prop)]
      simp_rw [integral_const_mul]
    rw [hrw]
    exact Finset.measurable_sum _ fun i _ => measurable_const.mul (hmom i)
  -- Weierstrass approximation extends this to all continuous functions.
  have hcont : ∀ g : C(↥(Set.Icc (0 : ℝ) 1), ℝ), Measurable fun a => ∫ x, g x ∂(ν a) := by
    intro g
    have happrox : ∀ n : ℕ, ∃ p : Polynomial ℝ,
        ‖p.toContinuousMapOn (Set.Icc (0 : ℝ) 1) - g‖ < 1 / (n + 1) := fun n =>
      exists_polynomial_near_continuousMap 0 1 g (1 / (n + 1)) (by positivity)
    choose q hq using happrox
    have hbound : ∀ (n : ℕ) (x : ↥(Set.Icc (0 : ℝ) 1)),
        ‖(q n).eval ((x : ℝ)) - g x‖ ≤ 1 / ((n : ℝ) + 1) := by
      intro n x
      have hx := ContinuousMap.norm_coe_le_norm
        ((q n).toContinuousMapOn (Set.Icc (0 : ℝ) 1) - g) x
      simpa using hx.trans (hq n).le
    refine measurable_of_tendsto_metrizable
      (f := fun n a => ∫ x, (q n).eval ((x : ℝ)) ∂(ν a)) (fun n => hpoly (q n)) ?_
    rw [tendsto_pi_nhds]
    intro a
    have hgint : Integrable (fun x => g x) (ν a) := integrable_of_continuous_Icc g.continuous
    have hqint : ∀ n, Integrable (fun x : ↥(Set.Icc (0 : ℝ) 1) => (q n).eval ((x : ℝ))) (ν a) :=
      fun n => integrable_of_continuous_Icc ((q n).continuous.comp continuous_subtype_val)
    have key : ∀ n : ℕ, ‖(∫ x, (q n).eval ((x : ℝ)) ∂(ν a)) - ∫ x, g x ∂(ν a)‖
        ≤ (1 / ((n : ℝ) + 1)) * (ν a).real Set.univ := by
      intro n
      rw [← integral_sub (hqint n) hgint]
      exact norm_integral_le_of_norm_le_const
        (Filter.Eventually.of_forall fun x => hbound n x)
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) key ?_
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.mul_const ((ν a).real Set.univ)
  -- Non-negative bounded continuous test functions, in `ℝ≥0∞` form.
  have hlint : ∀ g : ↥(Set.Icc (0 : ℝ) 1) →ᵇ ℝ≥0,
      Measurable fun a => ∫⁻ x, (g x : ℝ≥0∞) ∂(ν a) := by
    intro g
    have hrw : (fun a => ∫⁻ x, (g x : ℝ≥0∞) ∂(ν a))
        = fun a => ENNReal.ofReal (∫ x, ((g x : ℝ)) ∂(ν a)) := by
      funext a
      rw [← BoundedContinuousFunction.toReal_lintegral_coe_eq_integral g (ν a),
        ENNReal.ofReal_toReal (BoundedContinuousFunction.lintegral_lt_top_of_nnreal (ν a) g).ne]
    rw [hrw]
    exact ENNReal.measurable_ofReal.comp
      (hcont ⟨fun x => (g x : ℝ), NNReal.continuous_coe.comp g.continuous⟩)
  -- Outer approximation of closed sets transfers measurability to closed sets.
  have hclosed : ∀ F : Set ↥(Set.Icc (0 : ℝ) 1), IsClosed F → Measurable fun a => ν a F := by
    intro F hF
    have hrw : (fun a => ν a F)
        = fun a => liminf (fun n => ∫⁻ x, (hF.apprSeq n x : ℝ≥0∞) ∂(ν a)) atTop := by
      funext a
      exact (HasOuterApproxClosed.tendsto_lintegral_apprSeq hF (ν a)).liminf_eq.symm
    rw [hrw]
    exact Measurable.liminf fun n => hlint (hF.apprSeq n)
  -- The closed sets are a π-system generating the Borel σ-algebra.
  have hνmeas : Measurable ν := by
    refine Measurable.measure_of_isPiSystem ?_ isPiSystem_isClosed
      (fun F hF => hclosed F hF) (hclosed _ isClosed_univ)
    rw [BorelSpace.measurable_eq (α := ↥(Set.Icc (0 : ℝ) 1)), borel_eq_generateFrom_isClosed]
  -- Undo the change of variables.
  have hrw : μ = fun a => (ν a).map negLogNNReal := by
    funext a
    simpa only [hνdef] using (map_negLogNNReal_map_expNegUnitInterval (μ a)).symm
  rw [hrw]
  exact (Measure.measurable_map negLogNNReal measurable_negLogNNReal).comp hνmeas

end TauCeti

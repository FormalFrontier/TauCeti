/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Stieltjes functions

A Stieltjes function on `(0, ∞)` is a function with a representation

`f(t) = a / t + b + ∫ x, 1 / (t + x) ∂μ`,

where `a` and `b` are nonnegative and `μ` is a positive measure on `ℝ≥0` satisfying
`μ {0} = 0` and `∫ (1 + x)⁻¹ ∂μ < ∞`.  Removing the atom at zero makes the singular coefficient
`a` canonical.  The weighted integrability condition is the standard sharp condition: the
representing measure need not be finite, but it makes the transform finite at every positive
parameter.  Values outside `(0, ∞)` are deliberately unconstrained.

This file introduces the representation predicate and the function class, proves that the
defining integral is genuinely integrable at every positive parameter, and develops the basic
cone API and the elementary reciprocal examples.  These are the foundations for the
Stieltjes/Bernstein-function correspondences requested by the one-parameter-semigroups roadmap.

## Main declarations

* `TauCeti.RepresentsStieltjes`: a measure and two nonnegative coefficients represent a function
  by the Stieltjes formula on `(0, ∞)`.
* `TauCeti.IsStieltjesFunction`: existence of a Stieltjes representation.
* `TauCeti.IsStieltjesFunction.add`, `TauCeti.IsStieltjesFunction.smul`: Stieltjes functions form
  a convex cone.
* `TauCeti.isStieltjesFunction_const`, `TauCeti.isStieltjesFunction_inv`,
  `TauCeti.isStieltjesFunction_inv_const_add`: the basic examples.

## References

* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*,
  2nd ed., Definition 2.1 and Theorem 2.2.
* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B, the
  Stieltjes/Bernstein-function relationships target.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace TauCeti

/-- The weight controlling a Stieltjes representing measure. -/
def stieltjesWeight (x : ℝ≥0) : ℝ := (1 + x)⁻¹

/-- Evaluation of the standard Stieltjes weight. -/
@[simp]
lemma stieltjesWeight_apply (x : ℝ≥0) : stieltjesWeight x = (1 + (x : ℝ))⁻¹ :=
  (rfl)

/-- A measure `μ` with coefficients `a, b ≥ 0` represents `f` as a Stieltjes function if its
standard weight is integrable and the Stieltjes formula holds on `(0, ∞)`. -/
def RepresentsStieltjes (μ : Measure ℝ≥0) (a b : ℝ≥0) (f : ℝ → ℝ) : Prop :=
  μ {0} = 0 ∧ Integrable stieltjesWeight μ ∧
      ∀ t : ℝ, 0 < t → f t = (a : ℝ) / t + (b : ℝ) + ∫ x, (t + (x : ℝ))⁻¹ ∂μ

/-- Characterization of `RepresentsStieltjes` without unfolding its body. -/
theorem representsStieltjes_iff {μ : Measure ℝ≥0} {a b : ℝ≥0} {f : ℝ → ℝ} :
    RepresentsStieltjes μ a b f ↔
      μ {0} = 0 ∧ Integrable stieltjesWeight μ ∧
        ∀ t : ℝ, 0 < t → f t = (a : ℝ) / t + (b : ℝ) + ∫ x, (t + (x : ℝ))⁻¹ ∂μ :=
  Iff.rfl

/-- The Stieltjes kernel is integrable at every positive parameter when its standard weight is. -/
theorem integrable_inv_add {μ : Measure ℝ≥0} (hμ : Integrable stieltjesWeight μ)
    {t : ℝ} (ht : 0 < t) : Integrable (fun x : ℝ≥0 => (t + (x : ℝ))⁻¹) μ := by
  let C : ℝ := max 1 t⁻¹
  refine ((hμ.const_mul C).mono' (by fun_prop) ?_)
  filter_upwards [] with x
  have hx : 0 ≤ (x : ℝ) := x.coe_nonneg
  have htx : 0 < t + (x : ℝ) := add_pos_of_pos_of_nonneg ht hx
  have h1x : 0 < 1 + (x : ℝ) := by positivity
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr htx), stieltjesWeight]
  by_cases h₁ : 1 ≤ t
  · have hden : 1 + (x : ℝ) ≤ t + (x : ℝ) := by linarith
    exact ((inv_le_inv₀ htx h1x).2 hden).trans <| by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (le_max_left 1 t⁻¹) (inv_nonneg.mpr h1x.le)
  · have ht₁ : t ≤ 1 := le_of_not_ge h₁
    have hmul : t * (1 + (x : ℝ)) ≤ t + (x : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_right ht₁ hx]
    have hinv : (t + (x : ℝ))⁻¹ ≤ t⁻¹ * (1 + (x : ℝ))⁻¹ := by
      rw [← mul_inv]
      exact (inv_le_inv₀ htx (mul_pos ht h1x)).2 hmul
    exact hinv.trans <| mul_le_mul_of_nonneg_right (le_max_right _ _) (inv_nonneg.mpr h1x.le)

namespace RepresentsStieltjes

variable {μ ν : Measure ℝ≥0} {a b c d : ℝ≥0} {f g : ℝ → ℝ}

/-- A Stieltjes representing measure has no atom at zero. -/
lemma measure_singleton_zero (h : RepresentsStieltjes μ a b f) : μ {0} = 0 := h.1

/-- The weighted integrability condition on a Stieltjes representing measure. -/
lemma integrable_weight (h : RepresentsStieltjes μ a b f) : Integrable stieltjesWeight μ := h.2.1

/-- Evaluation of a Stieltjes representation at a positive parameter. -/
lemma eq_div_add_add_integral_inv_add (h : RepresentsStieltjes μ a b f) {t : ℝ} (ht : 0 < t) :
    f t = (a : ℝ) / t + (b : ℝ) + ∫ x : ℝ≥0, (t + (x : ℝ))⁻¹ ∂μ :=
  h.2.2 t ht

/-- A represented Stieltjes function is nonnegative on `(0, ∞)`. -/
lemma nonneg (h : RepresentsStieltjes μ a b f) {t : ℝ} (ht : 0 < t) : 0 ≤ f t := by
  rw [h.eq_div_add_add_integral_inv_add ht]
  exact add_nonneg (add_nonneg (div_nonneg a.coe_nonneg ht.le) b.coe_nonneg)
    (integral_nonneg fun x => inv_nonneg.mpr (add_nonneg ht.le x.coe_nonneg))

/-- A Stieltjes representation depends only on the represented function's values on `(0, ∞)`. -/
lemma congr (h : RepresentsStieltjes μ a b f) (hfg : EqOn g f (Ioi 0)) :
    RepresentsStieltjes μ a b g := by
  refine ⟨h.measure_singleton_zero, h.integrable_weight, fun t ht => ?_⟩
  rw [hfg ht, h.eq_div_add_add_integral_inv_add ht]

/-- The sum of two Stieltjes representations is represented by the sum of their coefficients and
measures. -/
lemma add (hf : RepresentsStieltjes μ a b f) (hg : RepresentsStieltjes ν c d g) :
    RepresentsStieltjes (μ + ν) (a + c) (b + d) (f + g) := by
  refine ⟨by simp [hf.measure_singleton_zero, hg.measure_singleton_zero],
    hf.integrable_weight.add_measure hg.integrable_weight, fun t ht => ?_⟩
  rw [Pi.add_apply, hf.eq_div_add_add_integral_inv_add ht,
    hg.eq_div_add_add_integral_inv_add ht,
    integral_add_measure (integrable_inv_add hf.integrable_weight ht)
      (integrable_inv_add hg.integrable_weight ht)]
  push_cast
  ring

/-- A nonnegative scalar multiple of a Stieltjes representation is represented by scaling its
coefficients and measure. -/
lemma smul (h : RepresentsStieltjes μ a b f) {r : ℝ} (hr : 0 ≤ r) :
    RepresentsStieltjes ((ENNReal.ofReal r) • μ) (r.toNNReal * a) (r.toNNReal * b) (r • f) := by
  refine ⟨by simp [h.measure_singleton_zero],
    h.integrable_weight.smul_measure ENNReal.ofReal_ne_top, fun t ht => ?_⟩
  rw [Pi.smul_apply, smul_eq_mul]
  rw [h.eq_div_add_add_integral_inv_add ht, integral_smul_measure]
  simp only [ENNReal.toReal_ofReal hr, smul_eq_mul]
  push_cast
  rw [Real.coe_toNNReal r hr]
  ring

end RepresentsStieltjes

/-- A real function is a Stieltjes function if it has a standard Stieltjes representation on
`(0, ∞)`. -/
def IsStieltjesFunction (f : ℝ → ℝ) : Prop :=
  ∃ a b : ℝ≥0, ∃ μ : Measure ℝ≥0, RepresentsStieltjes μ a b f

/-- Characterization of a Stieltjes function by its representing data. -/
theorem isStieltjesFunction_iff {f : ℝ → ℝ} :
    IsStieltjesFunction f ↔
      ∃ a b : ℝ≥0, ∃ μ : Measure ℝ≥0, RepresentsStieltjes μ a b f :=
  Iff.rfl

namespace IsStieltjesFunction

variable {f g : ℝ → ℝ}

/-- A Stieltjes function is nonnegative on `(0, ∞)`. -/
@[grind =>]
lemma nonneg (hf : IsStieltjesFunction f) {t : ℝ} (ht : 0 < t) : 0 ≤ f t := by
  obtain ⟨a, b, μ, hμ⟩ := hf
  exact hμ.nonneg ht

/-- The Stieltjes property depends only on values on `(0, ∞)`. -/
lemma congr (hf : IsStieltjesFunction f) (hfg : EqOn g f (Ioi 0)) : IsStieltjesFunction g := by
  obtain ⟨a, b, μ, hμ⟩ := hf
  exact ⟨a, b, μ, hμ.congr hfg⟩

/-- Stieltjes functions are closed under addition. -/
lemma add (hf : IsStieltjesFunction f) (hg : IsStieltjesFunction g) :
    IsStieltjesFunction (f + g) := by
  obtain ⟨a, b, μ, hμ⟩ := hf
  obtain ⟨c, d, ν, hν⟩ := hg
  exact ⟨a + c, b + d, μ + ν, hμ.add hν⟩

/-- Stieltjes functions are closed under multiplication by a nonnegative scalar. -/
lemma smul (hf : IsStieltjesFunction f) {r : ℝ} (hr : 0 ≤ r) :
    IsStieltjesFunction (r • f) := by
  obtain ⟨a, b, μ, hμ⟩ := hf
  exact ⟨r.toNNReal * a, r.toNNReal * b, ENNReal.ofReal r • μ, hμ.smul hr⟩

end IsStieltjesFunction

/-- Every nonnegative constant function is Stieltjes. -/
theorem isStieltjesFunction_const {b : ℝ} (hb : 0 ≤ b) :
    IsStieltjesFunction (fun _ : ℝ => b) := by
  refine ⟨0, b.toNNReal, 0, ?_⟩
  refine ⟨by simp, integrable_zero_measure, fun t ht => ?_⟩
  simp [Real.coe_toNNReal b hb]

/-- The zero function is Stieltjes. -/
theorem isStieltjesFunction_zero : IsStieltjesFunction (fun _ : ℝ => 0) := by
  simpa using isStieltjesFunction_const le_rfl

/-- The reciprocal `t ↦ t⁻¹` is Stieltjes; it is the singular coefficient with zero measure. -/
theorem isStieltjesFunction_inv : IsStieltjesFunction (fun t : ℝ => t⁻¹) := by
  refine ⟨1, 0, 0, ?_⟩
  refine ⟨by simp, integrable_zero_measure, fun t ht => ?_⟩
  simp [div_eq_mul_inv]

/-- For `x ≥ 0`, the shifted reciprocal `t ↦ (t + x)⁻¹` is Stieltjes.  At `x = 0` it is the
singular term; for `0 < x` it is represented by the Dirac mass at `x`. -/
theorem isStieltjesFunction_inv_const_add {x : ℝ} (hx : 0 ≤ x) :
    IsStieltjesFunction (fun t : ℝ => (x + t)⁻¹) := by
  by_cases hzero : x = 0
  · subst x
    simpa using isStieltjesFunction_inv
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hzero)
    have hxnn : x.toNNReal ≠ 0 := ne_of_gt (Real.toNNReal_pos.mpr hxpos)
    refine ⟨0, 0, Measure.dirac x.toNNReal, ?_⟩
    refine ⟨by simp [hxnn], integrable_dirac (by simp), fun t _ht => ?_⟩
    rw [integral_dirac]
    simp [Real.coe_toNNReal x hx, add_comm]

end TauCeti

end

end

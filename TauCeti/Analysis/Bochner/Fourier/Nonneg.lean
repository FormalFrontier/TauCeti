/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import TauCeti.LinearAlgebra.Matrix.PosSemidef
-- The remaining imports are proof-only: the Fejér averaging argument uses dominated convergence,
-- Fubini, simple-function approximation, the Haar ball formulas and negation invariance, the
-- Fourier atom kernel with its Fourier-transform bridge, the continuity of `𝓕`/`𝓕⁻`, and the
-- kernel Cauchy–Schwarz bounds;
-- the integrability theorem additionally uses Fourier inversion, the Gaussian Fourier
-- transform, the Gaussian kernel, and the real part of a Bochner integral.
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.Bochner.Fourier.Convention
import TauCeti.Analysis.Fourier.Continuous
import TauCeti.Analysis.Bochner.Gaussian.Basic
import TauCeti.Analysis.PositiveDefinite.Kernel.Bounds

/-!
# Nonnegativity of the Fourier transform of a positive-definite function

For a continuous, integrable function `F : V → ℂ` on a finite-dimensional real inner-product
space whose subtraction kernel `(a, b) ↦ F (a - b)` is positive definite, the Fourier transform
`𝓕 F` is real and nonnegative: its real part is nonnegative at every frequency and its imaginary
part vanishes. This is the analytic half of Bochner's theorem.

The real-part nonnegativity is proved by Fejér ball averaging. For a fixed frequency `ξ`, the
twisted function `ψ = fourierAtom ξ * F` is still positive definite (Schur product with the
Fourier atom kernel), continuous, and integrable, and `𝓕 F ξ = ∫ ψ`. For `R > 0` the averaged
double integral `J_R = vol(B_R)⁻¹ ∬_{B_R × B_R} ψ (x - y)` has nonnegative real part because it
is a limit of positive-definite double sums (simple-function approximation of the identity),
while Fubini rewrites `J_R = ∫ ψ · overlapRatio R` whose dominated limit as `R → ∞` is `∫ ψ`.

Building on this, the Fourier transform of such a function is itself *integrable*: testing
against a shrinking family of Gaussians and using the Parseval/Fubini identity bounds
`∫ (𝓕 F) · exp (-t‖·‖²)` by `(F 0).re` uniformly in `t`, and Fatou's lemma passes to the limit.

Adapted (Apache 2.0) from the Bochner–Minlos formalization by Michael R. Douglas
(https://github.com/mrdouglasny/bochner, revision `08eb302`), source files `Bochner/FejerPD.lean`
and `Bochner/Main.lean`; the arguments are ported with the positive-definiteness hypotheses
restated through `Matrix.PosSemidef`.

## Main declarations

* `TauCeti.fourier_re_nonneg_of_posSemidef`: the Fourier transform of a
  continuous integrable positive-definite function has nonnegative real part.
* `TauCeti.fourier_im_eq_zero_of_map_neg_eq_conj` and
  `TauCeti.fourier_eq_re_of_map_neg_eq_conj`: for an integrable *conjugate-symmetric* `F`
  (continuity is not needed), the imaginary part of `𝓕 F` vanishes and `𝓕 F` equals its own real
  part; `TauCeti.fourier_im_eq_zero_of_posSemidef` and
  `TauCeti.fourier_eq_re_of_posSemidef` are the positive-definite specializations.
* `TauCeti.integrable_fourier_of_posSemidef`: the Fourier transform of a
  continuous integrable positive-definite function is integrable.
* `TauCeti.fourierInv_re_nonneg_of_posSemidef`,
  `TauCeti.fourierInv_eq_re_of_posSemidef`,
  `TauCeti.integrable_fourierInv_of_posSemidef` and
  `TauCeti.measurable_ofReal_re_fourierInv`: the same facts for the inverse transform `𝓕⁻ F`,
  which is the density of the representing measure of Bochner's theorem.

## References

* W. Rudin, *Fourier Analysis on Groups* (1962), Theorem 1.4.3.
* G. B. Folland, *A Course in Abstract Harmonic Analysis*, §4.2, Lemma 4.8.
* Roadmap: TauCetiRoadmap/OneParameterSemigroups/README.md, Part C (Bochner milestone).
-/

public section

open Complex ComplexConjugate Filter MeasureTheory
open scoped ComplexOrder FourierTransform Topology

namespace TauCeti

/-! ### A simple-function expansion for integrals of compositions -/

section SimpleFuncExpansion

variable {α : Type*} [MeasurableSpace α]

/-- For a simple function `sn : α → W` and any `g : W → ℂ`,
`∫ g (sn x) ∂μ = ∑ u ∈ sn.range, μ (sn ⁻¹' {u}).toReal • g u`. -/
private theorem integral_simpleFunc_comp {W : Type*} (sn : SimpleFunc α W) (g : W → ℂ)
    (μ : Measure α) [IsFiniteMeasure μ] :
    ∫ x, g (sn x) ∂μ = ∑ u ∈ sn.range, (μ (⇑sn ⁻¹' {u})).toReal • g u := by
  classical
  have hmap : ∀ x, g (sn x) = sn.map g x := fun x => (SimpleFunc.map_apply g sn x).symm
  simp_rw [hmap]
  rw [(sn.map g).integral_eq_sum (SimpleFunc.integrable_of_isFiniteMeasure _),
    SimpleFunc.range_map]
  refine Finset.sum_image' _ fun b _ => ?_
  calc μ.real (⇑(sn.map g) ⁻¹' {g b}) • g b
      = (∑ u ∈ sn.range with g u = g b, μ (⇑sn ⁻¹' {u})).toReal • g b := by
        rw [measureReal_def, SimpleFunc.map_preimage_singleton,
          sn.sum_measure_preimage_singleton]
    _ = ∑ u ∈ sn.range with g u = g b, (μ (⇑sn ⁻¹' {u})).toReal • g u := by
        rw [ENNReal.toReal_sum fun u _ => measure_ne_top μ _, Finset.sum_smul]
        exact Finset.sum_congr rfl fun u hu => by rw [(Finset.mem_filter.mp hu).2]

/-- **Discretising a double integral against a simple function.** For a finite measure `μ` and a
simple function `sn`, the double integral of `ψ (sn x - sn y)` is the double sum over the range of
`sn`, each term weighted by the measures of the two preimages. -/
private theorem double_integral_comp_simpleFunc_eq_sum {W : Type*} [Sub W] (ψ : W → ℂ)
    (μ : Measure α) [IsFiniteMeasure μ] (sn : SimpleFunc α W) :
    (∫ x, ∫ y, ψ (sn x - sn y) ∂μ ∂μ) =
      ∑ u ∈ sn.range, ∑ v ∈ sn.range,
        ((μ (sn ⁻¹' {u})).toReal : ℂ) *
        ((μ (sn ⁻¹' {v})).toReal : ℂ) * ψ (u - v) := by
  classical
  set R := sn.range with hR
  have h_inner : ∀ x, ∫ y, ψ (sn x - sn y) ∂μ =
      ∑ v ∈ R, (μ (⇑sn ⁻¹' {v})).toReal • ψ (sn x - v) :=
    fun x => integral_simpleFunc_comp sn (fun v => ψ (sn x - v)) μ
  simp_rw [h_inner, Complex.real_smul]
  rw [integral_finsetSum _ (fun v _ => ?_)]
  · -- Expand the outer integral via `integral_simpleFunc_comp`.
    have h_expand : ∀ v, ∫ a, (↑(μ (⇑sn ⁻¹' {v})).toReal : ℂ) * ψ (sn a - v) ∂μ =
        ∑ u ∈ R, (μ (⇑sn ⁻¹' {u})).toReal •
          ((↑(μ (⇑sn ⁻¹' {v})).toReal : ℂ) * ψ (u - v)) := fun v =>
      integral_simpleFunc_comp sn
        (fun w => (↑(μ (⇑sn ⁻¹' {v})).toReal : ℂ) * ψ (w - v)) μ
    simp_rw [h_expand]
    rw [Finset.sum_comm]
    congr 1
    ext u
    congr 1
    ext v
    rw [Complex.real_smul]
    ring
  · -- `c * ψ (sn · - v)` is integrable for the finite measure `μ`.
    refine Integrable.const_mul ?_ _
    -- as above: rewrite to the `SimpleFunc` coercion, which carries the integrability instance
    have hmap : (fun x => ψ (sn x - v)) = ⇑(sn.map fun u => ψ (u - v)) :=
      funext fun x => (SimpleFunc.map_apply (fun u => ψ (u - v)) sn x).symm
    rw [hmap]
    exact SimpleFunc.integrable_of_isFiniteMeasure _

/-- Precomposing any function with a simple function is a.e. strongly measurable: the composite
is itself (the coercion of) a simple function. -/
private theorem aestronglyMeasurable_comp_simpleFunc {β : Type*} [TopologicalSpace β]
    (sn : SimpleFunc α α) (g : α → β) (μ : Measure α) :
    AEStronglyMeasurable (fun x => g (sn x)) μ := by
  -- `SimpleFunc.map_apply` is stated pointwise, so the rewrite needs the `funext`ed form; the
  -- coercion `⇑(sn.map g)` is what carries the `SimpleFunc` measurability instance.
  have hmap : (fun x => g (sn x)) = ⇑(sn.map g) :=
    funext fun x => (SimpleFunc.map_apply g sn x).symm
  rw [hmap]
  exact (SimpleFunc.map _ _).aestronglyMeasurable

end SimpleFuncExpansion

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-! ### Consequences of positive definiteness for a subtraction kernel -/

section KernelConsequences

variable {ψ : V → ℂ}

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The positive-definite double sum attached to a subtraction kernel has nonnegative real
part. -/
private theorem re_sum_nonneg_of_kernel
    (hpd : Matrix.PosSemidef fun a b : V => ψ (a - b)) {ι : Type*} [Fintype ι]
    (x : ι → V) (c : ι → ℂ) :
    0 ≤ (∑ i, ∑ j, conj (c i) * c j * ψ (x i - x j)).re := by
  have h := (posSemidef_iff_finite_sum.mp hpd).2 x c
  simpa only [RCLike.star_def, mul_comm, mul_left_comm, mul_assoc] using
    (Complex.nonneg_iff.mp h).1

end KernelConsequences

/-! ### Step A: the positive-definite double integral has nonnegative real part -/

/-- Simple-function approximation of the Fejér double integral: for a finite measure, the double
integrals along `StronglyMeasurable.approx id` converge to `∬ ψ (x - y)`.

Dominated convergence twice, with the uniform bound `‖ψ z‖ ≤ (ψ 0).re` supplied by positive
definiteness. -/
private theorem exists_simpleFunc_tendsto_double_integral (ψ : V → ℂ)
    (hpd : Matrix.PosSemidef fun a b : V => ψ (a - b)) (hcont : Continuous ψ)
    (μ : Measure V) [IsFiniteMeasure μ] :
    ∃ s : ℕ → SimpleFunc V V,
      Tendsto (fun n => ∫ x, ∫ y, ψ (s n x - s n y) ∂μ ∂μ) atTop
        (nhds (∫ x, ∫ y, ψ (x - y) ∂μ ∂μ)) := by
  have hid : StronglyMeasurable (id : V → V) := stronglyMeasurable_id
  refine ⟨hid.approx, ?_⟩
  have h_ptwise : ∀ x, Tendsto (fun n => hid.approx n x) atTop (nhds x) :=
    fun x => by simpa using hid.tendsto_approx x
  have hbound : ∀ z, ‖ψ z‖ ≤ (ψ 0).re := norm_apply_le_map_zero_re_of_posSemidef hpd
  -- The inner integral converges for each `x` by dominated convergence.
  have h_inner_conv : ∀ x, Tendsto
      (fun n => ∫ y, ψ (hid.approx n x - hid.approx n y) ∂μ)
      atTop (nhds (∫ y, ψ (x - y) ∂μ)) := by
    intro x
    have hmeas : ∀ n, AEStronglyMeasurable
        (fun y => ψ (hid.approx n x - hid.approx n y)) μ := fun n =>
      aestronglyMeasurable_comp_simpleFunc (hid.approx n)
        (fun v => ψ (hid.approx n x - v)) μ
    have hbd : ∀ n, ∀ᵐ y ∂μ, ‖ψ (hid.approx n x - hid.approx n y)‖ ≤ (ψ 0).re :=
      fun n => ae_of_all _ (fun y => hbound _)
    have hlim : ∀ᵐ y ∂μ, Tendsto
        (fun n => ψ (hid.approx n x - hid.approx n y))
        atTop (nhds (ψ (x - y))) :=
      ae_of_all _ (fun y =>
        (hcont.continuousAt.tendsto.comp ((h_ptwise x).sub (h_ptwise y))))
    exact tendsto_integral_of_dominated_convergence
      (fun _ => (ψ 0).re) hmeas (integrable_const _) hbd hlim
  -- The outer integral converges by dominated convergence.
  have hmeas2 : ∀ n, AEStronglyMeasurable
      (fun x => ∫ y, ψ (hid.approx n x - hid.approx n y) ∂μ) μ := fun n =>
    aestronglyMeasurable_comp_simpleFunc (hid.approx n)
      (fun u => ∫ y, ψ (u - hid.approx n y) ∂μ) μ
  have hbd2 : ∀ n, ∀ᵐ x ∂μ,
      ‖∫ y, ψ (hid.approx n x - hid.approx n y) ∂μ‖ ≤
        (ψ 0).re * (μ Set.univ).toReal := fun n =>
    ae_of_all _ fun _ => norm_integral_le_of_norm_le_const (ae_of_all _ fun _ => hbound _)
  exact tendsto_integral_of_dominated_convergence
    (fun _ => (ψ 0).re * (μ Set.univ).toReal)
    hmeas2 (integrable_const _) hbd2 (ae_of_all _ h_inner_conv)

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] in
/-- **The double integral of a positive-definite kernel along a simple function has nonnegative
real part.** For a positive-definite `fun a b => ψ (a - b)`, a finite measure `μ` and a simple
function `sn`, the real part of `∬ ψ (sn x - sn y)` is nonnegative. -/
private theorem re_double_integral_simpleFunc_nonneg (ψ : V → ℂ)
    (hpd : Matrix.PosSemidef fun a b : V => ψ (a - b))
    (μ : Measure V) [IsFiniteMeasure μ] (sn : SimpleFunc V V) :
    0 ≤ (∫ x, ∫ y, ψ (sn x - sn y) ∂μ ∂μ).re := by
  classical
  rw [double_integral_comp_simpleFunc_eq_sum ψ μ sn]
  -- Reindex both sums over the coercion of the range to a type, then apply positive definiteness.
  set R := sn.range with hR
  simp_rw [← Finset.sum_coe_sort R]
  set c : R → ℂ := fun i => ((μ (sn ⁻¹' {(i : V)})).toReal : ℂ) with hc
  have hpd_eval := re_sum_nonneg_of_kernel hpd (fun i : R => (i : V)) c
  -- The coefficients are real, so the conjugation is the identity.
  have hpd_match : (∑ i : R, ∑ j : R, conj (c i) * c j * ψ ((i : V) - (j : V))) =
      ∑ i : R, ∑ j : R, c i * c j * ψ ((i : V) - (j : V)) :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      simp only [hc, Complex.conj_ofReal]
  rwa [hpd_match] at hpd_eval

/-- The double integral of a positive-definite function over `S × S` has nonnegative real part.

Approximate `id : V → V` by simple functions `sₙ`. Each `∬ ψ (sₙ x - sₙ y)` is a positive-definite
double sum with real coefficients, so has nonnegative real part
(`re_double_integral_simpleFunc_nonneg`); the sums converge to `∬ ψ (x - y)`
(`exists_simpleFunc_tendsto_double_integral`), so nonnegativity passes to the limit.
See Rudin, *Fourier Analysis on Groups*, proof of Theorem 1.4.3, step 1. -/
private theorem pd_double_integral_re_nonneg (ψ : V → ℂ)
    (hpd : Matrix.PosSemidef fun a b : V => ψ (a - b))
    (hcont : Continuous ψ) (S : Set V) (hSbdd : Bornology.IsBounded S) :
    0 ≤ (∫ x in S, ∫ y in S, ψ (x - y)).re := by
  let μ := (volume : Measure V).restrict S
  have hfm : IsFiniteMeasure μ := ⟨by simpa [μ] using hSbdd.measure_lt_top⟩
  obtain ⟨s, hs_tendsto⟩ := exists_simpleFunc_tendsto_double_integral ψ hpd hcont μ
  exact ge_of_tendsto' ((Complex.continuous_re.tendsto _).comp hs_tendsto)
    fun n => re_double_integral_simpleFunc_nonneg ψ hpd μ (s n)

/-! ### The Fejér overlap ratio -/

/-- The overlap ratio `vol (B_R ∩ B_R(v)) / vol B_R` appearing in the Fejér average. -/
private noncomputable def overlapRatio (R : ℝ) (v : V) : ℝ :=
  if (volume (Metric.closedBall (0 : V) R)).toReal = 0 then 0
  else (volume (Metric.closedBall (0 : V) R ∩ Metric.closedBall v R)).toReal /
       (volume (Metric.closedBall (0 : V) R)).toReal

/-- The overlap ratio is at most one. -/
private theorem overlapRatio_le_one (R : ℝ) (v : V) : overlapRatio R v ≤ 1 := by
  unfold overlapRatio
  split_ifs with h
  · exact zero_le_one
  · exact div_le_one_of_le₀
      (ENNReal.toReal_mono (ne_of_lt measure_closedBall_lt_top)
        (measure_mono Set.inter_subset_left))
      ENNReal.toReal_nonneg

/-- The overlap ratio is nonnegative. -/
private theorem overlapRatio_nonneg (R : ℝ) (v : V) : 0 ≤ overlapRatio R v := by
  unfold overlapRatio
  split_ifs
  · exact le_refl 0
  · exact div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

/-- The overlap ratio is measurable in the translation variable. -/
private theorem measurable_overlapRatio (R : ℝ) : Measurable (overlapRatio R : V → ℝ) := by
  unfold overlapRatio
  split_ifs with h
  · exact measurable_const
  · refine Measurable.div_const ?_ _
    let E := {p : V × V | p.2 ∈ Metric.closedBall (0 : V) R ∧ dist p.2 p.1 ≤ R}
    have hE : MeasurableSet E :=
      .inter (measurableSet_closedBall.preimage measurable_snd)
        ((isClosed_le (continuous_snd.dist continuous_fst) continuous_const).measurableSet)
    have hfib : ∀ v : V, Prod.mk v ⁻¹' E =
        Metric.closedBall (0 : V) R ∩ Metric.closedBall v R := by
      intro v
      ext x
      simp [E, Metric.mem_closedBall, Set.mem_inter_iff, dist_comm x v]
    simp_rw [← hfib]
    exact (measurable_measure_prodMk_left hE (ν := volume)).ennreal_toReal

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- Ball containment: `closedBall 0 (R - ‖v‖) ⊆ closedBall 0 R ∩ closedBall v R`. -/
private theorem closedBall_sub_norm_subset (v : V) (R : ℝ) :
    Metric.closedBall (0 : V) (R - ‖v‖) ⊆
    Metric.closedBall (0 : V) R ∩ Metric.closedBall v R := fun x hx =>
  ⟨Metric.closedBall_subset_closedBall (by linarith [norm_nonneg v]) hx,
    Metric.closedBall_subset_closedBall' (by simp [dist_zero_left]) hx⟩

/-- The overlap ratio tends to one along integer radii, for a fixed translation.

Since `closedBall 0 (R - ‖v‖) ⊆ closedBall 0 R ∩ closedBall v R`, the ratio is at least
`((R - ‖v‖) / R) ^ d → 1` by the Haar ball formula, and it is at most `1`; squeeze. -/
private theorem overlapRatio_tendsto_one (v : V) :
    Tendsto (fun n : ℕ => overlapRatio (n : ℝ) v) atTop (nhds 1) := by
  set d := Module.finrank ℝ V
  -- Lower bound: `((n - ‖v‖) / n) ^ d → 1`.
  have hlower : Tendsto (fun n : ℕ => ((↑n - ‖v‖) / ↑n) ^ d) atTop (nhds 1) := by
    have h : Tendsto (fun n : ℕ => (↑n - ‖v‖) / (↑n : ℝ)) atTop (nhds 1) := by
      have h1 : ∀ᶠ n : ℕ in atTop, (↑n - ‖v‖) / (↑n : ℝ) = 1 - ‖v‖ / ↑n := by
        filter_upwards [Filter.eventually_gt_atTop 0] with n hn
        field_simp
      have hc : Tendsto (fun n : ℕ => ‖v‖ / (↑n : ℝ)) atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
      exact Tendsto.congr' (EventuallyEq.symm h1)
        (by simpa using Tendsto.sub tendsto_const_nhds hc)
    simpa using h.pow (n := d)
  -- The ratio dominates the lower bound once `n > ‖v‖`, by the Haar ball formula.
  have hdom : ∀ᶠ n : ℕ in atTop, ((↑n - ‖v‖) / ↑n) ^ d ≤ overlapRatio (n : ℝ) v := by
    filter_upwards [Filter.eventually_gt_atTop (⌈‖v‖⌉₊)] with n hn
    have hn_gt : ‖v‖ < (n : ℝ) :=
      lt_of_le_of_lt (Nat.le_ceil _) (Nat.cast_lt.mpr hn)
    have hn_pos : (0 : ℝ) < n := by linarith [norm_nonneg v]
    have hsub_nn : (0 : ℝ) ≤ ↑n - ‖v‖ := by linarith
    have hvol_pos := Metric.measure_closedBall_pos (volume : Measure V) 0 hn_pos
    have hvol_ne_top : volume (Metric.closedBall (0 : V) (↑n)) ≠ ⊤ :=
      ne_of_lt measure_closedBall_lt_top
    have hvol_toReal_pos : 0 < (volume (Metric.closedBall (0 : V) (↑n))).toReal :=
      ENNReal.toReal_pos (ne_of_gt hvol_pos) hvol_ne_top
    unfold overlapRatio
    rw [ite_eq_right (ne_of_gt hvol_toReal_pos)]
    have hball_pos : 0 < (volume (Metric.ball (0 : V) 1)).toReal :=
      ENNReal.toReal_pos (ne_of_gt (Metric.measure_ball_pos volume 0 one_pos))
        (ne_of_lt measure_ball_lt_top)
    have hvol_sub : (volume (Metric.closedBall (0 : V) (↑n - ‖v‖))).toReal =
        (↑n - ‖v‖) ^ d * (volume (Metric.ball (0 : V) 1)).toReal := by
      rw [Measure.addHaar_closedBall volume (0 : V) hsub_nn, ENNReal.toReal_mul,
          ENNReal.toReal_ofReal (by positivity)]
    have hvol_n : (volume (Metric.closedBall (0 : V) (↑n))).toReal =
        (↑n) ^ d * (volume (Metric.ball (0 : V) 1)).toReal := by
      rw [Measure.addHaar_closedBall volume (0 : V) hn_pos.le, ENNReal.toReal_mul,
          ENNReal.toReal_ofReal (by positivity)]
    calc ((↑n - ‖v‖) / ↑n) ^ d
        = (↑n - ‖v‖) ^ d / (↑n) ^ d := by rw [div_pow]
      _ = ((↑n - ‖v‖) ^ d * (volume (Metric.ball (0 : V) 1)).toReal) /
          ((↑n) ^ d * (volume (Metric.ball (0 : V) 1)).toReal) := by
          rw [mul_div_mul_right _ _ (ne_of_gt hball_pos)]
      _ = (volume (Metric.closedBall (0 : V) (↑n - ‖v‖))).toReal /
          (volume (Metric.closedBall (0 : V) (↑n))).toReal := by
          rw [hvol_sub, hvol_n]
      _ ≤ (volume (Metric.closedBall (0 : V) (↑n) ∩ Metric.closedBall v (↑n))).toReal /
          (volume (Metric.closedBall (0 : V) (↑n))).toReal :=
          div_le_div_of_nonneg_right
            (ENNReal.toReal_mono
              (ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_left)
                measure_closedBall_lt_top))
              (measure_mono (closedBall_sub_norm_subset v ↑n)))
            hvol_toReal_pos.le
  -- Squeeze between that lower bound and the constant `1`.
  exact Filter.Tendsto.squeeze' hlower tendsto_const_nhds hdom
    (Filter.Eventually.of_forall fun n => overlapRatio_le_one (n : ℝ) v)

/-! ### Step B: the Fubini identity for the Fejér average -/

/-- Inner integral substitution via Haar invariance:
`∫ y in closedBall 0 R, ψ (x - y) = ∫ v in closedBall x R, ψ v`. -/
private theorem inner_integral_sub (ψ : V → ℂ) (x : V) (R : ℝ) :
    ∫ y in Metric.closedBall (0 : V) R, ψ (x - y) =
    ∫ v in Metric.closedBall x R, ψ v := by
  rw [← integral_indicator measurableSet_closedBall,
      ← integral_indicator measurableSet_closedBall]
  have hind : ∀ y : V, (Metric.closedBall (0 : V) R).indicator (fun y => ψ (x - y)) y =
      (Metric.closedBall x R).indicator ψ (x - y) := by
    intro y
    simp only [Set.indicator, Metric.mem_closedBall]
    have : dist (x - y) x = dist y 0 := by simp [dist_eq_norm]
    rw [this]
  simp_rw [hind]
  exact integral_sub_left_eq_self ((Metric.closedBall x R).indicator ψ) volume x

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- Indicator equivalence: for the nested ball indicators, membership `v ∈ closedBall x R` can be
transposed to `x ∈ closedBall v R` by `dist_comm`. -/
private theorem indicator_closedBall_inter (ψ : V → ℂ) (R : ℝ) (x v : V) :
    (Metric.closedBall (0 : V) R).indicator
      (fun x => (Metric.closedBall x R).indicator ψ v) x =
    (Metric.closedBall (0 : V) R ∩ Metric.closedBall v R).indicator
      (fun _ => ψ v) x := by
  simp only [Set.indicator, Metric.mem_closedBall, Set.mem_inter_iff, dist_comm v x]
  split_ifs <;> first | rfl | (exfalso; tauto)

/-- The Fejér integrand is integrable on `V × V`: it is the indicator of a compact set applied
to the continuous function `ψ ∘ snd`. -/
private theorem integrable_indicator_prod (ψ : V → ℂ) (hcont : Continuous ψ) (R : ℝ) :
    Integrable (Function.uncurry fun x v =>
      (Metric.closedBall (0 : V) R ∩ Metric.closedBall v R).indicator
        (fun _ => ψ v) x)
      (Measure.prod volume volume) := by
  set S := {p : V × V | p.1 ∈ Metric.closedBall (0 : V) R ∧ dist p.1 p.2 ≤ R}
  have hfeq : (Function.uncurry fun x v =>
      (Metric.closedBall (0 : V) R ∩ Metric.closedBall v R).indicator
        (fun _ => ψ v) x) = S.indicator (ψ ∘ Prod.snd) := by
    ext ⟨x, v⟩
    simp only [Function.uncurry, Set.indicator,
      Metric.mem_closedBall, Set.mem_inter_iff, Function.comp, dist_zero_right, S,
      Set.mem_ofPred_eq]
  rw [hfeq]
  have hS_closed : IsClosed S :=
    (Metric.isClosed_closedBall.preimage continuous_fst).inter
      (isClosed_le (Continuous.dist continuous_fst continuous_snd) continuous_const)
  have hS_bdd : Bornology.IsBounded S := by
    apply Metric.isBounded_closedBall (x := (0 : V × V)) (r := |R| + |R|) |>.subset
    intro ⟨x, v⟩ ⟨hx, hdist⟩
    simp only [Metric.mem_closedBall, dist_zero_right] at hx
    simp only [Metric.mem_closedBall, Prod.dist_eq] at hdist ⊢
    simp only [Prod.fst_zero, Prod.snd_zero, dist_zero_right]
    apply max_le
    · linarith [le_abs_self R, abs_nonneg R]
    · have hv : ‖v‖ ≤ ‖x‖ + ‖v - x‖ := norm_le_insert' v x
      rw [← dist_eq_norm, dist_comm] at hv
      linarith [le_abs_self R]
  exact ((hcont.comp continuous_snd).continuousOn.integrableOn_compact
    (Metric.isCompact_of_isClosed_isBounded hS_closed hS_bdd)).integrable_indicator
    hS_closed.measurableSet

/-- Conversion of the nested set integrals of the Fejér average to indicator form on `V × V`. -/
private theorem fejer_indicator_form (ψ : V → ℂ) (R : ℝ) :
    ∫ x in Metric.closedBall (0 : V) R, ∫ v in Metric.closedBall x R, ψ v =
      ∫ x, ∫ v, (Metric.closedBall (0 : V) R ∩ Metric.closedBall v R).indicator
        (fun _ => ψ v) x := by
  set B := Metric.closedBall (0 : V) R
  trans ∫ x, B.indicator (fun x => ∫ v, (Metric.closedBall x R).indicator ψ v) x
  · rw [integral_indicator measurableSet_closedBall]
    congr 1
    funext x
    exact (integral_indicator measurableSet_closedBall).symm
  · congr 1
    funext x
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx]
      congr 1
      funext v
      rw [← indicator_closedBall_inter ψ R x v, Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      have hzero : (fun v => (B ∩ Metric.closedBall v R).indicator (fun _ => ψ v) x) = 0 :=
        funext fun v => Set.indicator_of_notMem (fun h => hx h.1) _
      rw [hzero]
      simp

/-- Fubini for the Fejér average: swapping the order of integration evaluates the inner integral
to the overlap volume. See Folland, *A Course in Abstract Harmonic Analysis*, §4.2. -/
private theorem fejer_fubini_eval (ψ : V → ℂ) (hcont : Continuous ψ) (R : ℝ) :
    ∫ x, ∫ v, (Metric.closedBall (0 : V) R ∩ Metric.closedBall v R).indicator
        (fun _ => ψ v) x =
      ∫ v, (volume (Metric.closedBall (0 : V) R ∩ Metric.closedBall v R)).toReal • ψ v := by
  rw [integral_integral_swap (integrable_indicator_prod ψ hcont R)]
  congr 1
  funext v
  rw [integral_indicator (measurableSet_closedBall.inter measurableSet_closedBall),
      setIntegral_const, measureReal_def]

/-- The Fubini identity: the normalized Fejér double integral equals `∫ ψ · overlapRatio`. -/
private theorem fejer_avg_eq_integral (ψ : V → ℂ) (hcont : Continuous ψ)
    (R : ℝ) (hR : 0 < R) :
    (volume (Metric.closedBall (0 : V) R)).toReal⁻¹ •
      ∫ x in Metric.closedBall (0 : V) R,
        ∫ y in Metric.closedBall (0 : V) R, ψ (x - y) =
    ∫ v, (overlapRatio R v : ℂ) * ψ v := by
  have hvol_ne : (volume (Metric.closedBall (0 : V) R)).toReal ≠ 0 :=
    ne_of_gt (ENNReal.toReal_pos (ne_of_gt (Metric.measure_closedBall_pos volume 0 hR))
      (ne_of_lt measure_closedBall_lt_top))
  rw [setIntegral_congr_fun measurableSet_closedBall
    (fun x _ => inner_integral_sub ψ x R)]
  rw [fejer_indicator_form ψ R, fejer_fubini_eval ψ hcont R]
  calc (volume (Metric.closedBall (0 : V) R)).toReal⁻¹ •
      ∫ v, (volume (Metric.closedBall (0 : V) R ∩ Metric.closedBall v R)).toReal • ψ v
    = ∫ v, (volume (Metric.closedBall (0 : V) R)).toReal⁻¹ •
        ((volume (Metric.closedBall (0 : V) R ∩ Metric.closedBall v R)).toReal • ψ v) :=
        (integral_smul _ _).symm
    _ = ∫ v, (overlapRatio R v : ℂ) * ψ v := by
        congr 1
        funext v
        rw [smul_comm, ← smul_assoc, Complex.real_smul]
        congr 1
        rw [Complex.ofReal_inj]
        rw [overlapRatio, ite_eq_right hvol_ne, div_eq_mul_inv, smul_eq_mul]

/-! ### Step C: the integral of a positive-definite function has nonnegative real part -/

/-- **The overlap-ratio weights converge to the integral.** For an integrable `ψ`, the integrals
of `ψ` against the weights `overlapRatio n` converge to `∫ ψ` as `n → ∞`. -/
private theorem tendsto_integral_overlapRatio_mul (ψ : V → ℂ) (hint : Integrable ψ) :
    Tendsto (fun n : ℕ => ∫ v, (overlapRatio (n : ℝ) v : ℂ) * ψ v) atTop (nhds (∫ x, ψ x)) := by
  have hone : (∫ x, ψ x) = ∫ x, (1 : ℂ) * ψ x := by simp
  rw [hone]
  apply tendsto_integral_of_dominated_convergence (fun v => ‖ψ v‖)
  · intro n
    exact (continuous_ofReal.measurable.comp
      (measurable_overlapRatio n)).aestronglyMeasurable.mul
      hint.aestronglyMeasurable
  · exact hint.norm
  · intro n
    filter_upwards with v
    rw [norm_mul, Complex.norm_real]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (abs_le.mpr ⟨by linarith [overlapRatio_nonneg (n : ℝ) v],
        overlapRatio_le_one (n : ℝ) v⟩)
  · filter_upwards with v
    have h2 : Tendsto (fun n : ℕ => (overlapRatio (n : ℝ) v : ℂ))
        atTop (nhds (1 : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 1).comp (overlapRatio_tendsto_one v)
    exact h2.mul tendsto_const_nhds

/-- For a continuous integrable positive-definite function `ψ`, the integral `∫ ψ` has
nonnegative real part: the Fejér-averaged double integral `J_R` converges to `∫ ψ` and has
nonnegative real part for each radius `R`. -/
private theorem pd_integral_re_nonneg (ψ : V → ℂ)
    (hpd : Matrix.PosSemidef fun a b : V => ψ (a - b))
    (hint : Integrable ψ) (hcont : Continuous ψ) :
    0 ≤ (∫ x, ψ x).re := by
  -- Define `J n = vol(B_n)⁻¹ • ∬_{B_n × B_n} ψ (x - y)`.
  set J : ℕ → ℂ := fun n =>
    if n = 0 then ψ 0
    else (volume (Metric.closedBall (0 : V) (n : ℝ))).toReal⁻¹ •
      ∫ x in Metric.closedBall (0 : V) (n : ℝ),
        ∫ y in Metric.closedBall (0 : V) (n : ℝ), ψ (x - y)
  -- `Re (J n) ≥ 0` for each `n`.
  have hnn : ∀ n : ℕ, 0 ≤ (J n).re := by
    intro n
    simp only [J]
    split_ifs with h
    · exact map_zero_re_nonneg_of_posSemidef hpd
    · rw [Complex.smul_re]
      apply mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
      exact pd_double_integral_re_nonneg ψ hpd hcont _ Metric.isBounded_closedBall
  -- `J n → ∫ ψ` via the Fubini identity and dominated convergence.
  have hconv : Tendsto J atTop (nhds (∫ x, ψ x)) := by
    suffices h : Tendsto
        (fun n : ℕ => ∫ v, (overlapRatio (n : ℝ) v : ℂ) * ψ v)
        atTop (nhds (∫ x, ψ x)) by
      apply h.congr'
      filter_upwards [Filter.eventually_ne_atTop 0] with n hn
      simp only [J, ite_eq_right hn]
      exact (fejer_avg_eq_integral ψ hcont n (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))).symm
    exact tendsto_integral_overlapRatio_mul ψ hint
  exact ge_of_tendsto' ((Complex.continuous_re.tendsto _).comp hconv) hnn

/-! ### The main theorems -/

/-- The Fourier transform of a continuous integrable positive-definite function on a
finite-dimensional real inner-product space has nonnegative real part.

Rudin, *Fourier Analysis on Groups*, Theorem 1.4.3; Folland, *A Course in Abstract Harmonic
Analysis*, §4.2, Lemma 4.8. -/
theorem fourier_re_nonneg_of_posSemidef (F : V → ℂ)
    (hpd : Matrix.PosSemidef fun a b : V => F (a - b))
    (hint : Integrable F) (hcont : Continuous F) (ξ : V) :
    0 ≤ (𝓕 F ξ).re := by
  -- Step 1: `𝓕 F ξ = ∫ v, fourierAtom ξ v * F v`.
  rw [fourier_eq_integral_fourierAtom_mul F ξ]
  -- Step 2: the twisted function is positive definite (Schur product with the Fourier atom).
  have hψ_pd : Matrix.PosSemidef
      fun a b : V => (fun v => fourierAtom ξ v * F v) (a - b) :=
    (posSemidef_fourierAtom ξ).hadamard hpd
  -- Step 3: the twisted function is continuous and integrable.
  have hψ_cont : Continuous fun v => fourierAtom ξ v * F v :=
    (continuous_fourierAtom ξ).mul hcont
  have hψ_int : Integrable fun v => fourierAtom ξ v * F v := by
    refine Integrable.mono hint hψ_cont.aestronglyMeasurable ?_
    filter_upwards with v
    rw [norm_mul, fourierAtom_eq_fourierChar, Circle.norm_coe, one_mul]
  -- Step 4: apply the Fejér average bound.
  exact pd_integral_re_nonneg _ hψ_pd hψ_int hψ_cont

/-- The Fourier transform of an integrable function whose subtraction kernel is positive definite,
on a finite-dimensional real inner-product space, has vanishing imaginary part — by Hermitian
symmetry and the negation invariance of Haar measure.

The argument never uses `_hint`, and the statement is provable without it: each step —
`Real.fourier_eq`, `integral_conj`, `integral_neg_eq_self` — is an equality that survives a
divergent integral, both sides then being the default value `0`. So requiring integrability is a
deliberate design choice, not a proof obligation. Without it `𝓕 F` is that default value rather
than the Fourier transform, so on a non-integrable conjugate-symmetric function such as `F = 1`
the conclusion degenerates to `(0 : ℂ).im = 0`; keeping those vacuous instances out of the public
API is worth the strength given up. Hence the hypothesis is bound as `_hint`.

Not a `@[simp]` lemma: neither side condition is dischargeable by `simp`'s discharger, so the
rule would be tried against every `(𝓕 _ _).im` and never fire. -/
theorem fourier_im_eq_zero_of_map_neg_eq_conj (F : V → ℂ)
    (hsymm : ∀ v : V, F (-v) = conj (F v)) (_hint : Integrable F) (ξ : V) :
    (𝓕 F ξ).im = 0 := by
  rw [fourier_eq_integral_fourierAtom_mul F ξ]
  have hconj : conj (∫ v, fourierAtom ξ v * F v) = ∫ v, fourierAtom ξ v * F v := by
    rw [← integral_conj]
    have hpt : ∀ v : V, conj (fourierAtom ξ v * F v) = fourierAtom ξ (-v) * F (-v) := by
      intro v
      rw [map_mul, ← hsymm v]
      congr 1
      rw [fourierAtom_eq_fourierChar, fourierAtom_eq_fourierChar,
        Circle.starRingEnd_addChar]
      simp [inner_neg_left]
    simp_rw [hpt]
    exact integral_neg_eq_self (fun v => fourierAtom ξ v * F v) volume
  have him := congrArg Complex.im hconj
  simp only [Complex.conj_im] at him
  linarith

/-- The Fourier transform of an integrable conjugate-symmetric function on a finite-dimensional
real inner-product space is real: it equals the coercion of its own real part.

As in `fourier_im_eq_zero_of_map_neg_eq_conj`, `hint` is a design choice rather than a proof
obligation — it is used only to discharge that lemma, which is itself provable without it. It is
required here so that the conclusion cannot be read off a divergent integral's default value. -/
theorem fourier_eq_re_of_map_neg_eq_conj (F : V → ℂ)
    (hsymm : ∀ v : V, F (-v) = conj (F v)) (hint : Integrable F) (ξ : V) :
    𝓕 F ξ = ((𝓕 F ξ).re : ℂ) := by
  refine Complex.ext (by simp) ?_
  simp [fourier_im_eq_zero_of_map_neg_eq_conj F hsymm hint ξ]

/-- The positive-definite specialization of `fourier_im_eq_zero_of_map_neg_eq_conj`: a function
with positive-definite subtraction kernel is conjugate-symmetric. -/
theorem fourier_im_eq_zero_of_posSemidef (F : V → ℂ)
    (hpd : Matrix.PosSemidef fun a b : V => F (a - b)) (hint : Integrable F) (ξ : V) :
    (𝓕 F ξ).im = 0 :=
  fourier_im_eq_zero_of_map_neg_eq_conj F (map_neg_eq_conj_of_posSemidef hpd) hint ξ

/-- The positive-definite specialization of `fourier_eq_re_of_map_neg_eq_conj`. -/
theorem fourier_eq_re_of_posSemidef (F : V → ℂ)
    (hpd : Matrix.PosSemidef fun a b : V => F (a - b)) (hint : Integrable F) (ξ : V) :
    𝓕 F ξ = ((𝓕 F ξ).re : ℂ) :=
  fourier_eq_re_of_map_neg_eq_conj F (map_neg_eq_conj_of_posSemidef hpd) hint ξ

/-! ### Integrability of the Fourier transform of a positive-definite function -/

/-- The Fourier transform of a Gaussian is integrable (it is again a Gaussian). -/
private theorem integrable_fourierIntegral_gaussian {t : ℝ} (ht : 0 < t) :
    Integrable (𝓕 fun ξ : V => Complex.exp (-(t * ‖ξ‖ ^ 2 : ℝ))) := by
  have htre : 0 < ((t : ℂ)).re := by simpa using ht
  have heq : (fun ξ : V => Complex.exp (-(t * ‖ξ‖ ^ 2 : ℝ)))
      = fun v : V => Complex.exp (-(t : ℂ) * (‖v‖ : ℂ) ^ 2) := by
    funext v
    push_cast
    ring_nf
  rw [heq, funext fun w : V => fourier_gaussian_innerProductSpace htre w]
  refine Integrable.const_mul ?_ _
  have hint : Integrable fun w : V => Complex.exp (-(Real.pi ^ 2 / t * ‖w‖ ^ 2 : ℝ)) :=
    integrable_cexp_neg_mul_sq_norm (by positivity)
  refine hint.congr (ae_of_all _ fun w => ?_)
  push_cast
  ring_nf

/-- The Fourier transform of a Gaussian integrates to `1`, by Fourier inversion at `0`. -/
private theorem integral_fourierIntegral_gaussian_eq_one {t : ℝ} (ht : 0 < t) :
    ∫ ξ : V, 𝓕 (fun x : V => Complex.exp (-(t * ‖x‖ ^ 2 : ℝ))) ξ = 1 := by
  have hg_int : Integrable fun x : V => Complex.exp (-(t * ‖x‖ ^ 2 : ℝ)) :=
    integrable_cexp_neg_mul_sq_norm ht
  have hg_cont : Continuous fun x : V => Complex.exp (-(t * ‖x‖ ^ 2 : ℝ)) :=
    continuous_cexp_neg_mul_sq_norm t
  have hft_int := integrable_fourierIntegral_gaussian (V := V) ht
  have h0 := congrFun (hg_cont.fourierInv_fourier_eq hg_int hft_int) 0
  rw [Real.fourierInv_eq] at h0
  simp only [inner_zero_right, AddChar.map_zero_eq_one, one_smul, norm_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, neg_zero, Complex.ofReal_zero,
    Complex.exp_zero] at h0
  exact h0

/-- The `L¹` norm of the Fourier transform of a Gaussian is `1`: the transform is real and
nonnegative because the Gaussian has a positive-definite subtraction kernel. -/
private theorem integral_norm_fourierIntegral_gaussian_eq_one {t : ℝ} (ht : 0 < t) :
    ∫ ξ : V, ‖𝓕 (fun x : V => Complex.exp (-(t * ‖x‖ ^ 2 : ℝ))) ξ‖ = 1 := by
  have hg_pd : Matrix.PosSemidef
      fun a b : V => Complex.exp (-(t * ‖a - b‖ ^ 2 : ℝ)) :=
    posSemidef_cexp_neg_mul_sq_norm ht.le
  have hg_int : Integrable fun x : V => Complex.exp (-(t * ‖x‖ ^ 2 : ℝ)) :=
    integrable_cexp_neg_mul_sq_norm ht
  have hg_cont : Continuous fun x : V => Complex.exp (-(t * ‖x‖ ^ 2 : ℝ)) :=
    continuous_cexp_neg_mul_sq_norm t
  have hft_int := integrable_fourierIntegral_gaussian (V := V) ht
  have hnorm : ∀ ξ : V, ‖𝓕 (fun x : V => Complex.exp (-(t * ‖x‖ ^ 2 : ℝ))) ξ‖ =
      (𝓕 (fun x : V => Complex.exp (-(t * ‖x‖ ^ 2 : ℝ))) ξ).re := by
    intro ξ
    have hre := fourier_re_nonneg_of_posSemidef _ hg_pd hg_int hg_cont ξ
    rw [fourier_eq_re_of_posSemidef _ hg_pd hg_int ξ, Complex.norm_real,
      Complex.ofReal_re, Real.norm_of_nonneg hre]
  calc ∫ ξ : V, ‖𝓕 (fun x : V => Complex.exp (-(t * ‖x‖ ^ 2 : ℝ))) ξ‖
      = ∫ ξ : V, (𝓕 (fun x : V => Complex.exp (-(t * ‖x‖ ^ 2 : ℝ))) ξ).re :=
        integral_congr_ae (ae_of_all _ hnorm)
    _ = (∫ ξ : V, 𝓕 (fun x : V => Complex.exp (-(t * ‖x‖ ^ 2 : ℝ))) ξ).re := by
        simpa only [RCLike.re_to_complex] using integral_re hft_int
    _ = 1 := by rw [integral_fourierIntegral_gaussian_eq_one ht, Complex.one_re]

/-- For a continuous integrable positive-definite `F` and `t > 0`, the Gaussian-tested integral
of `𝓕 F` is at most `(F 0).re`, by the Parseval/Fubini identity and the `L¹` bound on the
Fourier transform of the Gaussian. -/
private theorem re_integral_fourierIntegral_mul_gaussian_le (F : V → ℂ)
    (hpd : Matrix.PosSemidef fun a b : V => F (a - b))
    (hint : Integrable F) (hcont : Continuous F) {t : ℝ} (ht : 0 < t) :
    (∫ ξ, 𝓕 F ξ * Complex.exp (-(t * ‖ξ‖ ^ 2 : ℝ))).re ≤ (F 0).re := by
  have hgt_int : Integrable fun ξ : V => Complex.exp (-(t * ‖ξ‖ ^ 2 : ℝ)) :=
    integrable_cexp_neg_mul_sq_norm ht
  have hft_gt_int := integrable_fourierIntegral_gaussian (V := V) ht
  have hFbound : ∀ x, ‖F x‖ ≤ (F 0).re := norm_apply_le_map_zero_re_of_posSemidef hpd
  have hprod_int : Integrable fun x : V =>
      F x * 𝓕 (fun ξ : V => Complex.exp (-(t * ‖ξ‖ ^ 2 : ℝ))) x :=
    hft_gt_int.bdd_mul hcont.aestronglyMeasurable (ae_of_all _ hFbound)
  -- The `L¹` Parseval identity, from `integral_fourierIntegral_smul_eq_flip` with the
  -- symmetric pairing `innerₗ`.
  have hbridge : ∀ (f : V → ℂ) (ξ : V),
      VectorFourier.fourierIntegral 𝐞 volume (innerₗ V) f ξ = 𝓕 f ξ := fun f ξ => by
    rw [Real.fourier_eq]
    simp only [VectorFourier.fourierIntegral, innerₗ_apply_apply]
  have hpars : (∫ ξ, 𝓕 F ξ * Complex.exp (-(t * ‖ξ‖ ^ 2 : ℝ))) =
      ∫ x, F x * 𝓕 (fun ξ : V => Complex.exp (-(t * ‖ξ‖ ^ 2 : ℝ))) x := by
    have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ V)
      Real.continuous_fourierChar
      (by simpa only [innerₗ_apply_apply] using continuous_inner :
        Continuous fun p : V × V => (innerₗ V) p.1 p.2) hint hgt_int
    simpa only [flip_innerₗ, smul_eq_mul, hbridge] using h
  rw [hpars]
  calc (∫ x, F x * 𝓕 (fun ξ : V => Complex.exp (-(t * ‖ξ‖ ^ 2 : ℝ))) x).re
      ≤ ‖∫ x, F x * 𝓕 (fun ξ : V => Complex.exp (-(t * ‖ξ‖ ^ 2 : ℝ))) x‖ :=
        Complex.re_le_norm _
    _ ≤ ∫ x, ‖F x * 𝓕 (fun ξ : V => Complex.exp (-(t * ‖ξ‖ ^ 2 : ℝ))) x‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ x, (F 0).re * ‖𝓕 (fun ξ : V => Complex.exp (-(t * ‖ξ‖ ^ 2 : ℝ))) x‖ := by
        refine integral_mono hprod_int.norm ((hft_gt_int.norm).const_mul _) fun x => ?_
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hFbound x) (norm_nonneg _)
    _ = (F 0).re * ∫ x, ‖𝓕 (fun ξ : V => Complex.exp (-(t * ‖ξ‖ ^ 2 : ℝ))) x‖ :=
        integral_const_mul _ _
    _ = (F 0).re := by rw [integral_norm_fourierIntegral_gaussian_eq_one ht, mul_one]

/-- The Gaussian-damped lower integral of `‖𝓕 F‖ₑ` is bounded by `(F 0).re`, uniformly in the
damping parameter: the damped transform is real and nonnegative, so its `L¹` norm equals the
Gaussian-tested integral bounded by `re_integral_fourierIntegral_mul_gaussian_le`. -/
private theorem lintegral_enorm_fourierIntegral_mul_gaussian_le (F : V → ℂ)
    (hpd : Matrix.PosSemidef fun a b : V => F (a - b))
    (hint : Integrable F) (hcont : Continuous F) {t : ℝ} (ht : 0 < t) :
    ∫⁻ ξ, ‖𝓕 F ξ * Complex.exp (-(t * ‖ξ‖ ^ 2 : ℝ))‖ₑ ≤ ENNReal.ofReal (F 0).re := by
  have hbound : ∀ ξ : V, ‖𝓕 F ξ‖ ≤ ∫ x, ‖F x‖ := fun ξ =>
    VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 volume (innerₗ V) F ξ
  have hft_cont : Continuous (𝓕 F) := continuous_fourier_of_integrable hint
  have hprod_int : Integrable fun ξ : V => 𝓕 F ξ * Complex.exp (-(t * ‖ξ‖ ^ 2 : ℝ)) :=
    (integrable_cexp_neg_mul_sq_norm ht).bdd_mul hft_cont.aestronglyMeasurable
      (ae_of_all _ fun ξ => hbound ξ)
  rw [← ofReal_integral_norm_eq_lintegral_enorm hprod_int]
  refine ENNReal.ofReal_le_ofReal ?_
  have hnorm_eq : ∀ ξ : V, ‖𝓕 F ξ * Complex.exp (-(t * ‖ξ‖ ^ 2 : ℝ))‖ =
      (𝓕 F ξ * Complex.exp (-(t * ‖ξ‖ ^ 2 : ℝ))).re := by
    intro ξ
    rw [fourier_eq_re_of_posSemidef F hpd hint ξ, ← Complex.ofReal_neg,
      ← Complex.ofReal_exp, ← Complex.ofReal_mul, Complex.norm_real, Complex.ofReal_re,
      Real.norm_of_nonneg (mul_nonneg
        (fourier_re_nonneg_of_posSemidef F hpd hint hcont ξ)
        (Real.exp_nonneg _))]
  calc ∫ ξ, ‖𝓕 F ξ * Complex.exp (-(t * ‖ξ‖ ^ 2 : ℝ))‖
      = ∫ ξ, (𝓕 F ξ * Complex.exp (-(t * ‖ξ‖ ^ 2 : ℝ))).re :=
        integral_congr_ae (ae_of_all _ hnorm_eq)
    _ = (∫ ξ, 𝓕 F ξ * Complex.exp (-(t * ‖ξ‖ ^ 2 : ℝ))).re := by
        simpa only [RCLike.re_to_complex] using integral_re hprod_int
    _ ≤ (F 0).re := re_integral_fourierIntegral_mul_gaussian_le F hpd hint hcont ht

/-- The Fourier transform of a continuous integrable positive-definite function is integrable.

Testing `𝓕 F` against the Gaussians `exp (-‖·‖²/(n+1))` gives integrals uniformly bounded by
`(F 0).re`, and Fatou's lemma passes the bound to `∫⁻ ‖𝓕 F‖ₑ`. Folland, *A Course in Abstract
Harmonic Analysis*, §4.2. -/
theorem integrable_fourier_of_posSemidef (F : V → ℂ)
    (hpd : Matrix.PosSemidef fun a b : V => F (a - b))
    (hint : Integrable F) (hcont : Continuous F) :
    Integrable (𝓕 F) := by
  have hft_cont : Continuous (𝓕 F) := continuous_fourier_of_integrable hint
  set tn : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with htn_def
  have htn_pos : ∀ n, 0 < tn n := fun n => by positivity
  have htn_lim : Tendsto tn atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hf_meas : ∀ n : ℕ, Measurable fun ξ : V =>
      ‖𝓕 F ξ * Complex.exp (-(tn n * ‖ξ‖ ^ 2 : ℝ))‖ₑ := fun n =>
    ((hft_cont.mul (continuous_cexp_neg_mul_sq_norm (tn n))).measurable).enorm
  have hf_tendsto : ∀ ξ : V, Tendsto
      (fun n : ℕ => ‖𝓕 F ξ * Complex.exp (-(tn n * ‖ξ‖ ^ 2 : ℝ))‖ₑ)
      atTop (𝓝 ‖𝓕 F ξ‖ₑ) := by
    intro ξ
    have h2 : Tendsto (fun n : ℕ => Complex.exp (-(tn n * ‖ξ‖ ^ 2 : ℝ))) atTop (𝓝 1) :=
      (tendsto_cexp_neg_mul_sq_norm ξ).comp htn_lim
    have h3 : Tendsto (fun n : ℕ => 𝓕 F ξ * Complex.exp (-(tn n * ‖ξ‖ ^ 2 : ℝ)))
        atTop (𝓝 (𝓕 F ξ)) := by
      simpa using tendsto_const_nhds.mul h2
    exact h3.enorm
  have hbound : ∫⁻ ξ, ‖𝓕 F ξ‖ₑ ≤ ENNReal.ofReal (F 0).re := by
    calc ∫⁻ ξ, ‖𝓕 F ξ‖ₑ
        = ∫⁻ ξ, liminf
            (fun n : ℕ => ‖𝓕 F ξ * Complex.exp (-(tn n * ‖ξ‖ ^ 2 : ℝ))‖ₑ) atTop :=
          lintegral_congr fun ξ => ((hf_tendsto ξ).liminf_eq).symm
      _ ≤ liminf
            (fun n : ℕ => ∫⁻ ξ, ‖𝓕 F ξ * Complex.exp (-(tn n * ‖ξ‖ ^ 2 : ℝ))‖ₑ) atTop :=
          lintegral_liminf_le hf_meas
      _ ≤ ENNReal.ofReal (F 0).re := by
          apply liminf_le_of_le (h := fun b hb => ?_)
          obtain ⟨n, hn⟩ := hb.exists
          exact hn.trans
            (lintegral_enorm_fourierIntegral_mul_gaussian_le F hpd hint hcont (htn_pos n))
  exact ⟨hft_cont.aestronglyMeasurable, hbound.trans_lt ENNReal.ofReal_lt_top⟩

/-! ### The inverse transform

The inverse Fourier transform `𝓕⁻ F = 𝓕 F ∘ (-·)` is the density of the representing measure of
Bochner's theorem, so nonnegativity, realness and integrability are recorded for it too. -/

/-- The inverse Fourier transform of a continuous integrable positive-definite function has
nonnegative real part. -/
theorem fourierInv_re_nonneg_of_posSemidef (F : V → ℂ)
    (hpd : Matrix.PosSemidef fun a b : V => F (a - b))
    (hint : Integrable F) (hcont : Continuous F) (ξ : V) :
    0 ≤ (𝓕⁻ F ξ).re := by
  rw [Real.fourierInv_eq_fourier_neg]
  exact fourier_re_nonneg_of_posSemidef F hpd hint hcont (-ξ)

/-- The inverse Fourier transform of an integrable conjugate-symmetric function is real: it
equals the coercion of its own real part. As in `fourier_im_eq_zero_of_map_neg_eq_conj`, `hint`
is a design choice rather than a proof obligation: it keeps the statement from being read off the
default value of a divergent integral. -/
theorem fourierInv_eq_re_of_map_neg_eq_conj (F : V → ℂ)
    (hsymm : ∀ v : V, F (-v) = conj (F v)) (hint : Integrable F) (ξ : V) :
    𝓕⁻ F ξ = ((𝓕⁻ F ξ).re : ℂ) := by
  rw [Real.fourierInv_eq_fourier_neg]
  exact fourier_eq_re_of_map_neg_eq_conj F hsymm hint (-ξ)

/-- The positive-definite specialization of `fourierInv_eq_re_of_map_neg_eq_conj`. -/
theorem fourierInv_eq_re_of_posSemidef (F : V → ℂ)
    (hpd : Matrix.PosSemidef fun a b : V => F (a - b)) (hint : Integrable F) (ξ : V) :
    𝓕⁻ F ξ = ((𝓕⁻ F ξ).re : ℂ) :=
  fourierInv_eq_re_of_map_neg_eq_conj F (map_neg_eq_conj_of_posSemidef hpd) hint ξ

/-- The inverse Fourier transform of a continuous integrable positive-definite function is
integrable. -/
theorem integrable_fourierInv_of_posSemidef (F : V → ℂ)
    (hpd : Matrix.PosSemidef fun a b : V => F (a - b))
    (hint : Integrable F) (hcont : Continuous F) :
    Integrable (𝓕⁻ F) := by
  rw [funext fun ξ => Real.fourierInv_eq_fourier_neg F ξ]
  exact (integrable_fourier_of_posSemidef F hpd hint hcont).comp_neg

/-- The `ℝ≥0∞`-valued density `(𝓕⁻ F).re` of the Bochner representing measure is measurable
whenever `F` is integrable. -/
theorem measurable_ofReal_re_fourierInv {F : V → ℂ} (hint : Integrable F) :
    Measurable fun ξ : V => ENNReal.ofReal (𝓕⁻ F ξ).re :=
  ENNReal.measurable_ofReal.comp
    (Complex.measurable_re.comp (continuous_fourierInv_of_integrable hint).measurable)

end TauCeti

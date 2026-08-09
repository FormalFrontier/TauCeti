/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.WithDensity
public import TauCeti.Analysis.PositiveDefinite.FourierAtom
public import TauCeti.Analysis.PositiveDefinite.Function.Kernel
-- The remaining imports are proof-only: Fourier inversion, the negation invariance of Haar
-- measure, the `withDensity` Bochner-integral formula, the characteristic-function API and its
-- uniqueness theorem, the Lévy continuity theorem, Prokhorov's theorem with the Lévy–Prokhorov
-- metrizability of the space of probability measures, sequential compactness, the
-- Fourier-convention bridge, the nonnegativity and integrability of the Fourier transform of a
-- positive-definite function, the Gaussian regularization, and the kernel Cauchy–Schwarz
-- bounds.
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.Sequences
import TauCeti.Analysis.Bochner.Fourier.Convention
import TauCeti.Analysis.Bochner.Fourier.Nonneg
import TauCeti.Analysis.Bochner.Gaussian.Regularization
import TauCeti.Analysis.PositiveDefinite.Kernel.Bounds

/-!
# Bochner's theorem

A continuous function `F : V → ℂ` on a finite-dimensional real inner-product space has a
positive-definite subtraction kernel `(a, b) ↦ F (a - b)` if and only if it is the
Fourier-convention transform `v ↦ ∫ q, fourierAtom v q ∂μ` of a unique finite Borel measure `μ`
on `V`. This file assembles the final statement from the two analytic predecessors.

The `L¹` case comes first: for a continuous *integrable* positive-definite `F`, the finite
measure with density `(𝓕⁻ F).re` against Lebesgue measure recovers `F` as the
Fourier-convention transform `∫ q, fourierAtom · q` of the measure, by Fourier inversion; this
is the representing measure of Bochner's theorem, given explicitly.

Existence is proved by Gaussian regularization and a compactness argument. If `F 0 = 0` the
kernel Cauchy–Schwarz inequality forces `F = 0` and the zero measure represents. Otherwise,
after normalizing to `G 0 = 1`, the regularizations `G_n = G · exp (-‖·‖²/(n+1))` are
integrable positive-definite functions, each represented by an explicit probability measure
`ν_n` with density `(𝓕⁻ G_n).re` (`integral_fourierAtom_withDensity_re_fourierInv`).
The characteristic functions of the `ν_n` converge pointwise to a rescaling of `G`, which is
continuous at `0`, so the family is tight by the Lévy continuity theorem; Prokhorov's theorem
and the metrizability of the space of probability measures extract a weakly convergent
subsequence, whose limit represents `G` by passing to the limit in the characteristic
functions. Uniqueness reduces to Mathlib's `MeasureTheory.Measure.ext_of_charFun` through the
`-2π` rescaling of `integral_fourierAtom_eq_charFun_neg_two_pi_smul`.

Adapted from the Bochner–Minlos formalization (`Bochner/Main.lean` in our bochner project);
the positive-definiteness hypotheses are restated through `TauCeti.IsPositiveDefiniteKernel`,
and the representation is stated in the `fourierAtom` convention rather than through
`MeasureTheory.charFun`.

## Main declarations

* `TauCeti.isFiniteMeasure_withDensity_re_fourierInv` and
  `TauCeti.integral_fourierAtom_withDensity_re_fourierInv`: the measure
  `volume.withDensity (ENNReal.ofReal (𝓕⁻ F ·).re)` is finite and recovers `F` through the
  Fourier atom — the `L¹` case of Bochner's theorem.
* `TauCeti.exists_isFiniteMeasure_integral_fourierAtom_eq_of_isPositiveDefiniteKernel`:
  existence of a finite representing measure for a continuous positive-definite function.
* `TauCeti.Measure.ext_of_forall_integral_fourierAtom_eq`: uniqueness of the representing
  measure.
* `TauCeti.bochner`: **Bochner's theorem**, the equivalence between positive definiteness of
  the subtraction kernel and the unique Fourier representation.
* `TauCeti.bochner_of_forall_star_eq_neg`: the same equivalence for the involutive
  positive-definiteness predicate under the negation involution.

## References

* S. Bochner, *Vorlesungen über Fouriersche Integrale*, Akademische Verlagsgesellschaft (1932).
* W. Rudin, *Fourier Analysis on Groups* (1962), Theorem 1.4.3.
* Roadmap: TauCetiRoadmap/OneParameterSemigroups/README.md, Part C (Bochner milestone).
-/

public section

open Filter MeasureTheory
open scoped ComplexOrder FourierTransform Topology

namespace TauCeti

/-- The scaling constant `-2π` of the Fourier convention is nonzero. -/
private theorem neg_two_pi_ne_zero : (-2 * Real.pi) ≠ 0 :=
  mul_ne_zero (by norm_num) Real.pi_ne_zero

/-! ### Uniqueness of the representing measure -/

section Uniqueness

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  [BorelSpace V] [SecondCountableTopology V] [CompleteSpace V]

/-- **Uniqueness half of Bochner's theorem.** Two finite Borel measures with the same
Fourier-convention transform coincide; this is Mathlib's characteristic-function uniqueness
theorem, transported through the `-2π` rescaling. Stated on any complete second-countable real
inner-product space; no finite-dimensionality is needed. -/
theorem Measure.ext_of_forall_integral_fourierAtom_eq {μ ν : Measure V}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ v, ∫ q, fourierAtom v q ∂μ = ∫ q, fourierAtom v q ∂ν) : μ = ν := by
  refine MeasureTheory.Measure.ext_of_charFun (funext fun t => ?_)
  have h' := h ((-2 * Real.pi)⁻¹ • t)
  rwa [integral_fourierAtom_eq_charFun_neg_two_pi_smul,
    integral_fourierAtom_eq_charFun_neg_two_pi_smul, smul_smul,
    mul_inv_cancel₀ neg_two_pi_ne_zero, one_smul] at h'

end Uniqueness

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-! ### The L¹ representing measure -/

/-- The measure with density `(𝓕⁻ F).re` against Lebesgue measure is finite whenever `𝓕 F` is
integrable. This is the total-mass half of the `L¹` case of Bochner's theorem. -/
theorem isFiniteMeasure_withDensity_re_fourierInv (F : V → ℂ)
    (hint_ft : Integrable (𝓕 F)) :
    IsFiniteMeasure (volume.withDensity fun ξ => ENNReal.ofReal (𝓕⁻ F ξ).re) := by
  have hinv_int : Integrable (𝓕⁻ F) := by
    rw [show 𝓕⁻ F = fun ξ : V => 𝓕 F (-ξ) from
      funext fun ξ => Real.fourierInv_eq_fourier_neg F ξ]
    exact hint_ft.comp_neg
  exact isFiniteMeasure_withDensity_ofReal hinv_int.re.2

/-- **Bochner recovery for `L¹` positive-definite functions.** A continuous integrable function
`F` with positive-definite subtraction kernel is the Fourier-convention transform
`v ↦ ∫ q, fourierAtom v q ∂μ` of the finite measure `μ` with density `(𝓕⁻ F).re` against
Lebesgue measure. The identity is Fourier inversion `𝓕 (𝓕⁻ F) = F`, using that `𝓕⁻ F` is real
and nonnegative. Rudin, *Fourier Analysis on Groups*, §1.4; Folland, §4.2. -/
theorem integral_fourierAtom_withDensity_re_fourierInv (F : V → ℂ)
    (hpd : IsPositiveDefiniteKernel fun a b : V => F (a - b))
    (hint : Integrable F) (hcont : Continuous F) (v : V) :
    ∫ q, fourierAtom v q ∂(volume.withDensity fun ξ => ENNReal.ofReal (𝓕⁻ F ξ).re) = F v := by
  have hft_int : Integrable (𝓕 F) :=
    integrable_fourierIntegral_of_isPositiveDefiniteKernel F hpd hint hcont
  have hinv_cont : Continuous (𝓕⁻ F) := by
    rw [show 𝓕⁻ F = fun ξ : V => 𝓕 F (-ξ) from
      funext fun ξ => Real.fourierInv_eq_fourier_neg F ξ]
    exact (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (by simpa only [innerₗ_apply_apply] using continuous_inner) hint).comp continuous_neg
  have hre : ∀ ξ, 0 ≤ (𝓕⁻ F ξ).re := fun ξ => by
    rw [Real.fourierInv_eq_fourier_neg]
    exact fourierIntegral_re_nonneg_of_isPositiveDefiniteKernel F hpd hint hcont (-ξ)
  have hreal : ∀ ξ, 𝓕⁻ F ξ = ((𝓕⁻ F ξ).re : ℂ) := fun ξ => by
    rw [Real.fourierInv_eq_fourier_neg]
    exact fourierIntegral_eq_re_of_isPositiveDefiniteKernel F hpd (-ξ)
  have hmeas : Measurable fun ξ : V => ENNReal.ofReal (𝓕⁻ F ξ).re :=
    ENNReal.measurable_ofReal.comp (Complex.measurable_re.comp hinv_cont.measurable)
  rw [integral_withDensity_eq_integral_toReal_smul₀ hmeas.aemeasurable
    (ae_of_all _ fun ξ => ENNReal.ofReal_lt_top) _]
  calc ∫ q, (ENNReal.ofReal (𝓕⁻ F q).re).toReal • fourierAtom v q
      = ∫ q, fourierAtom v q * 𝓕⁻ F q := by
        refine integral_congr_ae (ae_of_all _ fun q => ?_)
        simp only [ENNReal.toReal_ofReal (hre q), Complex.real_smul]
        rw [← hreal q, mul_comm]
    _ = 𝓕 (𝓕⁻ F) v := (fourierIntegral_eq_integral_fourierAtom_mul (𝓕⁻ F) v).symm
    _ = F v := by rw [hcont.fourier_fourierInv_eq hint hft_int]

/-! ### The normalized existence argument -/

/-- **Existence, normalized case.** A continuous function `G` with positive-definite
subtraction kernel and `G 0 = 1` is the Fourier-convention transform of a probability
measure: Gaussian regularization, tightness via Lévy continuity, and Prokhorov compactness. -/
private theorem exists_probabilityMeasure_integral_fourierAtom_eq {G : V → ℂ}
    (hpd : IsPositiveDefiniteKernel fun a b : V => G (a - b))
    (hcont : Continuous G) (hG0 : G 0 = 1) :
    ∃ μ : Measure V, IsProbabilityMeasure μ ∧ ∀ v, ∫ q, fourierAtom v q ∂μ = G v := by
  -- the regularization parameters `ε n → 0⁺`
  set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε_pos : ∀ n, 0 < ε n := fun n => by positivity
  have hε_lim : Tendsto ε atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨tendsto_one_div_add_atTop_nhds_zero_nat, .of_forall fun n => Set.mem_Ioi.mpr (hε_pos n)⟩
  -- the explicit representing measures of the regularizations
  set ν : ℕ → Measure V := fun n =>
    volume.withDensity fun ξ => ENNReal.ofReal (𝓕⁻ (gaussianRegularize G (ε n)) ξ).re
  have hGn_pd : ∀ n, IsPositiveDefiniteKernel
      fun a b : V => gaussianRegularize G (ε n) (a - b) := fun n =>
    isPositiveDefiniteKernel_gaussianRegularize hpd (hε_pos n).le
  have hν_rep : ∀ n v, ∫ q, fourierAtom v q ∂(ν n) = gaussianRegularize G (ε n) v := fun n v =>
    integral_fourierAtom_withDensity_re_fourierInv _ (hGn_pd n)
      (integrable_gaussianRegularize hpd hcont (hε_pos n))
      (continuous_gaussianRegularize hcont (ε n)) v
  have hν_prob : ∀ n, IsProbabilityMeasure (ν n) := by
    intro n
    have : IsFiniteMeasure (ν n) := isFiniteMeasure_withDensity_re_fourierInv _
      (integrable_fourierIntegral_gaussianRegularize hpd hcont (hε_pos n))
    have h0 := hν_rep n 0
    simp only [gaussianRegularize_apply, hG0, one_mul, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, mul_zero, neg_zero, Complex.ofReal_zero,
      Complex.exp_zero] at h0
    simp only [fourierAtom_apply, inner_zero_right, Complex.ofReal_zero, mul_zero,
      Complex.exp_zero, integral_const, Complex.real_smul, mul_one,
      Complex.ofReal_eq_one] at h0
    exact isProbabilityMeasure_iff_real.mpr h0
  -- the pointwise limit of the characteristic functions
  set f : V → ℂ := fun t => G ((-2 * Real.pi)⁻¹ • t) with hf_def
  have hchar : ∀ n t, charFun (ν n) t =
      gaussianRegularize G (ε n) ((-2 * Real.pi)⁻¹ • t) := by
    intro n t
    have h := integral_fourierAtom_eq_charFun_neg_two_pi_smul (μ := ν n)
      ((-2 * Real.pi)⁻¹ • t)
    rw [hν_rep n, smul_smul, mul_inv_cancel₀ neg_two_pi_ne_zero, one_smul] at h
    exact h.symm
  have hconv : ∀ t, Tendsto (fun n => charFun (ν n) t) atTop (𝓝 (f t)) := by
    intro t
    simp only [hchar]
    exact (tendsto_gaussianRegularize G ((-2 * Real.pi)⁻¹ • t)).comp hε_lim
  -- tightness, Prokhorov compactness, and a weakly convergent subsequence
  have hf_cont : ContinuousAt f 0 := (hcont.comp (continuous_const_smul _)).continuousAt
  have htight : IsTightMeasureSet (Set.range ν) :=
    isTightMeasureSet_of_tendsto_charFun hf_cont hconv
  set P : ℕ → ProbabilityMeasure V := fun n => ⟨ν n, hν_prob n⟩
  have hcompact : IsCompact (closure (Set.range P)) := by
    apply isCompact_closure_of_isTightMeasureSet
    convert htight using 1
    ext m
    constructor
    · rintro ⟨p, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨P n, ⟨n, rfl⟩, rfl⟩
  obtain ⟨μ₀, -, φ, hφ, hlim⟩ :=
    hcompact.tendsto_subseq fun n => subset_closure (Set.mem_range_self n)
  -- identify the characteristic function of the limit
  have hsub := ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hlim
  have hcharlim : ∀ t, charFun (μ₀ : Measure V) t = f t := fun t =>
    tendsto_nhds_unique (hsub t) ((hconv t).comp hφ.tendsto_atTop)
  refine ⟨(μ₀ : Measure V), μ₀.prop, fun v => ?_⟩
  rw [integral_fourierAtom_eq_charFun_neg_two_pi_smul, hcharlim]
  simp only [hf_def]
  rw [smul_smul, inv_mul_cancel₀ neg_two_pi_ne_zero, one_smul]

/-! ### Bochner's theorem -/

/-- **Existence half of Bochner's theorem.** A continuous function `F` on a finite-dimensional
real inner-product space whose subtraction kernel `(a, b) ↦ F (a - b)` is positive definite is
the Fourier-convention transform `v ↦ ∫ q, fourierAtom v q ∂μ` of a finite Borel measure `μ`.
Rudin, *Fourier Analysis on Groups*, Theorem 1.4.3. -/
theorem exists_isFiniteMeasure_integral_fourierAtom_eq_of_isPositiveDefiniteKernel
    (F : V → ℂ) (hcont : Continuous F)
    (hpd : IsPositiveDefiniteKernel fun a b : V => F (a - b)) :
    ∃ μ : Measure V, IsFiniteMeasure μ ∧ ∀ v, F v = ∫ q, fourierAtom v q ∂μ := by
  have h0re : 0 ≤ (F 0).re :=
    (Complex.nonneg_iff.mp (by simpa using isPositiveDefiniteKernel_apply_self_nonneg hpd 0)).1
  have h0eq : F 0 = ((F 0).re : ℂ) := by
    have h0 : (0 : ℂ) ≤ F 0 := by
      simpa using isPositiveDefiniteKernel_apply_self_nonneg hpd 0
    exact Complex.ext (by simp) (by simp [← (Complex.nonneg_iff.mp h0).2])
  rcases h0re.eq_or_lt with hzero | hpos
  · -- degenerate case: `F 0 = 0` forces `F = 0`, represented by the zero measure
    have hF0 : F 0 = 0 := by rw [h0eq, ← hzero, Complex.ofReal_zero]
    exact ⟨0, inferInstance, fun v => by
      simp [show F v = 0 by
        simpa using isPositiveDefiniteKernel_eq_zero_of_apply_self_eq_zero_right hpd
          (a := v) (b := (0 : V)) (by simpa using hF0)]⟩
  · -- main case: normalize to value `1` at the origin and scale the measure back
    set c : ℝ := (F 0).re
    have hcne : (c : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    set G : V → ℂ := fun v => (c : ℂ)⁻¹ * F v with hG_def
    have hG_pd : IsPositiveDefiniteKernel fun a b : V => G (a - b) := by
      have h := isPositiveDefiniteKernel_smul_of_nonneg (K := fun a b : V => F (a - b))
        (c := ((c : ℂ))⁻¹)
        (inv_nonneg.mpr ((RCLike.ofReal_nonneg (K := ℂ)).mpr hpos.le)) hpd
      simpa only [smul_eq_mul] using h
    have hG_cont : Continuous G := continuous_const.mul hcont
    have hG0 : G 0 = 1 := by
      rw [hG_def]
      simp only [h0eq]
      exact inv_mul_cancel₀ hcne
    obtain ⟨μ, hμ_prob, hμ_rep⟩ :=
      exists_probabilityMeasure_integral_fourierAtom_eq hG_pd hG_cont hG0
    refine ⟨ENNReal.ofReal c • μ, ⟨?_⟩, fun v => ?_⟩
    · rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ _)
    · rw [integral_smul_measure, ENNReal.toReal_ofReal hpos.le, hμ_rep v, hG_def,
        Complex.real_smul, ← mul_assoc, mul_inv_cancel₀ hcne, one_mul]

/-- **Bochner's theorem.** A continuous function `F` on a finite-dimensional real inner-product
space has a positive-definite subtraction kernel `(a, b) ↦ F (a - b)` if and only if it is the
Fourier-convention transform `v ↦ ∫ q, fourierAtom v q ∂μ` of a unique finite Borel measure
`μ`. Bochner (1932); Rudin, *Fourier Analysis on Groups*, Theorem 1.4.3. -/
theorem bochner (F : V → ℂ) (hcont : Continuous F) :
    (IsPositiveDefiniteKernel fun a b : V => F (a - b)) ↔
      ∃! μ : Measure V, IsFiniteMeasure μ ∧ ∀ v, F v = ∫ q, fourierAtom v q ∂μ := by
  constructor
  · intro hpd
    obtain ⟨μ, hfin, hrep⟩ :=
      exists_isFiniteMeasure_integral_fourierAtom_eq_of_isPositiveDefiniteKernel F hcont hpd
    refine ⟨μ, ⟨hfin, hrep⟩, ?_⟩
    rintro ν ⟨hνfin, hνrep⟩
    have := hfin
    have := hνfin
    exact Measure.ext_of_forall_integral_fourierAtom_eq
      fun v => (hνrep v).symm.trans (hrep v)
  · rintro ⟨μ, ⟨hfin, hrep⟩, -⟩
    have := hfin
    have hfun : (fun a b : V => F (a - b)) =
        fun a b : V => ∫ q, fourierAtom (a - b) q ∂μ := by
      funext a b
      exact hrep (a - b)
    rw [hfun]
    exact fourierConventionCharFun_isPositiveDefiniteKernel

/-- **Bochner's theorem for the involutive predicate.** Under the negation involution
`star x = -x`, a continuous function is positive definite in the involutive sense if and only
if it is the Fourier-convention transform of a unique finite Borel measure. -/
theorem bochner_of_forall_star_eq_neg [StarAddMonoid V] (hstar : ∀ x : V, star x = -x)
    (F : V → ℂ) (hcont : Continuous F) :
    IsPositiveDefinite F ↔
      ∃! μ : Measure V, IsFiniteMeasure μ ∧ ∀ v, F v = ∫ q, fourierAtom v q ∂μ :=
  (isPositiveDefinite_iff_isPositiveDefiniteKernel_sub hstar).trans (bochner F hcont)

end TauCeti

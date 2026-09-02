/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.StudentT.WeightedIntegral
public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.Probability.Moments.Variance
import TauCeti.Analysis.SpecialFunctions.Beta
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Moments and exponential moments of Student's t law

This file develops the moments of the Student t distribution defined in
`TauCeti/Probability/Distributions/StudentT/Basic.lean`. The density is even, and on the positive
half-line the substitution `w = x ^ 2 / ν` turns every weighted integral into Euler's second beta
integral `∫ w ^ (a - 1) * (1 + w) ^ (-(a + b)) = Β(a, b)`. The cumulative distribution function is
computed in `TauCeti/Probability/Distributions/StudentT/Cdf.lean`.

## Main results

* `integral_id_studentTMeasure` — the mean is `0` when `1 < ν`;
* `not_integrable_id_studentTMeasure` and `not_integrable_sq_studentTMeasure` — the sharp
  non-integrability statements at `ν ≤ 1` and `ν ≤ 2`;
* `variance_id_studentTMeasure` — the variance is `ν / (ν - 2)` when `2 < ν`;
* `integrableExpSet_id_studentTMeasure` — the exponential-moment domain is the singleton `{0}`,
  together with the matching non-integrability statement for every nonzero rate.

## References

* Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 3, the **Student's t** target.
* Formal declaration scaffold: `TauCetiRoadmap/StandardDistributions/Suggested.lean`, Layer 3.
* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2, 2nd ed.,
  Wiley (1995), ch. 28.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set

open scoped ENNReal Real

namespace TauCeti

namespace Probability

variable {ν q x t : ℝ}

/-- The beta kernel is integrable on the positive half-line precisely for `-1 < q < ν`: the
exponent at `0` is `(q - 1) / 2` and the tail exponent is `(q - ν - 2) / 2`. -/
private lemma integrableOn_studentTBetaKernel_Ioi_iff (hν : 0 < ν) (hq : -1 < q) :
    IntegrableOn (studentTBetaKernel ν q) (Ioi (0 : ℝ)) ↔ q < ν := by
  set s := (ν + 1) / 2
  constructor
  · intro h
    by_cases hqν : q < ν
    · exact hqν
    set e := (q - ν - 2) / 2 with he
    have he1 : -1 ≤ e := by linarith
    have hbound : ∀ᶠ w in atTop,
        (2 : ℝ) ^ (-s) * w ^ e ≤ studentTBetaKernel ν q w := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with w hw
      have hw0 : 0 < w := by linarith
      have hle : 1 + w ≤ 2 * w := by
        have h : 1 ≤ w := hw
        linarith
      have hpos1 : 0 < 1 + w := by linarith
      have hpos2 : 0 < 2 * w := by linarith
      have hs_pos : 0 < s := by
        dsimp only [s]
        linarith [hν]
      have hp : (1 + w) ^ s ≤ (2 * w) ^ s :=
        Real.rpow_le_rpow hpos1.le hle hs_pos.le
      have hneg1 : (1 + w) ^ (-s) = ((1 + w) ^ s)⁻¹ :=
        Real.rpow_neg hpos1.le s
      have hneg2 : (2 * w) ^ (-s) = ((2 * w) ^ s)⁻¹ :=
        Real.rpow_neg hpos2.le s
      have h : (2 * w) ^ (-s) ≤ (1 + w) ^ (-s) := by
        rw [hneg2, hneg1]
        have hpos : 0 < (1 + w) ^ s := Real.rpow_pos_of_pos hpos1 s
        have h9 : 1 / (2 * w) ^ s ≤ 1 / (1 + w) ^ s :=
          one_div_le_one_div_of_le hpos hp
        simpa [div_eq_mul_inv] using h9
      have h9' : (2 * w) ^ (-s) = (2 : ℝ) ^ (-s) * w ^ (-s) := by
        rw [Real.mul_rpow (by positivity) hw0.le]
      have h10 : studentTBetaKernel ν q w =
          w ^ ((q - 1) / 2) * (1 + w) ^ (-s) := by
        rfl
      rw [h10]
      have h12 : w ^ e = w ^ ((q - 1) / 2) * w ^ (-s) := by
        have heq' : (q - 1) / 2 + (-s) = e := by
          dsimp only [e, s]; ring_nf
        have h12' : w ^ ((q - 1) / 2) * w ^ (-s) = w ^ e := by
          rw [← Real.rpow_add hw0 ((q - 1) / 2) (-s), heq']
        exact h12'.symm
      have h11 : (2 : ℝ) ^ (-s) * w ^ e ≤ studentTBetaKernel ν q w := by
        calc
          (2 : ℝ) ^ (-s) * w ^ e
            = (2 : ℝ) ^ (-s) * (w ^ ((q - 1) / 2) * w ^ (-s)) := by rw [h12]
          _ = w ^ ((q - 1) / 2) * ((2 : ℝ) ^ (-s) * w ^ (-s)) := by ring
          _ = w ^ ((q - 1) / 2) * (2 * w) ^ (-s) := by rw [h9']
          _ ≤ w ^ ((q - 1) / 2) * (1 + w) ^ (-s) :=
            mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hw0.le _)
          _ = studentTBetaKernel ν q w := h10.symm
      exact h11
    have hIoi1 : IntegrableOn (studentTBetaKernel ν q) (Ioi (1 : ℝ)) :=
      h.mono_set fun x hx => mem_Ioi.mpr (by linarith [mem_Ioi.mp hx])
    obtain ⟨a0, ha0⟩ := eventually_atTop.mp hbound
    set a := max a0 1 with ha_def
    have ha : ∀ w : ℝ, a ≤ w → (2 : ℝ) ^ (-s) * w ^ e ≤ studentTBetaKernel ν q w := by
      intro w hw
      exact ha0 w (le_trans (le_max_left a0 1) hw)
    let f : ℝ → ℝ := fun w => (2 : ℝ) ^ (-s) * w ^ e
    -- `f` is continuous on the compact interval `[1, a]`, where the base is bounded away from 0
    have hf_contOn : ContinuousOn f (Icc (1 : ℝ) a) := by
      apply ContinuousOn.mul
      · exact continuous_const.continuousOn
      · intro x hx
        have hx1 : x ≠ 0 := by
          have h2 : 1 ≤ x := hx.1
          linarith
        exact Real.continuousAt_rpow_const x e (Or.inl hx1) |>.continuousWithinAt
    have hbounded : IntegrableOn f (Icc (1 : ℝ) a) :=
      hf_contOn.integrableOn_Icc
    have hbounded' : IntegrableOn f (Ioc (1 : ℝ) a) :=
      hbounded.mono_set Ioc_subset_Icc_self
    have hae : ∀ᵐ w ∂volume.restrict (Ioi a), |f w| ≤ studentTBetaKernel ν q w := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
      have hwa : a ≤ w := le_of_lt hw
      have hwpos : 0 < w := by
        have h1 : 1 ≤ a := by simp [ha_def]
        linarith
      have hnonneg : 0 ≤ f w := by
        dsimp only [f]
        exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hwpos.le _)
      have habs : |f w| = f w := abs_of_nonneg hnonneg
      rw [habs]
      exact ha w hwa
    have ha1 : 1 ≤ a := by
      simp [ha_def]
    have hIoi_a : IntegrableOn (studentTBetaKernel ν q) (Ioi a) :=
      hIoi1.mono_set fun x hx => by
        have hxa : a < x := hx
        have h : 1 < x := by linarith [ha1, hxa]
        exact h
    have htail : IntegrableOn f (Ioi a) :=
      hIoi_a.mono' (by fun_prop) hae
    have hconst : IntegrableOn f (Ioi (1 : ℝ)) := by
      have hdisj : Disjoint (Ioc (1 : ℝ) a) (Ioi a) := by
        simp [Set.disjoint_left]
      have hunion : Ioc (1 : ℝ) a ∪ Ioi a = Ioi (1 : ℝ) := by
        ext x; simp [ha_def]
      have : IntegrableOn f (Ioc (1 : ℝ) a ∪ Ioi a) :=
        hbounded'.union htail
      rwa [hunion] at this
    have hc : IsUnit ((2 : ℝ) ^ (-s)) :=
      isUnit_iff_ne_zero.mpr (Real.rpow_pos_of_pos (by positivity) _).ne'
    have hpow : IntegrableOn (fun w : ℝ => w ^ e) (Ioi (1 : ℝ)) := by
      have h : IntegrableOn (fun w : ℝ => (2 : ℝ) ^ (-s) * w ^ e) (Ioi (1 : ℝ)) := hconst
      have h' : IntegrableOn (fun w : ℝ => w ^ e) (Ioi (1 : ℝ)) := by
        simpa [IntegrableOn, integrable_const_mul_iff hc] using h
      exact h'
    rw [integrableOn_Ioi_rpow_iff one_pos] at hpow
    linarith
  · intro hqν
    set ha := (q + 1) / 2
    set hb := (ν - q) / 2 with hb_def
    have ha_pos : 0 < ha := by
      dsimp only [ha]; linarith
    have hb_pos : 0 < hb := by
      dsimp only [hb]; linarith
    have hsum : ha + hb = s := by
      dsimp only [ha, hb, s]; ring
    have h := integrableOn_rpow_mul_one_add_rpow ha_pos hb_pos
    have hkernel : ∀ w : ℝ, studentTBetaKernel ν q w =
        w ^ (ha - 1) * (1 + w) ^ (-(ha + hb)) := by
      intro w
      dsimp only [studentTBetaKernel]
      have h1 : (q - 1) / 2 = ha - 1 := by
        dsimp only [ha]; ring
      have h2 : -((ν + 1) / 2) = -(ha + hb) := by
        dsimp only [ha, hb]; ring
      rw [h1, h2]
    have h3 : IntegrableOn (studentTBetaKernel ν q) (Ioi (0 : ℝ)) := by
      have h4 : EqOn (fun w : ℝ => w ^ (ha - 1) * (1 + w) ^ (-(ha + hb)))
          (studentTBetaKernel ν q) (Ioi (0 : ℝ)) := by
        intro w hw
        exact (hkernel w).symm
      exact h.congr_fun h4 measurableSet_Ioi
    exact h3

/-- The weighted Student t density `studentTPDFReal ν x * x ^ q` is integrable on the positive
half-line exactly for `-1 < q < ν`. -/
private theorem integrableOn_pow_mul_studentTPDFReal_Ioi_iff (hν : 0 < ν) (hq : -1 < q) :
    IntegrableOn (fun x : ℝ => studentTPDFReal ν x * x ^ q) (Ioi (0 : ℝ)) ↔ q < ν := by
  set C := Real.Gamma ((ν + 1) / 2) / (Real.sqrt (ν * Real.pi) * Real.Gamma (ν / 2))
  let g : ℝ → ℝ := fun w => C * ν ^ ((q + 1) / 2) / 2 * studentTBetaKernel ν q w
  have hderiv : ∀ z ∈ Ioi (0 : ℝ),
      HasDerivWithinAt (fun z : ℝ => z ^ 2 / ν) (2 * z / ν) (Ioi (0 : ℝ)) z :=
    fun z _ => (hasDerivAt_sq_div_const ν z).hasDerivWithinAt
  have hiff : IntegrableOn g (Ioi (0 : ℝ)) ↔
      IntegrableOn (fun x : ℝ => studentTPDFReal ν x * x ^ q) (Ioi (0 : ℝ)) := by
    have himg0 : (fun z : ℝ => z ^ 2 / ν) '' Ioi (0 : ℝ) = Ioi (0 ^ 2 / ν) :=
      image_sq_div_const_Ioi hν (y := 0) le_rfl
    have himg : (fun z : ℝ => z ^ 2 / ν) '' Ioi (0 : ℝ) = Ioi (0 : ℝ) := by
      rw [himg0]
      simp
    have h_g_eq : ∀ z : ℝ, 0 < z → |2 * z / ν| • g (z ^ 2 / ν) =
        studentTPDFReal ν z * z ^ q := by
      intro z hz
      simpa [g] using abs_deriv_smul_studentTPDFReal hν q hz
    have h_g_eq' : EqOn (fun z : ℝ => |2 * z / ν| • g (z ^ 2 / ν))
        (fun x : ℝ => studentTPDFReal ν x * x ^ q) (Ioi (0 : ℝ)) := by
      intro z hz
      exact h_g_eq z hz
    have himg1 : IntegrableOn (fun z : ℝ => |2 * z / ν| • g (z ^ 2 / ν)) (Ioi (0 : ℝ)) ↔
        IntegrableOn (fun x : ℝ => studentTPDFReal ν x * x ^ q) (Ioi (0 : ℝ)) := by
      refine ⟨fun h => h.congr_fun h_g_eq' measurableSet_Ioi,
        fun h => h.congr_fun (fun z hz => (h_g_eq' hz).symm) measurableSet_Ioi⟩
    have hpre : IntegrableOn g ((fun z : ℝ => z ^ 2 / ν) '' Ioi (0 : ℝ)) ↔
        IntegrableOn (fun z : ℝ => |2 * z / ν| • g (z ^ 2 / ν)) (Ioi (0 : ℝ)) :=
      integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hderiv
        (injOn_sq_div_const_Ioi hν) g
    rw [himg] at hpre
    exact hpre.trans himg1
  have hC_ne : C ≠ 0 := (studentT_const_pos hν).ne'
  have hc : IsUnit (C * ν ^ ((q + 1) / 2) / 2) := isUnit_iff_ne_zero.mpr <|
    div_ne_zero (mul_ne_zero hC_ne (Real.rpow_pos_of_pos hν _).ne') (by norm_num)
  rw [← hiff]
  simpa [g, IntegrableOn, integrable_const_mul_iff hc] using
    integrableOn_studentTBetaKernel_Ioi_iff hν hq

/-- The value of the weighted half-line integral: with `a = (q + 1) / 2` and `b = (ν - q) / 2`,
it is `C(ν) * ν ^ a / 2 * Β(a, b)`, where `C(ν)` is the Student t normalizing constant. -/
private theorem integral_Ioi_pow_mul_studentTPDFReal (hν : 0 < ν) (hq1 : -1 < q) (hq2 : q < ν) :
    ∫ x in Ioi (0 : ℝ), studentTPDFReal ν x * x ^ q =
      (Real.Gamma ((ν + 1) / 2) / (Real.sqrt (ν * Real.pi) * Real.Gamma (ν / 2))) *
        ν ^ ((q + 1) / 2) / 2 * beta ((q + 1) / 2) ((ν - q) / 2) := by
  set s := (ν + 1) / 2
  set C := Real.Gamma s / (Real.sqrt (ν * Real.pi) * Real.Gamma (ν / 2))
  let g : ℝ → ℝ := fun w => C * ν ^ ((q + 1) / 2) / 2 * studentTBetaKernel ν q w
  have hderiv : ∀ z ∈ Ioi (0 : ℝ),
      HasDerivWithinAt (fun z : ℝ => z ^ 2 / ν) (2 * z / ν) (Ioi (0 : ℝ)) z :=
    fun z _ => (hasDerivAt_sq_div_const ν z).hasDerivWithinAt
  have himg0 : (fun z : ℝ => z ^ 2 / ν) '' Ioi (0 : ℝ) = Ioi (0 ^ 2 / ν) :=
    image_sq_div_const_Ioi hν (y := 0) le_rfl
  have himg : (fun z : ℝ => z ^ 2 / ν) '' Ioi (0 : ℝ) = Ioi (0 : ℝ) := by
    rw [himg0]; simp
  have h_g_eq : ∀ z : ℝ, 0 < z → |2 * z / ν| • g (z ^ 2 / ν) =
      studentTPDFReal ν z * z ^ q := by
    intro z hz
    simpa [g] using abs_deriv_smul_studentTPDFReal hν q hz
  have h1 : ∫ x in Ioi (0 : ℝ), studentTPDFReal ν x * x ^ q =
      ∫ x in Ioi (0 : ℝ), |2 * x / ν| • g (x ^ 2 / ν) := by
    have h : EqOn (fun x : ℝ => studentTPDFReal ν x * x ^ q)
        (fun x : ℝ => |2 * x / ν| • g (x ^ 2 / ν)) (Ioi (0 : ℝ)) := by
      intro x hx
      exact (h_g_eq x hx).symm
    exact setIntegral_congr_fun measurableSet_Ioi h
  rw [h1]
  have h2 : ∫ w in (fun z : ℝ => z ^ 2 / ν) '' Ioi (0 : ℝ), g w =
      ∫ x in Ioi (0 : ℝ), |2 * x / ν| • g (x ^ 2 / ν) :=
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv
      (injOn_sq_div_const_Ioi hν) g
  rw [← h2, himg]
  have ha : 0 < (q + 1) / 2 := by linarith
  have hb : 0 < (ν - q) / 2 := by linarith
  have hsum : (q + 1) / 2 + (ν - q) / 2 = s := by ring
  have hkernel_eq : EqOn (studentTBetaKernel ν q)
      (fun w : ℝ => w ^ (((q + 1) / 2) - 1) *
        (1 + w) ^ (-(((q + 1) / 2) + ((ν - q) / 2)))) (Ioi (0 : ℝ)) := by
    intro w _
    dsimp only [studentTBetaKernel]
    have h1 : (q - 1) / 2 = (q + 1) / 2 - 1 := by ring
    have h2 : -((ν + 1) / 2) = -(((q + 1) / 2) + ((ν - q) / 2)) := by ring
    have h3 : w ^ ((q - 1) / 2) * (1 + w) ^ (-((ν + 1) / 2)) =
        w ^ (((q + 1) / 2) - 1) *
          (1 + w) ^ (-(((q + 1) / 2) + ((ν - q) / 2))) := by
      rw [h1, h2]
    exact h3
  have h3 : ∫ w in Ioi (0 : ℝ), g w =
      C * ν ^ ((q + 1) / 2) / 2 * beta ((q + 1) / 2) ((ν - q) / 2) := by
    simp only [g, integral_const_mul]
    have h4 : ∫ w in Ioi (0 : ℝ), studentTBetaKernel ν q w =
        ∫ w in Ioi (0 : ℝ), w ^ (((q + 1) / 2) - 1) *
          (1 + w) ^ (-(((q + 1) / 2) + ((ν - q) / 2))) :=
      setIntegral_congr_fun measurableSet_Ioi hkernel_eq
    rw [h4, integral_rpow_mul_one_add_rpow ha hb]
  exact h3

/-! ### Reflection across the origin -/

/-- Reflection in the origin relates integrability on the two half-lines for an odd function. -/
private lemma integrableOn_reflect_odd_Iic_iff_Ioi {g : ℝ → ℝ} (hneg : ∀ x, g (-x) = -g x) :
    IntegrableOn g (Iic (0 : ℝ)) ↔ IntegrableOn g (Ioi (0 : ℝ)) := by
  have hmp := Measure.measurePreserving_neg (volume : Measure ℝ)
  have hpre : (fun z : ℝ => -z) ⁻¹' (Ici (0 : ℝ)) = Iic (0 : ℝ) := by
    ext z
    simp
  have h1 : IntegrableOn (fun x : ℝ => g (-x)) (Iic (0 : ℝ)) ↔
      IntegrableOn g (Ici (0 : ℝ)) := by
    rw [← hpre]
    exact hmp.integrableOn_comp_preimage (Homeomorph.neg ℝ).measurableEmbedding
  have h2 : (fun x : ℝ => g (-x)) = fun x : ℝ => -g x := funext hneg
  rw [h2] at h1
  have h3 : IntegrableOn (fun x : ℝ => -g x) (Iic (0 : ℝ)) ↔
      IntegrableOn g (Iic (0 : ℝ)) := integrableOn_neg_iff
  rw [h3] at h1
  rw [h1, integrableOn_Ici_iff_integrableOn_Ioi]

/-- Reflection in the origin relates integrability on the two half-lines for an even function. -/
private lemma integrableOn_reflect_even_Iic_iff_Ioi {g : ℝ → ℝ} (heven : ∀ x, g (-x) = g x) :
    IntegrableOn g (Iic (0 : ℝ)) ↔ IntegrableOn g (Ioi (0 : ℝ)) := by
  have hmp := Measure.measurePreserving_neg (volume : Measure ℝ)
  have hpre : (fun z : ℝ => -z) ⁻¹' (Ici (0 : ℝ)) = Iic (0 : ℝ) := by
    ext z
    simp
  have h1 : IntegrableOn (fun x : ℝ => g (-x)) (Iic (0 : ℝ)) ↔
      IntegrableOn g (Ici (0 : ℝ)) := by
    rw [← hpre]
    exact hmp.integrableOn_comp_preimage (Homeomorph.neg ℝ).measurableEmbedding
  have h2 : (fun x : ℝ => g (-x)) = g := funext heven
  rw [h2] at h1
  rw [h1, integrableOn_Ici_iff_integrableOn_Ioi]

/-- For an odd integrable function, the integral over the nonpositive half-line is the negative of
the integral over the positive half-line. -/
private lemma setIntegral_Iic_odd_eq_neg_Ioi {g : ℝ → ℝ} (_hg : Integrable g)
    (hneg : ∀ x, g (-x) = -g x) :
    ∫ x in Iic (0 : ℝ), g x = -∫ x in Ioi (0 : ℝ), g x := by
  have hmp := Measure.measurePreserving_neg (volume : Measure ℝ)
  have himg : (fun x : ℝ => -x) '' Iic (0 : ℝ) = Ici (0 : ℝ) := by
    ext y; simp
  have h := hmp.setIntegral_image_emb (Homeomorph.neg ℝ).measurableEmbedding g (Iic (0 : ℝ))
  rw [himg] at h
  have h3 : (fun x : ℝ => g (-x)) = fun x : ℝ => -g x := funext hneg
  have h4 : ∫ x in Iic (0 : ℝ), g (-x) = -∫ x in Iic (0 : ℝ), g x := by
    rw [h3]
    simpa using integral_neg g
  rw [h4] at h
  have h5 : ∫ x in Ici (0 : ℝ), g x = ∫ x in Ioi (0 : ℝ), g x := by
    rw [setIntegral_congr_set Ioi_ae_eq_Ici.symm]
  rw [h5] at h
  linarith

/-! ### Integrability of the identity and of the square -/

/-- The identity is integrable under a Student t law exactly when the number of degrees of
freedom exceeds `1`. -/
theorem integrable_id_studentTMeasure_iff (hν : 0 < ν) :
    Integrable id (studentTMeasure ν) ↔ 1 < ν := by
  -- `studentTMeasure ν` *is* `volume.withDensity (studentTPDF ν)` by the definition in
  -- Basic.lean; work throughout with the withDensity measure and conclude via the
  -- definitional equality
  let g : ℝ → ℝ := fun x => studentTPDFReal ν x * x
  have hodd : ∀ x, g (-x) = -g x := by
    intro x
    have h : g (-x) = studentTPDFReal ν (-x) * (-x) := by rfl
    rw [h, studentTPDFReal_neg]; ring
  have hIoi : IntegrableOn g (Ioi (0 : ℝ)) ↔ 1 < ν := by
    have hq1 : -1 < (1 : ℝ) := by norm_num
    have h1 : IntegrableOn (fun x : ℝ => studentTPDFReal ν x * x ^ (1 : ℝ)) (Ioi (0 : ℝ)) ↔
        (1 : ℝ) < ν := integrableOn_pow_mul_studentTPDFReal_Ioi_iff hν hq1
    have h2 : (fun x : ℝ => studentTPDFReal ν x * x ^ (1 : ℝ)) = g := by
      funext x
      simp [g, Real.rpow_one]
    rw [h2] at h1
    exact h1
  have hfull : Integrable g ↔ IntegrableOn g (Ioi (0 : ℝ)) := by
    rw [← integrableOn_univ, ← Iic_union_Ioi, integrableOn_union,
      integrableOn_reflect_odd_Iic_iff_Ioi hodd]
    exact and_self_iff
  have hlt : ∀ᵐ x : ℝ ∂volume, studentTPDF ν x < ⊤ :=
    ae_of_all _ fun x => by
      rw [studentTPDF_of_pos hν x]
      exact ENNReal.ofReal_lt_top
  have h : Integrable (fun x : ℝ => (id x : ℝ) * (studentTPDF ν x).toReal) volume ↔
      Integrable id (volume.withDensity (studentTPDF ν)) :=
    (integrable_withDensity_iff (measurable_studentTPDF ν) hlt).symm
  have hfeq : (fun x : ℝ => (id x : ℝ) * (studentTPDF ν x).toReal) = g := by
    funext x
    have hto : (studentTPDF ν x).toReal = studentTPDFReal ν x := toReal_studentTPDF ν x
    simp [g, hto]; ring
  rw [hfeq] at h
  -- `studentTMeasure ν = volume.withDensity (studentTPDF ν)` by definition in Basic.lean
  -- (`abbrev studentTMeasure`), so the two terms are definitionally equal
  exact h.symm.trans (hfull.trans hIoi)

/-- The identity is not integrable under a Student t law with at most one degree of freedom:
the mean does not exist. -/
theorem not_integrable_id_studentTMeasure (hν0 : 0 < ν) (hν1 : ν ≤ 1) :
    ¬ Integrable id (studentTMeasure ν) := by
  rw [integrable_id_studentTMeasure_iff hν0]
  exact not_lt.mpr hν1

/-- The mean of a Student t law with more than one degree of freedom is `0`: the density is even
and the identity is integrable. -/
theorem integral_id_studentTMeasure (hν : 1 < ν) :
    ∫ x, x ∂studentTMeasure ν = 0 := by
  have hν0 : 0 < ν := by linarith
  let g : ℝ → ℝ := fun x => studentTPDFReal ν x * x
  have hodd : ∀ x, g (-x) = -g x := by
    intro x
    have h : g (-x) = studentTPDFReal ν (-x) * (-x) := by rfl
    rw [h, studentTPDFReal_neg]; ring
  have hq1 : -1 < (1 : ℝ) := by norm_num
  have hgIoi0 : IntegrableOn (fun x : ℝ => studentTPDFReal ν x * x ^ (1 : ℝ)) (Ioi (0 : ℝ)) :=
    (integrableOn_pow_mul_studentTPDFReal_Ioi_iff hν0 hq1).mpr (by linarith)
  have hgeq : (fun x : ℝ => studentTPDFReal ν x * x ^ (1 : ℝ)) = g := by
    funext x
    simp [g, Real.rpow_one]
  have hgIoi : IntegrableOn g (Ioi (0 : ℝ)) := by
    rw [← hgeq]
    exact hgIoi0
  have hgIic : IntegrableOn g (Iic (0 : ℝ)) :=
    (integrableOn_reflect_odd_Iic_iff_Ioi hodd).mpr hgIoi
  have hint : Integrable g := by
    rw [← integrableOn_univ, ← Iic_union_Ioi]
    exact hgIic.union hgIoi
  have hsum : ∫ x in Iic (0 : ℝ), g x = -∫ x in Ioi (0 : ℝ), g x :=
    setIntegral_Iic_odd_eq_neg_Ioi hint hodd
  have h_add : (∫ x in Iic (0 : ℝ), g x) + ∫ x in Ioi (0 : ℝ), g x = 0 := by
    have h : (∫ x in Iic (0 : ℝ), g x) = -∫ x in Ioi (0 : ℝ), g x := hsum
    rw [h]; ring
  have huniv : ∫ x, g x = 0 := by
    have h9 : (∫ x in Iic (0 : ℝ), g x) + ∫ x in (Iic (0 : ℝ))ᶜ, g x = ∫ x, g x :=
      integral_add_compl (s := Iic (0 : ℝ)) measurableSet_Iic hint
    have h10 : ∫ x in (Iic (0 : ℝ))ᶜ, g x = ∫ x in Ioi (0 : ℝ), g x := by
      rw [compl_Iic]
    linarith [h_add, h9, h10]
  have hlt : ∀ᵐ x : ℝ ∂volume, studentTPDF ν x < ⊤ :=
    ae_of_all _ fun x => by
      rw [studentTPDF_of_pos hν0 x]
      exact ENNReal.ofReal_lt_top
  have hfinal : ∫ x, x ∂studentTMeasure ν = ∫ x, g x := by
    have hmsr : studentTMeasure ν = volume.withDensity (studentTPDF ν) := by rfl
    rw [hmsr]
    have h : ∫ x, (x : ℝ) ∂volume.withDensity (studentTPDF ν) =
        ∫ x, (studentTPDF ν x).toReal • (x : ℝ) :=
      integral_withDensity_eq_integral_toReal_smul
        (measurable_studentTPDF ν) hlt (id)
    rw [h]
    have hfeq : (fun x : ℝ => (studentTPDF ν x).toReal • (x : ℝ)) = g := by
      funext x
      have hto : (studentTPDF ν x).toReal = studentTPDFReal ν x := toReal_studentTPDF ν x
      simp [g, hto, smul_eq_mul]
    rw [hfeq]
  rw [hfinal, huniv]

/-- Squaring is integrable under a Student t law exactly when the number of degrees of freedom
exceeds `2`. -/
theorem integrable_sq_studentTMeasure_iff (hν : 0 < ν) :
    Integrable (fun x : ℝ => x ^ 2) (studentTMeasure ν) ↔ 2 < ν := by
  let g : ℝ → ℝ := fun x => studentTPDFReal ν x * x ^ 2
  have heven : ∀ x, g (-x) = g x := by
    intro x
    simp only [g, studentTPDFReal_neg, neg_sq]
  have hq1 : -1 < (2 : ℝ) := by norm_num
  have h2 : (fun x : ℝ => studentTPDFReal ν x * x ^ (2 : ℝ)) = g := by
    funext x
    simp [g]
  have hIoi : IntegrableOn g (Ioi (0 : ℝ)) ↔ 2 < ν := by
    rw [← h2]
    exact integrableOn_pow_mul_studentTPDFReal_Ioi_iff hν hq1
  have hfull : Integrable g ↔ IntegrableOn g (Ioi (0 : ℝ)) := by
    rw [← integrableOn_univ, ← Iic_union_Ioi, integrableOn_union,
      integrableOn_reflect_even_Iic_iff_Ioi heven]
    exact and_self_iff
  have hlt : ∀ᵐ x : ℝ ∂volume, studentTPDF ν x < ⊤ :=
    ae_of_all _ fun x => by
      rw [studentTPDF_of_pos hν x]
      exact ENNReal.ofReal_lt_top
  have h : Integrable (fun x : ℝ => x ^ 2) (volume.withDensity (studentTPDF ν)) ↔
      Integrable (fun x : ℝ => (x ^ 2) * (studentTPDF ν x).toReal) volume :=
    integrable_withDensity_iff (measurable_studentTPDF ν) hlt
  have hfeq : (fun x : ℝ => (x ^ 2) * (studentTPDF ν x).toReal) = g := by
    funext x
    have hto : (studentTPDF ν x).toReal = studentTPDFReal ν x := toReal_studentTPDF ν x
    simp [g, hto]; ring
  rw [hfeq] at h
  -- the goal is `Integrable (x^2) (studentTMeasure ν) ↔ 2 < ν`, and
  -- `studentTMeasure ν = volume.withDensity (studentTPDF ν)` by definition
  exact h.trans (hfull.trans hIoi)

/-- At most two degrees of freedom, the second raw moment of a Student t law diverges. -/
theorem not_integrable_sq_studentTMeasure (hν0 : 0 < ν) (hν2 : ν ≤ 2) :
    ¬ Integrable (fun x : ℝ => x ^ 2) (studentTMeasure ν) := by
  rw [integrable_sq_studentTMeasure_iff hν0]
  exact not_lt.mpr hν2

/-- The half-line second raw moment of a Student t law with more than two degrees of freedom is
`ν / (2 * (ν - 2))`; the full moment is twice that by evenness. -/
private lemma integral_Ioi_sq_mul_studentTPDFReal (hν : 2 < ν) :
    ∫ x in Ioi (0 : ℝ), studentTPDFReal ν x * x ^ 2 = ν / (2 * (ν - 2)) := by
  have hν0 : 0 < ν := by linarith
  have hq1 : -1 < (2 : ℝ) := by norm_num
  have h := integral_Ioi_pow_mul_studentTPDFReal hν0 hq1 (by linarith)
  -- `x ^ (2 : ℝ) = x ^ 2` for positive `x`
  have h_eq1 : (fun x : ℝ => studentTPDFReal ν x * x ^ (2 : ℝ)) =
      fun x : ℝ => studentTPDFReal ν x * x ^ 2 := by
    funext x
    have hr : x ^ (2 : ℝ) = x ^ 2 := by
      rw [Real.rpow_two]
    rw [hr]
  rw [h_eq1] at h
  -- the half-line moment is `C(ν) * ν^(3/2)/2 * Β(3/2, (ν-2)/2)`
  set C := Real.Gamma ((ν + 1) / 2) / (Real.sqrt (ν * Real.pi) * Real.Gamma (ν / 2)) with hC
  have h32 : (3 / 2 : ℝ) = (2 + 1) / 2 := by norm_num
  have h_beta : ProbabilityTheory.beta ((2 + 1) / 2) ((ν - 2) / 2) =
      Real.Gamma (3 / 2 : ℝ) * Real.Gamma ((ν - 2) / 2) / Real.Gamma ((ν + 1) / 2) := by
    rw [← h32, ProbabilityTheory.beta]; congr 2; ring
  have hG1 : Real.Gamma (3 / 2 : ℝ) = Real.sqrt Real.pi / 2 := by
    have h12 : (1 / 2 : ℝ) ≠ 0 := by norm_num
    have h : Real.Gamma (3 / 2 : ℝ) = (1 / 2 : ℝ) * Real.Gamma (1 / 2 : ℝ) := by
      have h9 : (3 / 2 : ℝ) = (1 / 2 : ℝ) + 1 := by norm_num
      rw [h9, Real.Gamma_add_one h12]
    rw [h, Real.Gamma_one_half_eq]; ring
  have hG2 : Real.Gamma (ν / 2) = ((ν - 2) / 2) * Real.Gamma ((ν - 2) / 2) := by
    have hne : (ν - 2) / 2 ≠ 0 := by linarith
    have h4 : ν / 2 = (ν - 2) / 2 + 1 := by ring
    rw [h4, Real.Gamma_add_one hne]
  have h_val : C * Real.rpow ν ((2 + 1) / 2) / 2 *
      ProbabilityTheory.beta ((2 + 1) / 2) ((ν - 2) / 2) = ν / (2 * (ν - 2)) := by
    -- Expand beta and Gamma identities, then cancel the common factors
    have hsqrt : Real.sqrt (ν * Real.pi) = Real.sqrt ν * Real.sqrt Real.pi := by
      rw [Real.sqrt_mul]; linarith
    have h5 : Real.rpow ν ((2 + 1) / 2) = Real.sqrt ν * ν := by
      have h72 : (3 / 2 : ℝ) = (1 : ℝ) + (1 / 2 : ℝ) := by norm_num
      have h73 : Real.rpow ν (3 / 2 : ℝ) =
          Real.rpow ν (1 : ℝ) * Real.rpow ν (1 / 2 : ℝ) := by
        rw [h72]
        exact Real.rpow_add hν0 (1 : ℝ) (1 / 2 : ℝ)
      have h6 : Real.rpow ν ((2 + 1) / 2) = Real.rpow ν (3 / 2 : ℝ) := by norm_num
      have h74 : Real.rpow ν (1 : ℝ) = ν := by simp
      have h71 : Real.rpow ν (1 / 2 : ℝ) = Real.sqrt ν := by
        exact (Real.sqrt_eq_rpow ν).symm
      rw [h6]
      rw [h73, h74, h71]; ring
    set sν := Real.sqrt ν with hsν
    set sπ := Real.sqrt Real.pi with hsπ
    set G := Real.Gamma ((ν - 2) / 2) with hG
    set k := (ν - 2) / 2 with hk
    set G1 := Real.Gamma ((ν + 1) / 2) with hG1
    set G32 := Real.Gamma (3 / 2 : ℝ) with hG32
    have hne_sν : sν ≠ 0 := (Real.sqrt_pos.mpr hν0).ne'
    have hne_sπ : sπ ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have hne_G : G ≠ 0 := by
      dsimp only [G]
      apply Real.Gamma_ne_zero
      intro m
      have h_pos : 0 < (ν - 2) / 2 := by linarith
      linarith
    have hne_k : k ≠ 0 := by
      dsimp only [k]; linarith
    have hG32_eq : G32 = sπ / 2 := by
      simp only [hG32, hsπ]
      exact hG1
    have hC' : C = G1 / (sν * sπ * (k * G)) := by
      dsimp only [C]
      rw [hsqrt, hG2]
    have hbeta' : ProbabilityTheory.beta ((2 + 1) / 2) ((ν - 2) / 2) =
        (sπ / 2) * G / G1 := by
      rw [h_beta, hG32_eq]
    have h5' : Real.rpow ν ((2 + 1) / 2) = sν * ν := h5
    have h_goal : C * Real.rpow ν ((2 + 1) / 2) / 2 *
        ProbabilityTheory.beta ((2 + 1) / 2) ((ν - 2) / 2) = ν / (2 * (ν - 2)) := by
      have h_step1 : C * Real.rpow ν ((2 + 1) / 2) / 2 *
          ProbabilityTheory.beta ((2 + 1) / 2) ((ν - 2) / 2) =
          (G1 / (sν * sπ * (k * G))) * (sν * ν) / 2 *
            ((sπ / 2) * G / G1) := by
        rw [hC', hbeta', h5']
      have h_ne_G1 : G1 ≠ 0 := by
        dsimp only [G1]
        exact Real.Gamma_ne_zero (fun m => by
          have h : (ν + 1) / 2 > 0 := by linarith
          linarith)
      have h_calc : (G1 / (sν * sπ * (k * G))) * (sν * ν) / 2 *
          ((sπ / 2) * G / G1) = ν / (4 * k) := by
        have h1 : sν ≠ 0 := hne_sν
        have h2 : sπ ≠ 0 := hne_sπ
        have h3 : G ≠ 0 := hne_G
        have h4 : G1 ≠ 0 := h_ne_G1
        have h5 : k ≠ 0 := hne_k
        have hpos : 0 < sν := Real.sqrt_pos.mpr hν0
        have hπpos : 0 < sπ := Real.sqrt_pos.mpr Real.pi_pos
        have hGpos : 0 < G := Real.Gamma_pos_of_pos (by linarith : 0 < (ν - 2) / 2)
        have hG1pos : 0 < G1 := Real.Gamma_pos_of_pos (by linarith : 0 < (ν + 1) / 2)
        have hkpos : 0 < k := by linarith
        have h_all_pos : 0 < sν * sπ * k * G * G1 := by positivity
        -- expand: `sν * sπ * k * G * G1 * LHS = sν * sπ * ν * G * G1 / 4`
        -- and `sν * sπ * k * G * G1 * (ν / (4 * k)) = sν * sπ * ν * G * G1 / 4`
        have h_ne_all : sν * sπ * k * G * G1 ≠ 0 := h_all_pos.ne'
        set LHS := (G1 / (sν * sπ * (k * G))) * (sν * ν) / 2 * ((sπ / 2) * G / G1) with hLHS
        have h_eq_simp : sν * sπ * k * G * G1 * LHS = sν * sπ * ν * G * G1 / 4 := by
          simp only [hLHS]
          field_simp; ring
        have h_rhs_simp : sν * sπ * k * G * G1 * (ν / (4 * k)) =
            sν * sπ * ν * G * G1 / 4 := by
          have h : k * (ν / (4 * k)) = ν / 4 := by
            field_simp [hkpos.ne']
          calc
            sν * sπ * k * G * G1 * (ν / (4 * k))
              = sν * sπ * G * G1 * (k * (ν / (4 * k))) := by ring
            _ = sν * sπ * G * G1 * (ν / 4) := by rw [h]
            _ = sν * sπ * ν * G * G1 / 4 := by ring
        have h_eq_mult : sν * sπ * k * G * G1 * LHS =
            sν * sπ * k * G * G1 * (ν / (4 * k)) := by
          rw [h_eq_simp, h_rhs_simp]
        exact (mul_right_inj' h_ne_all).mp h_eq_mult
      rw [h_step1, h_calc]
      have hk2 : k = (ν - 2) / 2 := by rfl
      rw [hk2]; ring
    exact h_goal
  rw [h]
  exact h_val

/-- The second raw moment of a Student t law with more than two degrees of freedom is
`ν / (ν - 2)`. -/
theorem integral_sq_studentTMeasure (hν : 2 < ν) :
    ∫ x, x ^ 2 ∂studentTMeasure ν = ν / (ν - 2) := by
  have hν0 : 0 < ν := by linarith
  have hlt : ∀ᵐ x : ℝ ∂volume, studentTPDF ν x < ⊤ :=
    ae_of_all _ fun x => by
      rw [studentTPDF_of_pos hν0 x]
      exact ENNReal.ofReal_lt_top
  have h2 : Integrable (fun x : ℝ => studentTPDFReal ν x * x ^ 2) := by
    have h := integrable_sq_studentTMeasure_iff hν0
    have h' : Integrable (fun x : ℝ => x ^ 2) (volume.withDensity (studentTPDF ν)) ↔
        Integrable (fun x : ℝ => (x ^ 2) * (studentTPDF ν x).toReal) :=
      integrable_withDensity_iff (measurable_studentTPDF ν) hlt
    have hfeq : (fun x : ℝ => (x ^ 2) * (studentTPDF ν x).toReal) =
        fun x : ℝ => studentTPDFReal ν x * x ^ 2 := by
      funext x
      have hto : (studentTPDF ν x).toReal = studentTPDFReal ν x := toReal_studentTPDF ν x
      simp [hto]; ring
    rw [hfeq] at h'
    exact h'.mp (h.mpr hν)
  have hfull : ∫ x, studentTPDFReal ν x * x ^ 2 =
      2 * ∫ x in Ioi (0 : ℝ), studentTPDFReal ν x * x ^ 2 := by
    have h := integral_comp_abs (f := fun y : ℝ => studentTPDFReal ν y * y ^ 2)
    have heven : ∀ x : ℝ, studentTPDFReal ν |x| * |x| ^ 2 = studentTPDFReal ν x * x ^ 2 := by
      intro x
      have h1 : |x| ^ 2 = x ^ 2 := sq_abs x
      have h2 : studentTPDFReal ν |x| = studentTPDFReal ν x := by
        by_cases h : 0 ≤ x
        · rw [abs_of_nonneg h]
        · have h' : x < 0 := by linarith
          rw [abs_of_neg h', studentTPDFReal_neg]
      rw [h1, h2]
    have habs : ∫ x, studentTPDFReal ν |x| * |x| ^ 2 =
        2 * ∫ x in Ioi (0 : ℝ), studentTPDFReal ν x * x ^ 2 := h
    have heq : (fun x : ℝ => studentTPDFReal ν |x| * |x| ^ 2) =
        fun x : ℝ => studentTPDFReal ν x * x ^ 2 := by
      funext x
      exact heven x
    rw [heq] at habs
    exact habs
  have hmsr : studentTMeasure ν = volume.withDensity (studentTPDF ν) := by rfl
  rw [hmsr]
  have h : ∫ x, (x ^ 2) ∂volume.withDensity (studentTPDF ν) =
      ∫ x, (studentTPDF ν x).toReal • (x ^ 2) :=
    integral_withDensity_eq_integral_toReal_smul
      (measurable_studentTPDF ν) hlt (fun x => x ^ 2)
  rw [h]
  have hfeq : (fun x : ℝ => (studentTPDF ν x).toReal • (x ^ 2)) =
      fun x : ℝ => studentTPDFReal ν x * x ^ 2 := by
    funext x
    have hto : (studentTPDF ν x).toReal = studentTPDFReal ν x := toReal_studentTPDF ν x
    simp [hto, smul_eq_mul]
  rw [hfeq, hfull]
  -- half-line moment is `ν / (2 * (ν - 2))`; full moment is twice that = `ν / (ν - 2)`
  have hhalf : ∫ x in Ioi (0 : ℝ), studentTPDFReal ν x * x ^ 2 = ν / (2 * (ν - 2)) :=
    integral_Ioi_sq_mul_studentTPDFReal hν
  rw [hhalf]
  have hne : ν - 2 ≠ 0 := by linarith
  field_simp [hne]

/-- The variance of a Student t law with more than two degrees of freedom is
`ν / (ν - 2)`. -/
theorem variance_id_studentTMeasure (hν : 2 < ν) :
    variance id (studentTMeasure ν) = ν / (ν - 2) := by
  have : IsProbabilityMeasure (studentTMeasure ν) :=
    isProbabilityMeasure_studentTMeasure (by linarith)
  have hmem : MemLp id 2 (studentTMeasure ν) := by
    rw [memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable]
    simpa [id_eq] using (integrable_sq_studentTMeasure_iff (by linarith)).mpr hν
  rw [variance_eq_sub hmem]
  have hmean : ∫ x : ℝ, (id x : ℝ) ∂studentTMeasure ν = 0 :=
    integral_id_studentTMeasure (by linarith)
  rw [hmean]
  simp only [Pi.pow_apply, id_eq, integral_sq_studentTMeasure hν]
  ring

/-! ### Exponential moments -/

/-- For large enough positive `x`, the Student t density dominates a positive constant multiple
of `x ^ (-(ν + 1))`. -/
private lemma eventually_studentTPDFReal_ge_rpow (hν : 0 < ν) :
    ∀ᶠ x in atTop,
      (Real.Gamma ((ν + 1) / 2) / (Real.sqrt (ν * Real.pi) * Real.Gamma (ν / 2))) *
          (ν / (ν + 1)) ^ ((ν + 1) / 2) ≤
        studentTPDFReal ν x * x ^ (ν + 1) := by
  set s := (ν + 1) / 2 with hs
  set C := Real.Gamma s / (Real.sqrt (ν * Real.pi) * Real.Gamma (ν / 2)) with hC
  set c := C * (ν / (ν + 1)) ^ s with hc
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  have hνpos : 0 < ((ν + 1) / ν) * x ^ 2 := by positivity
  have hle : 1 + x ^ 2 / ν ≤ ((ν + 1) / ν) * x ^ 2 := by
    have h1 : (1 : ℝ) ≤ x ^ 2 := by nlinarith
    have h2 : x ^ 2 + x ^ 2 / ν = ((ν + 1) / ν) * x ^ 2 := by
      field_simp [hν.ne']
    linarith
  have hle2 : 0 < 1 + x ^ 2 / ν := by positivity
  have hspos : 0 < s := by dsimp only [s]; linarith
  have hpos1 : 0 < (ν + 1) / ν := by positivity
  have hpos2 : 0 < ν / (ν + 1) := by positivity
  set A := (1 + x ^ 2 / ν) ^ s
  set B := (((ν + 1) / ν) * x ^ 2) ^ s
  have hApos : 0 < A := Real.rpow_pos_of_pos hle2 s
  have hBpos : 0 < B := Real.rpow_pos_of_pos hνpos s
  have hdecr : (1 + x ^ 2 / ν) ^ (-s) ≥ (((ν + 1) / ν) * x ^ 2) ^ (-s) := by
    -- `t ↦ t^(-s)` is decreasing on `(0, ∞)` for `s > 0`: the smaller base has the
    -- larger reciprocal power
    have hp : A ≤ B := Real.rpow_le_rpow (by positivity) hle hspos.le
    have ha : ∀ (y : ℝ), 0 < y → y ^ (-s) = (y ^ s)⁻¹ := fun y hy =>
      Real.rpow_neg hy.le s
    rw [ha (1 + x ^ 2 / ν) hle2, ha (((ν + 1) / ν) * x ^ 2) hνpos]
    have h9 : 1 / B ≤ 1 / A := one_div_le_one_div_of_le hApos hp
    have h10 : A⁻¹ ≥ B⁻¹ := by
      rw [inv_eq_one_div, inv_eq_one_div]
      exact h9
    exact h10
  have h_inv : ((ν + 1) / ν) * (ν / (ν + 1)) = 1 := by field_simp [hν.ne']
  have h3 : (((ν + 1) / ν) * x ^ 2) ^ (-s) =
      (ν / (ν + 1)) ^ s * x ^ (-(ν + 1)) := by
    have h4 : (((ν + 1) / ν) * x ^ 2) ^ (-s) =
        (((ν + 1) / ν) ^ (-s)) * (x ^ 2) ^ (-s) := by
      rw [Real.mul_rpow hpos1.le (by positivity)]
    have h6 : (((ν + 1) / ν) ^ s) * ((ν / (ν + 1)) ^ s) = 1 := by
      rw [← Real.mul_rpow hpos1.le hpos2.le, h_inv, Real.one_rpow]
    have h7 : ((ν / (ν + 1)) ^ s) = (((ν + 1) / ν) ^ s)⁻¹ :=
      eq_inv_of_mul_eq_one_right h6
    have h5 : ((ν + 1) / ν) ^ (-s) = (ν / (ν + 1)) ^ s := by
      rw [Real.rpow_neg hpos1.le, h7.symm]
    have h9 : (x ^ 2) ^ (-s) = x ^ (-(ν + 1)) := by
      rw [← Real.rpow_two, ← Real.rpow_mul hx0.le,
        show 2 * (-s) = -(ν + 1) by dsimp only [s]; ring]
    rw [h4, h5, h9]
  have hge : (1 + x ^ 2 / ν) ^ (-s) ≥ (ν / (ν + 1)) ^ s * x ^ (-(ν + 1)) := by
    calc (1 + x ^ 2 / ν) ^ (-s)
        ≥ (((ν + 1) / ν) * x ^ 2) ^ (-s) := hdecr
      _ = (ν / (ν + 1)) ^ s * x ^ (-(ν + 1)) := h3
  have hCpos : 0 < C := by
    rw [hC]
    exact studentT_const_pos hν
  have hmain : C * (1 + x ^ 2 / ν) ^ (-s) ≥
      C * ((ν / (ν + 1)) ^ s * x ^ (-(ν + 1))) :=
    mul_le_mul_of_nonneg_left hge hCpos.le
  have hpdf : studentTPDFReal ν x = C * (1 + x ^ 2 / ν) ^ (-s) := by
    rw [studentTPDFReal_of_pos hν, hC]
  have h4 : studentTPDFReal ν x ≥ c * x ^ (-(ν + 1)) := by
    rw [hpdf]
    have hc' : c * x ^ (-(ν + 1)) = C * ((ν / (ν + 1)) ^ s * x ^ (-(ν + 1))) := by
      rw [hc, hC]; ring
    rw [hc']
    exact hmain
  have hexp_add : -(ν + 1) + (ν + 1) = 0 := by ring
  have h5 : (c * x ^ (-(ν + 1))) * x ^ (ν + 1) = c := by
    have h6 : x ^ (-(ν + 1)) * x ^ (ν + 1) = 1 := by
      rw [← Real.rpow_add hx0, hexp_add, Real.rpow_zero]
    rw [mul_assoc, h6, mul_one]
  calc c
      = (c * x ^ (-(ν + 1))) * x ^ (ν + 1) := h5.symm
    _ ≤ studentTPDFReal ν x * x ^ (ν + 1) :=
      mul_le_mul_of_nonneg_right h4 (by positivity)

/-- The exponential of a positive multiple of the identity is not integrable against the Student
t density: the polynomial tail cannot absorb `exp (t * x)`. -/
private theorem not_integrable_exp_mul_studentTPDFReal_of_pos (hν : 0 < ν) {t : ℝ} (ht : 0 < t) :
    ¬ Integrable (fun x : ℝ => Real.exp (t * x) * studentTPDFReal ν x) := by
  set s := (ν + 1) / 2
  set C := Real.Gamma s / (Real.sqrt (ν * Real.pi) * Real.Gamma (ν / 2))
  set c := C * (ν / (ν + 1)) ^ s with hc
  have hc_pos : 0 < c := by positivity
  intro hint
  have hlarge : ∀ᶠ x in atTop, 1 / c ≤ Real.exp (t * x) / x ^ (ν + 1) :=
    (tendsto_exp_mul_div_rpow_atTop (ν + 1) t ht).eventually_ge_atTop (1 / c)
  have hbound : ∀ᶠ x in atTop, (1 : ℝ) ≤ Real.exp (t * x) * studentTPDFReal ν x := by
    filter_upwards [eventually_studentTPDFReal_ge_rpow hν, hlarge,
      eventually_ge_atTop (1 : ℝ)] with x hpdf hexp _
    have hx0 : 0 < x := by linarith
    have h10 : x ^ (ν + 1) * x ^ (-(ν + 1)) = 1 := by
      rw [← Real.rpow_add hx0, show (ν + 1) + (-(ν + 1)) = 0 by ring, Real.rpow_zero]
    have h6 : c * x ^ (-(ν + 1)) ≤ studentTPDFReal ν x := by
      have h7 : c ≤ studentTPDFReal ν x * x ^ (ν + 1) := hpdf
      have h8 : c * x ^ (-(ν + 1)) ≤
          (studentTPDFReal ν x * x ^ (ν + 1)) * x ^ (-(ν + 1)) :=
        mul_le_mul_of_nonneg_right h7 (Real.rpow_nonneg hx0.le _)
      have h9 : (studentTPDFReal ν x * x ^ (ν + 1)) * x ^ (-(ν + 1)) =
          studentTPDFReal ν x := by
        rw [mul_assoc, h10, mul_one]
      rw [h9] at h8
      exact h8
    have hxinv : x ^ (-(ν + 1)) = (x ^ (ν + 1))⁻¹ := Real.rpow_neg hx0.le _
    have h11 : c * (Real.exp (t * x) / x ^ (ν + 1)) =
        Real.exp (t * x) * (c * x ^ (-(ν + 1))) := by
      rw [hxinv]
      ring
    calc (1 : ℝ) = c * (1 / c) := by field_simp [hc_pos.ne']
      _ ≤ c * (Real.exp (t * x) / x ^ (ν + 1)) :=
        mul_le_mul_of_nonneg_left hexp hc_pos.le
      _ = Real.exp (t * x) * (c * x ^ (-(ν + 1))) := h11
      _ ≤ Real.exp (t * x) * studentTPDFReal ν x :=
        mul_le_mul_of_nonneg_left h6 (Real.exp_pos _).le
  obtain ⟨a, ha⟩ := eventually_atTop.mp hbound
  have hg : IntegrableOn (fun x : ℝ => Real.exp (t * x) * studentTPDFReal ν x) (Ioi a) :=
    hint.integrableOn
  have hone : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioi a) := by
    refine hg.mono' (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simpa using ha x hx.le
  rw [integrableOn_const_iff, Real.volume_Ioi] at hone
  simp at hone

/-- The exponential of a nonzero multiple of the identity is not integrable under a Student t
law. -/
theorem not_integrable_exp_mul_id_studentTMeasure (hν : 0 < ν) {t : ℝ} (ht : t ≠ 0) :
    ¬ Integrable (fun x : ℝ => Real.exp (t * x)) (studentTMeasure ν) := by
  have hlt : ∀ᵐ x : ℝ ∂volume, studentTPDF ν x < ⊤ := by
    filter_upwards with x
    rw [studentTPDF_of_pos hν]
    exact ENNReal.ofReal_lt_top
  have hfeq : (fun x : ℝ => Real.exp (t * x) * (studentTPDF ν x).toReal) =
      fun x : ℝ => Real.exp (t * x) * studentTPDFReal ν x := by
    funext x
    have hto : (studentTPDF ν x).toReal = studentTPDFReal ν x := toReal_studentTPDF ν x
    rw [hto]
  have hiff : Integrable (fun x : ℝ => Real.exp (t * x)) (studentTMeasure ν) ↔
      Integrable (fun x : ℝ => Real.exp (t * x) * studentTPDFReal ν x) := by
    rw [integrable_withDensity_iff (measurable_studentTPDF ν) hlt, hfeq]
  rw [hiff]
  intro hint
  rcases lt_or_gt_of_ne ht with ht | ht
  · -- negative rate: reflection in the origin carries the positive-tail divergence to this one
    let g : ℝ → ℝ := fun y => Real.exp (-t * y) * studentTPDFReal ν y
    have hgm : AEStronglyMeasurable g volume := by fun_prop
    have hmp : MeasurePreserving (fun x : ℝ => -x) volume volume :=
      Measure.measurePreserving_neg volume
    have h : Integrable (g ∘ fun x : ℝ => -x) volume ↔ Integrable g volume :=
      hmp.integrable_comp hgm
    have heq : (g ∘ fun x : ℝ => -x) = fun x : ℝ => Real.exp (t * x) * studentTPDFReal ν x := by
      funext x
      have harg : -t * (-x) = t * x := by ring
      simp only [Function.comp_apply, g, harg, studentTPDFReal_neg]
    rw [heq] at h
    exact not_integrable_exp_mul_studentTPDFReal_of_pos hν (neg_pos.mpr ht) (h.mp hint)
  · exact not_integrable_exp_mul_studentTPDFReal_of_pos hν ht hint

/-- The exponential integrand of a Student t law is integrable exactly at rate zero. -/
@[simp]
theorem integrable_exp_mul_id_studentTMeasure_iff (hν : 0 < ν) (t : ℝ) :
    Integrable (fun x : ℝ => Real.exp (t * x)) (studentTMeasure ν) ↔ t = 0 := by
  have : IsProbabilityMeasure (studentTMeasure ν) :=
    isProbabilityMeasure_studentTMeasure hν
  refine ⟨fun h => not_ne_iff.mp fun ht => not_integrable_exp_mul_id_studentTMeasure hν ht h,
    fun ht => ?_⟩
  subst t
  have h : (fun x : ℝ => Real.exp (0 * x)) = fun _ : ℝ => (1 : ℝ) := by
    funext x
    simp
  rw [h]
  exact integrable_const (1 : ℝ)

/-- The exponential-integrability domain of the identity under a Student t law is the singleton
`{0}`: every nonzero exponential moment diverges in the polynomial tails. -/
@[simp]
theorem integrableExpSet_id_studentTMeasure (hν : 0 < ν) :
    integrableExpSet id (studentTMeasure ν) = {0} := by
  ext t
  simpa [integrableExpSet, id_eq] using integrable_exp_mul_id_studentTMeasure_iff hν t


end Probability

end TauCeti

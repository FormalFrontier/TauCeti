/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.StudentT.WeightedIntegral
public import Mathlib.Probability.Moments.IntegrableExpMul
import TauCeti.Analysis.SpecialFunctions.Beta
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Exponential moments of Student's t law

The mean, variance and polynomial moment thresholds of the Student t distribution defined in
`TauCeti/Probability/Distributions/StudentT/Basic.lean` are proved there; the cumulative
distribution function is computed in `TauCeti/Probability/Distributions/StudentT/Cdf.lean`. This
file develops the *exponential* moments, together with the sharp non-integrability of the identity.
The density is even, and on the positive half-line the substitution `w = x ^ 2 / ν` turns every
weighted integral into Euler's second beta integral
`∫ w ^ (a - 1) * (1 + w) ^ (-(a + b)) = Β(a, b)`, so the weighted density is integrable there
exactly for `-1 < q < ν`; the exponential-moment statements read off that sharp threshold.

## Main results

* `not_integrable_id_studentTMeasure` — the sharp non-integrability of the identity at `ν ≤ 1`;
* `integrable_exp_mul_id_studentTMeasure_iff` — `exp (t · x)` is integrable exactly at `t = 0`;
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

/-- A Student t law presented as Lebesgue measure with the real-valued density: the
`withDensity` integrability bridge specialized to `studentTPDFReal`. -/
private lemma integrable_studentTMeasure_iff {f : ℝ → ℝ} (hν : 0 < ν) :
    Integrable f (studentTMeasure ν) ↔
      Integrable (fun x : ℝ => studentTPDFReal ν x * f x) := by
  have hpdf : studentTPDF ν = fun x => ENNReal.ofReal (studentTPDFReal ν x) := by
    funext x
    exact (studentTPDF_of_pos hν x).trans (by rw [studentTPDFReal_of_pos hν x])
  have hden : studentTMeasure ν =
      volume.withDensity (fun x : ℝ => ENNReal.ofReal (studentTPDFReal ν x)) := by
    rw [studentTMeasure, hpdf]
  rw [hden]
  exact integrable_withDensity_ofReal_iff (measurable_studentTPDFReal ν)
    (ae_of_all _ fun _ => studentTPDFReal_nonneg ν _)

/-! ### Sharp non-integrability of the identity

The integrability threshold `integrable_id_studentTMeasure_iff` is proved in
`TauCeti/Probability/Distributions/StudentT/Basic.lean`; the sharp failure at `ν ≤ 1` is its
contrapositive. -/

/-- The identity is not integrable under a Student t law with at most one degree of freedom:
the mean does not exist. -/
theorem not_integrable_id_studentTMeasure (hν0 : 0 < ν) (hν1 : ν ≤ 1) :
    ¬ Integrable id (studentTMeasure ν) := by
  rw [integrable_id_studentTMeasure_iff hν0]
  exact not_lt.mpr hν1

/-! ### Exponential moments -/

/-- The exponential of a nonzero multiple of the identity is not integrable under a Student t
law: if `exp (t * x)` and `exp (-t * x)` were both integrable, then every moment would be
finite, contradicting the sharp moment threshold `q < ν`. -/
theorem not_integrable_exp_mul_id_studentTMeasure (hν : 0 < ν) {t : ℝ} (ht : t ≠ 0) :
    ¬ Integrable (fun x : ℝ => Real.exp (t * x)) (studentTMeasure ν) := by
  intro hint
  -- reflection in the origin turns the rate `t` into `-t`
  have hmap : (studentTMeasure ν).map (fun x : ℝ => -x) = studentTMeasure ν :=
    studentTMeasure_map_neg ν
  have hkey : Integrable (fun y : ℝ => Real.exp (t * y))
      ((studentTMeasure ν).map (fun x : ℝ => -x)) := by
    rw [hmap]
    exact hint
  have hcomp : Integrable (fun x : ℝ => Real.exp (t * (-x))) (studentTMeasure ν) :=
    (integrable_map_measure hkey.aestronglyMeasurable measurable_neg.aemeasurable).mp hkey
  have hneg : Integrable (fun x : ℝ => Real.exp (-t * x)) (studentTMeasure ν) := by
    simpa [mul_neg] using hcomp
  -- both one-sided exponential moments would force every polynomial moment to be finite
  have hmom : Integrable (fun x : ℝ => |x| ^ ν) (studentTMeasure ν) :=
    integrable_rpow_abs_of_integrable_exp_mul ht hint hneg hν.le
  have hden : Integrable (fun x : ℝ => studentTPDFReal ν x * |x| ^ ν) :=
    (integrable_studentTMeasure_iff hν (f := fun x : ℝ => |x| ^ ν)).mp hmom
  have hIoi : IntegrableOn (fun x : ℝ => studentTPDFReal ν x * x ^ ν) (Ioi (0 : ℝ)) := by
    have h1 : IntegrableOn (fun x : ℝ => studentTPDFReal ν x * |x| ^ ν) (Ioi (0 : ℝ)) :=
      hden.integrableOn
    have h2 : ∀ x ∈ Ioi (0 : ℝ), studentTPDFReal ν x * |x| ^ ν = studentTPDFReal ν x * x ^ ν := by
      intro x hx
      have hx0 : 0 < x := hx
      have habs : |x| = x := abs_of_pos hx0
      rw [habs]
    exact h1.congr_fun h2 measurableSet_Ioi
  have hq : -1 < ν := by linarith
  have : ν < ν := (integrableOn_pow_mul_studentTPDFReal_Ioi_iff hν hq).mp hIoi
  linarith

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

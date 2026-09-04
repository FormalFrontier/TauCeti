/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Beta.Basic
public import TauCeti.Probability.Distributions.Gamma.Basic
import Mathlib.MeasureTheory.Function.Jacobian
import TauCeti.Probability.Distributions.PDFInstances

/-!
# Independent Gamma variables and the Beta distribution

This file studies the coordinate change

`(x, y) ↦ (x / (x + y), x + y)`

on the positive quadrant. Its inverse sends `(u, s)` to `(u * s, (1 - u) * s)` and has
Jacobian determinant `s`. Applied to two independent Gamma laws with a common rate, the change
of variables separates their ratio from their sum: the ratio is Beta-distributed, the sum is
Gamma-distributed, and the two are independent.

## Main result

* `TauCeti.map_div_add_prod_gammaMeasure` identifies the joint pushforward with the product of a
  Beta law and a Gamma law.
* `TauCeti.map_div_add_gammaMeasure` gives the Beta marginal.
* `TauCeti.indepFun_div_add_gammaMeasure` proves independence under the product Gamma law.
* `TauCeti.hasLaw_div_add_prod_gammaMeasure_of_indepFun`,
  `TauCeti.hasLaw_div_add_gammaMeasure_of_indepFun`, and
  `TauCeti.indepFun_div_add_of_hasLaw_gammaMeasure` transfer the conclusions to independent
  random variables.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  2nd ed., Wiley, 1995.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace TauCeti

/-! ### The Gamma--Beta coordinate change -/

/-- The positive quadrant on which the Gamma--Beta coordinate change is bijective. -/
def gammaBetaSource : Set (ℝ × ℝ) := Ioi 0 ×ˢ Ioi 0

/-- The product of the open unit interval and the positive half-line. -/
def gammaBetaTarget : Set (ℝ × ℝ) := Ioo 0 1 ×ˢ Ioi 0

/-- The ratio-and-sum coordinate map. -/
def gammaBetaMap (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.1 / (z.1 + z.2), z.1 + z.2)

/-- The inverse of the ratio-and-sum coordinate map. -/
def betaGammaMap (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.1 * z.2, (1 - z.1) * z.2)

/-- The ratio-and-sum coordinate map is measurable. -/
theorem measurable_gammaBetaMap : Measurable gammaBetaMap := by
  unfold gammaBetaMap
  fun_prop

/-- The inverse Gamma--Beta coordinate map is measurable. -/
theorem measurable_betaGammaMap : Measurable betaGammaMap := by
  unfold betaGammaMap
  fun_prop

/-- The inverse coordinate map sends the target region into the positive quadrant. -/
theorem betaGammaMap_mem_source {z : ℝ × ℝ} (hz : z ∈ gammaBetaTarget) :
    betaGammaMap z ∈ gammaBetaSource := by
  rcases z with ⟨u, s⟩
  simp only [gammaBetaTarget, gammaBetaSource, mem_prod, mem_Ioo, mem_Ioi,
    betaGammaMap] at hz ⊢
  exact ⟨mul_pos hz.1.1 hz.2, mul_pos (sub_pos.mpr hz.1.2) hz.2⟩

/-- The ratio-and-sum coordinate map sends the positive quadrant into its target region. -/
theorem gammaBetaMap_mem_target {z : ℝ × ℝ} (hz : z ∈ gammaBetaSource) :
    gammaBetaMap z ∈ gammaBetaTarget := by
  rcases z with ⟨x, y⟩
  simp only [gammaBetaSource, gammaBetaTarget, mem_prod, mem_Ioi, mem_Ioo,
    gammaBetaMap] at hz ⊢
  have hsum : 0 < x + y := add_pos hz.1 hz.2
  exact ⟨⟨div_pos hz.1 hsum, (div_lt_one hsum).2 (by linarith)⟩, hsum⟩

/-- The ratio-and-sum map is a left inverse to the inverse coordinate map on the target region. -/
theorem gammaBetaMap_betaGammaMap {z : ℝ × ℝ} (hz : z ∈ gammaBetaTarget) :
    gammaBetaMap (betaGammaMap z) = z := by
  rcases z with ⟨u, s⟩
  simp only [gammaBetaTarget, mem_prod, mem_Ioo, mem_Ioi] at hz
  have hs : s ≠ 0 := hz.2.ne'
  apply Prod.ext
  · simp only [gammaBetaMap, betaGammaMap]
    field_simp
    ring
  · simp only [gammaBetaMap, betaGammaMap]
    ring

/-- The inverse coordinate map is a left inverse to the ratio-and-sum map on the source region. -/
theorem betaGammaMap_gammaBetaMap {z : ℝ × ℝ} (hz : z ∈ gammaBetaSource) :
    betaGammaMap (gammaBetaMap z) = z := by
  rcases z with ⟨x, y⟩
  simp only [gammaBetaSource, mem_prod, mem_Ioi] at hz
  have hsum : x + y ≠ 0 := (add_pos hz.1 hz.2).ne'
  apply Prod.ext
  · simp only [gammaBetaMap, betaGammaMap]
    field_simp
  · simp only [gammaBetaMap, betaGammaMap]
    field_simp
    ring

/-- The inverse coordinate map sends the target region onto the positive quadrant. -/
theorem betaGammaMap_image_target :
    betaGammaMap '' gammaBetaTarget = gammaBetaSource := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact betaGammaMap_mem_source hz
  · intro z hz
    exact ⟨gammaBetaMap z, gammaBetaMap_mem_target hz, betaGammaMap_gammaBetaMap hz⟩

/-- The inverse coordinate map is injective on the target region. -/
theorem betaGammaMap_injOn : Set.InjOn betaGammaMap gammaBetaTarget := by
  intro z hz w hw hzw
  rw [← gammaBetaMap_betaGammaMap hz, ← gammaBetaMap_betaGammaMap hw, hzw]

/-- The derivative of the inverse Gamma--Beta coordinate map. -/
def fderivBetaGammaMap (z : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ)
    !![z.2, z.1; -z.2, 1 - z.1]).toContinuousLinearMap

/-- The stated continuous linear map is the derivative of the inverse coordinate map. -/
theorem hasFDerivAt_betaGammaMap (z : ℝ × ℝ) :
    HasFDerivAt betaGammaMap (fderivBetaGammaMap z) z := by
  have hfst : HasFDerivAt (fun q : ℝ × ℝ ↦ q.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) z := hasFDerivAt_fst
  have hsnd : HasFDerivAt (fun q : ℝ × ℝ ↦ q.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) z := hasFDerivAt_snd
  have hone : HasFDerivAt (fun _ : ℝ × ℝ ↦ (1 : ℝ))
      (0 : (ℝ × ℝ) →L[ℝ] ℝ) z := hasFDerivAt_const (𝕜 := ℝ) 1 z
  unfold fderivBetaGammaMap betaGammaMap
  rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
  convert! HasFDerivAt.prodMk (𝕜 := ℝ)
    (hfst.mul hsnd) ((hone.sub hfst).mul hsnd) using 2
  all_goals try simp only [Pi.sub_apply]
  all_goals module

/-- The Jacobian determinant of the inverse Gamma--Beta coordinate map is its second coordinate. -/
theorem det_fderivBetaGammaMap (z : ℝ × ℝ) :
    (fderivBetaGammaMap z).det = z.2 := by
  unfold fderivBetaGammaMap
  simp only [LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin,
    Matrix.det_fin_two_of]
  ring

/-- The Jacobian formula for the inverse coordinate change, expressed as an equality of restricted
Lebesgue measures. -/
theorem map_betaGammaMap_withDensity :
    Measure.map betaGammaMap
        ((volume.restrict gammaBetaTarget).withDensity fun z ↦ ENNReal.ofReal z.2) =
      volume.restrict gammaBetaSource := by
  let _ : Measure.IsAddHaarMeasure (volume : Measure (ℝ × ℝ)) :=
    Measure.prod.instIsAddHaarMeasure _ _
  have heq : (fun z : ℝ × ℝ ↦ ENNReal.ofReal z.2) =ᵐ[volume.restrict gammaBetaTarget]
      fun z ↦ ENNReal.ofReal |(fderivBetaGammaMap z).det| := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioi)] with z hz
    rw [det_fderivBetaGammaMap, abs_of_pos hz.2]
  rw [withDensity_congr_ae heq, ← betaGammaMap_image_target]
  exact map_withDensity_abs_det_fderiv_eq_addHaar volume
    (measurableSet_Ioo.prod measurableSet_Ioi).nullMeasurableSet
    (fun z _ ↦ (hasFDerivAt_betaGammaMap z).hasFDerivWithinAt) betaGammaMap_injOn

private theorem gammaBeta_density_real {a b r u s : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hr : 0 < r) (hu : 0 < u) (hu' : u < 1) (hs : 0 < s) :
    s * (gammaPDFReal a r (u * s) * gammaPDFReal b r ((1 - u) * s)) =
      betaPDFReal a b u * gammaPDFReal (a + b) r s := by
  rw [gammaPDFReal, gammaPDFReal, gammaPDFReal, betaPDFReal,
    ite_eq_left (mul_nonneg hu.le hs.le),
    ite_eq_left (mul_nonneg (sub_nonneg.mpr hu'.le) hs.le),
    ite_eq_left hs.le, ite_eq_left ⟨hu, hu'⟩, Real.mul_rpow hu.le hs.le,
    Real.mul_rpow (sub_nonneg.mpr hu'.le) hs.le]
  have hs_pow : s * s ^ (a - 1) * s ^ (b - 1) = s ^ (a + b - 1) := by
    calc
      s * s ^ (a - 1) * s ^ (b - 1) = s ^ (1 : ℝ) * s ^ (a - 1) * s ^ (b - 1) := by
        simp only [Real.rpow_one]
      _ = s ^ ((1 : ℝ) + (a - 1)) * s ^ (b - 1) := by
        rw [Real.rpow_add hs]
      _ = s ^ (((1 : ℝ) + (a - 1)) + (b - 1)) := by
        exact (Real.rpow_add hs _ _).symm
      _ = s ^ (a + b - 1) := by ring_nf
  rw [ProbabilityTheory.beta]
  rw [Real.rpow_add hr, ← hs_pow]
  field_simp [(Real.Gamma_pos_of_pos ha).ne', (Real.Gamma_pos_of_pos hb).ne',
    (Real.Gamma_pos_of_pos (add_pos ha hb)).ne']
  ring_nf
  calc
    Real.exp (-(s * r * u)) * (1 - u) ^ (-1 + b) * Real.exp (-(s * r) + s * r * u) =
        (1 - u) ^ (-1 + b) *
          (Real.exp (-(s * r * u)) * Real.exp (-(s * r) + s * r * u)) := by ring
    _ = (1 - u) ^ (-1 + b) * Real.exp (-(s * r)) := by
      rw [← Real.exp_add]
      congr 2
      ring

private theorem gammaBeta_density {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    {z : ℝ × ℝ} (hz : z ∈ gammaBetaTarget) :
    ENNReal.ofReal z.2 *
        (gammaPDF a r (betaGammaMap z).1 * gammaPDF b r (betaGammaMap z).2) =
      betaPDF a b z.1 * gammaPDF (a + b) r z.2 := by
  rcases z with ⟨u, s⟩
  simp only [gammaBetaTarget, mem_prod, mem_Ioo, mem_Ioi] at hz
  simp only [gammaPDF, betaPDF, betaGammaMap]
  rw [← ENNReal.ofReal_mul (gammaPDFReal_nonneg ha hr _),
    ← ENNReal.ofReal_mul hz.2.le,
    ← ENNReal.ofReal_mul (betaPDFReal_nonneg ha hb _),
    gammaBeta_density_real ha hb hr hz.1.1 hz.1.2 hz.2]

private def gammaGammaPDF (a b r : ℝ) (z : ℝ × ℝ) : ℝ≥0∞ :=
  gammaPDF a r z.1 * gammaPDF b r z.2

private def betaGammaPDF (a b r : ℝ) (z : ℝ × ℝ) : ℝ≥0∞ :=
  betaPDF a b z.1 * gammaPDF (a + b) r z.2

private theorem measurable_gammaGammaPDF (a b r : ℝ) : Measurable (gammaGammaPDF a b r) := by
  unfold gammaGammaPDF
  exact ((Probability.measurable_gammaPDF a r).comp measurable_fst).mul
    ((Probability.measurable_gammaPDF b r).comp measurable_snd)

private theorem prod_gammaMeasure_eq_withDensity (a b r : ℝ) :
    (gammaMeasure a r).prod (gammaMeasure b r) =
      volume.withDensity (gammaGammaPDF a b r) := by
  simp only [gammaMeasure]
  rw [prod_withDensity (Probability.measurable_gammaPDF a r)
    (Probability.measurable_gammaPDF b r), ← Measure.volume_eq_prod]
  rfl

private theorem prod_beta_gammaMeasure_eq_withDensity (a b r : ℝ) :
    (betaMeasure a b).prod (gammaMeasure (a + b) r) =
      volume.withDensity (betaGammaPDF a b r) := by
  rw [betaMeasure, gammaMeasure,
    prod_withDensity (Probability.measurable_betaPDF a b)
      (Probability.measurable_gammaPDF (a + b) r), ← Measure.volume_eq_prod]
  rfl

private theorem ae_mem_gammaBetaSource {a b r : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hr : 0 < r) :
    ∀ᵐ z ∂(gammaMeasure a r).prod (gammaMeasure b r), z ∈ gammaBetaSource := by
  let _ := isProbabilityMeasure_gammaMeasure ha hr
  let _ := isProbabilityMeasure_gammaMeasure hb hr
  unfold gammaBetaSource
  rw [Measure.ae_prod_mem_iff_ae_ae_mem (measurableSet_Ioi.prod measurableSet_Ioi)]
  filter_upwards [ae_pos_gammaMeasure a r] with x hx
  filter_upwards [ae_pos_gammaMeasure b r] with y hy
  exact ⟨hx, hy⟩

private theorem ae_mem_gammaBetaTarget {a b r : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hr : 0 < r) :
    ∀ᵐ z ∂(betaMeasure a b).prod (gammaMeasure (a + b) r), z ∈ gammaBetaTarget := by
  let _ := isProbabilityMeasureBeta ha hb
  let _ := isProbabilityMeasure_gammaMeasure (add_pos ha hb) hr
  unfold gammaBetaTarget
  rw [Measure.ae_prod_mem_iff_ae_ae_mem (measurableSet_Ioo.prod measurableSet_Ioi)]
  filter_upwards [ae_mem_Ioo_betaMeasure a b] with u hu
  filter_upwards [ae_pos_gammaMeasure (a + b) r] with s hs
  exact ⟨hu, hs⟩

private theorem map_betaGammaMap_prod_beta_gamma {a b r : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hr : 0 < r) :
    Measure.map betaGammaMap ((betaMeasure a b).prod (gammaMeasure (a + b) r)) =
      (gammaMeasure a r).prod (gammaMeasure b r) := by
  let _ := isProbabilityMeasureBeta ha hb
  let _ := isProbabilityMeasure_gammaMeasure (add_pos ha hb) hr
  let _ := isProbabilityMeasure_gammaMeasure ha hr
  let _ := isProbabilityMeasure_gammaMeasure hb hr
  rw [← Measure.restrict_eq_self_of_ae_mem (ae_mem_gammaBetaTarget ha hb hr),
    ← Measure.restrict_eq_self_of_ae_mem (ae_mem_gammaBetaSource ha hb hr),
    prod_beta_gammaMeasure_eq_withDensity, prod_gammaMeasure_eq_withDensity]
  unfold gammaBetaTarget gammaBetaSource
  rw [restrict_withDensity (measurableSet_Ioo.prod measurableSet_Ioi),
    restrict_withDensity (measurableSet_Ioi.prod measurableSet_Ioi)]
  ext q hq
  rw [Measure.map_apply measurable_betaGammaMap hq,
    withDensity_apply _ (measurable_betaGammaMap hq), withDensity_apply _ hq]
  rw [← lintegral_indicator (measurable_betaGammaMap hq), ← lintegral_indicator hq]
  calc
    ∫⁻ z in gammaBetaTarget, (betaGammaMap ⁻¹' q).indicator (betaGammaPDF a b r) z =
        ∫⁻ z in gammaBetaTarget, ENNReal.ofReal z.2 *
          (q.indicator (gammaGammaPDF a b r)) (betaGammaMap z) := by
      refine setLIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioi) fun z hz ↦ ?_
      by_cases hzq : betaGammaMap z ∈ q
      · have hzq' : z ∈ betaGammaMap ⁻¹' q := hzq
        rw [indicator_of_mem hzq', indicator_of_mem hzq]
        unfold betaGammaPDF gammaGammaPDF
        exact (gammaBeta_density ha hb hr hz).symm
      · have hzq' : z ∉ betaGammaMap ⁻¹' q := hzq
        rw [indicator_of_notMem hzq', indicator_of_notMem hzq, mul_zero]
    _ = ∫⁻ z, q.indicator (gammaGammaPDF a b r) z ∂Measure.map betaGammaMap
          ((volume.restrict gammaBetaTarget).withDensity fun z ↦ ENNReal.ofReal z.2) := by
      have hf := (measurable_gammaGammaPDF a b r).indicator hq
      have hcomp : Measurable (fun z ↦
          q.indicator (gammaGammaPDF a b r) (betaGammaMap z)) :=
        hf.comp measurable_betaGammaMap
      rw [lintegral_map hf measurable_betaGammaMap,
        lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hcomp]
      rfl
    _ = ∫⁻ z in gammaBetaSource, q.indicator (gammaGammaPDF a b r) z := by
      rw [map_betaGammaMap_withDensity]

/-! ### Independent Gamma variables -/

/-- The ratio and sum of two independent Gamma variables with the same positive rate have the
product law `betaMeasure a b ⊗ gammaMeasure (a + b) r`. In particular, the ratio and sum are
independent. The denominator-zero branch of the ratio is irrelevant because both Gamma variables
are strictly positive almost surely. -/
theorem map_div_add_prod_gammaMeasure {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    ((gammaMeasure a r).prod (gammaMeasure b r)).map
        (fun z ↦ (z.1 / (z.1 + z.2), z.1 + z.2)) =
      (betaMeasure a b).prod (gammaMeasure (a + b) r) := by
  let _ := isProbabilityMeasureBeta ha hb
  let _ := isProbabilityMeasure_gammaMeasure (add_pos ha hb) hr
  have hmap : (fun z : ℝ × ℝ ↦ (z.1 / (z.1 + z.2), z.1 + z.2)) = gammaBetaMap := by
    funext z
    simp only [gammaBetaMap]
  rw [hmap, ← map_betaGammaMap_prod_beta_gamma ha hb hr,
    Measure.map_map measurable_gammaBetaMap measurable_betaGammaMap]
  calc
    Measure.map (gammaBetaMap ∘ betaGammaMap)
        ((betaMeasure a b).prod (gammaMeasure (a + b) r)) =
        Measure.map id ((betaMeasure a b).prod (gammaMeasure (a + b) r)) := by
      apply Measure.map_congr
      filter_upwards [ae_mem_gammaBetaTarget ha hb hr] with z hz
      exact gammaBetaMap_betaGammaMap hz
    _ = (betaMeasure a b).prod (gammaMeasure (a + b) r) := Measure.map_id

/-- The ratio of two independent Gamma variables with a common positive rate has a Beta law. -/
theorem map_div_add_gammaMeasure {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    ((gammaMeasure a r).prod (gammaMeasure b r)).map
        (fun z ↦ z.1 / (z.1 + z.2)) = betaMeasure a b := by
  let _ := isProbabilityMeasure_gammaMeasure (add_pos ha hb) hr
  have h := congrArg (Measure.map Prod.fst) (map_div_add_prod_gammaMeasure ha hb hr)
  rw [Measure.map_map measurable_fst (by fun_prop)] at h
  simpa only [Function.comp_def, Measure.map_fst_prod, measure_univ, one_smul] using h

/-- Under the product of two Gamma laws with a common positive rate, the ratio is independent of
the sum. -/
theorem indepFun_div_add_gammaMeasure {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    IndepFun (fun z : ℝ × ℝ ↦ z.1 / (z.1 + z.2)) (fun z ↦ z.1 + z.2)
      ((gammaMeasure a r).prod (gammaMeasure b r)) := by
  let _ := isProbabilityMeasure_gammaMeasure ha hr
  let _ := isProbabilityMeasure_gammaMeasure hb hr
  have hsum : ((gammaMeasure a r).prod (gammaMeasure b r)).map
      (fun z ↦ z.1 + z.2) = gammaMeasure (a + b) r := by
    exact gammaMeasure_conv_gammaMeasure ha hb hr
  refine (indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)).2 ?_
  rw [map_div_add_prod_gammaMeasure ha hb hr, map_div_add_gammaMeasure ha hb hr, hsum]

/-- For independent Gamma variables with a common positive rate, the pair consisting of their
ratio and their sum has the product of a Beta law and a Gamma law. -/
theorem hasLaw_div_add_prod_gammaMeasure_of_indepFun
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y : Ω → ℝ}
    {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (hXY : IndepFun X Y P)
    (hX : HasLaw X (gammaMeasure a r) P) (hY : HasLaw Y (gammaMeasure b r) P) :
    HasLaw (fun ω ↦ (X ω / (X ω + Y ω), X ω + Y ω))
      ((betaMeasure a b).prod (gammaMeasure (a + b) r)) P := by
  let _ := isProbabilityMeasure_gammaMeasure ha hr
  let _ := isProbabilityMeasure_gammaMeasure hb hr
  let _ : IsProbabilityMeasure P := hX.isProbabilityMeasure
  have hpair : HasLaw (fun ω ↦ (X ω, Y ω))
      ((gammaMeasure a r).prod (gammaMeasure b r)) P := hXY.hasLaw_prod hX hY
  have hmap : HasLaw gammaBetaMap
      ((betaMeasure a b).prod (gammaMeasure (a + b) r))
      ((gammaMeasure a r).prod (gammaMeasure b r)) :=
    ⟨measurable_gammaBetaMap.aemeasurable, map_div_add_prod_gammaMeasure ha hb hr⟩
  simpa only [gammaBetaMap, Function.comp_def] using hmap.fun_comp hpair

/-- The ratio of independent Gamma random variables with a common positive rate has a Beta law. -/
theorem hasLaw_div_add_gammaMeasure_of_indepFun
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y : Ω → ℝ}
    {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (hXY : IndepFun X Y P)
    (hX : HasLaw X (gammaMeasure a r) P) (hY : HasLaw Y (gammaMeasure b r) P) :
    HasLaw (fun ω ↦ X ω / (X ω + Y ω)) (betaMeasure a b) P := by
  let _ := isProbabilityMeasure_gammaMeasure ha hr
  let _ := isProbabilityMeasure_gammaMeasure hb hr
  let _ : IsProbabilityMeasure P := hX.isProbabilityMeasure
  have hpair : HasLaw (fun ω ↦ (X ω, Y ω))
      ((gammaMeasure a r).prod (gammaMeasure b r)) P := hXY.hasLaw_prod hX hY
  have hratio : HasLaw (fun z : ℝ × ℝ ↦ z.1 / (z.1 + z.2)) (betaMeasure a b)
      ((gammaMeasure a r).prod (gammaMeasure b r)) :=
    ⟨by fun_prop, map_div_add_gammaMeasure ha hb hr⟩
  exact hratio.fun_comp hpair

/-- The ratio and sum of independent Gamma random variables with a common positive rate are
independent. -/
theorem indepFun_div_add_of_hasLaw_gammaMeasure
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y : Ω → ℝ}
    {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (hXY : IndepFun X Y P)
    (hX : HasLaw X (gammaMeasure a r) P) (hY : HasLaw Y (gammaMeasure b r) P) :
    IndepFun (fun ω ↦ X ω / (X ω + Y ω)) (fun ω ↦ X ω + Y ω) P := by
  let _ := isProbabilityMeasure_gammaMeasure ha hr
  let _ := isProbabilityMeasure_gammaMeasure hb hr
  let _ := isProbabilityMeasureBeta ha hb
  let _ := isProbabilityMeasure_gammaMeasure (add_pos ha hb) hr
  let _ : IsProbabilityMeasure P := hX.isProbabilityMeasure
  have hjoint := hasLaw_div_add_prod_gammaMeasure_of_indepFun ha hb hr hXY hX hY
  have hratio := hasLaw_div_add_gammaMeasure_of_indepFun ha hb hr hXY hX hY
  have hsum : HasLaw (fun ω ↦ X ω + Y ω) (gammaMeasure (a + b) r) P := by
    have hsnd : HasLaw Prod.snd (gammaMeasure (a + b) r)
        ((betaMeasure a b).prod (gammaMeasure (a + b) r)) :=
      MeasureTheory.measurePreserving_snd.hasLaw
    simpa only [Function.comp_def] using hsnd.fun_comp hjoint
  exact (indepFun_iff_hasLaw_prodMk_prod hratio hsum).2 hjoint

end TauCeti

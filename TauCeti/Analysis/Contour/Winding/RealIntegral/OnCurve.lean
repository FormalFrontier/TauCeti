/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Contour.Winding.RealIntegral.Basic
public import TauCeti.Analysis.Contour.PwC1ImmersionOn
import TauCeti.Analysis.Contour.Crossing.Finiteness
import TauCeti.Analysis.Contour.Crossing.PVAggregation
import TauCeti.Analysis.Contour.Crossing.Windows
import TauCeti.Analysis.Contour.InvSubCPVExistence
import TauCeti.Analysis.Contour.PerWindow.CPV
import TauCeti.Analysis.Contour.Winding.LipschitzBoundedIntegrand
import TauCeti.Analysis.Contour.Winding.PrincipalValueRealIntegral
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# The real bounded-integrand formula for the winding number, allowing crossings

Hungerbühler–Wasem Proposition 2.3 evaluates the generalized winding number by the real,
non-principal-value integral

`n_s(γ) = (1 / 2π) ∫_a^b (x ẏ - y ẋ) / (x² + y²) dt`, `x + i y = γ - s`,

for a closed piecewise-`C¹` immersion `γ`. `Winding.RealIntegral.Basic` proves this when `γ`
avoids `s` throughout, where the winding number is already a genuine integer. This file drops
that avoidance hypothesis: `s` may be a value of `γ`, so long as every parameter where `γ` meets
`s` is interior to `[a, b]`. The generalized winding number is then a genuine Cauchy principal
value rather than an ordinary index integral, and this theorem shows it is still real and equal
to the same bounded real integral. Unlike the avoiding case, interval-integrability of that
integral is not assumed here: it is derived from the crossing regularity, the same `C^{1,1}`
hypothesis this file's boundedness result needs. (That hypothesis is satisfied vacuously when `γ`
never meets `s`, so this also reproves the avoiding case, but the two are kept as separate
theorems since their proofs are unrelated.)

This bundles two independent facts about the single-point Cauchy principal value
`L := 2πi · n_s(γ)` of the Cauchy kernel `(z - s)⁻¹` along `γ`:

* **Reality** (`Re L = 0`): the real part of the truncated index integral telescopes to
  `Real.log ‖γ b - s‖ - Real.log ‖γ a - s‖` regardless of any branch-cut/slit-plane data — the
  real part of `Complex.log` never depends on a branch — and this vanishes by closedness.
* **The integral identity** (`Im L = ∫ h`, `h` the real winding integrand): supplied directly by
  `HasCauchyPVAt.im_eq_integral_realWindingIntegrand`, since `h` is interval-integrable.

Both facts are read off the *same* explicit principal-value witness, built by
`Crossing.PVAggregation`'s per-window aggregation from the plain (avoiding) pieces and the
per-crossing windows along the sorted crossing list.

## Main results

* `TauCeti.Contour.windingNumber_eq_real_integral_of_closed_of_interior_crossings` — the real
  bounded-integrand formula for a closed immersion whose crossings of `s`, if any, are interior.

## Provenance

New assembly for this roadmap target (HW Prop 2.3), built from existing Tau Ceti
contour-integration infrastructure: the per-crossing window value
(`exists_radius_perWindow_tendsto_value`), the existence-and-real-part aggregation
(`hasCauchyPVAt_of_perWindow_tendsto_of_interiorDisjoint_re_boundary`), and the integral-identity
bridge (`HasCauchyPVAt.im_eq_integral_realWindingIntegrand`). This file's own content is the
log-norm derivative machinery (feeding the real-part telescoping hypothesis of the aggregation
theorem) and the assembly of the above into the final formula; the per-crossing-window
construction and its real/imaginary-part facts are proved once, generically, in
`Crossing.PVAggregation` rather than re-derived here.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997 — Proposition 2.3.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Set Topology intervalIntegral

open scoped Interval NNReal

namespace TauCeti.Contour

/-! ### The real part of a complex derivative along the real embeddings -/

/-- The derivative of the squared complex modulus, in the real-parameter chain-rule form used to
differentiate the log-norm below. An instance of Mathlib's generic inner-product-space
squared-norm derivative rule (`HasDerivAt.norm_sq`), rewritten from `⟪·,·⟫_ℝ` to `Complex.normSq`
via `Complex.inner` and `Complex.normSq_eq_norm_sq`. -/
private theorem hasDerivAt_normSq {f : ℝ → ℂ} {t : ℝ} {D : ℂ} (hf : HasDerivAt f D t) :
    HasDerivAt (fun u => Complex.normSq (f u)) (2 * ((starRingEnd ℂ (f t) * D).re)) t := by
  simpa [Complex.normSq_eq_norm_sq, Complex.inner, mul_comm] using HasDerivAt.norm_sq hf

/-- **The log-norm derivative.** Wherever a real-parametrized curve is differentiable and avoids
`0`, the real-valued function `t ↦ Real.log ‖f t‖` is differentiable, with derivative the real
part of the index integrand `(f t)⁻¹ * deriv f t` — unconditionally, with no slit-plane or branch
data: `Complex.log`'s real part `Real.log ∘ norm` never depends on a choice of branch. -/
private theorem hasDerivAt_log_norm {f : ℝ → ℂ} {t : ℝ} {D : ℂ} (hf : HasDerivAt f D t)
    (hne : f t ≠ 0) :
    HasDerivAt (fun u => Real.log ‖f u‖) (((f t)⁻¹ * D).re) t := by
  have hnsq := hasDerivAt_normSq hf
  have hnsq_pos : (0 : ℝ) < Complex.normSq (f t) := Complex.normSq_pos.mpr hne
  have hlog : HasDerivAt (fun u => Real.log (Complex.normSq (f u)))
      ((Complex.normSq (f t))⁻¹ * (2 * ((starRingEnd ℂ (f t) * D).re))) t :=
    HasDerivAt.comp t (Real.hasDerivAt_log hnsq_pos.ne') hnsq
  have hval : ((Complex.normSq (f t))⁻¹ * (2 * ((starRingEnd ℂ (f t) * D).re)))
      = 2 * (((f t)⁻¹ * D).re) := by
    have hre : ((f t)⁻¹ * D).re = (Complex.normSq (f t))⁻¹ * (starRingEnd ℂ (f t) * D).re := by
      have hrw : (f t)⁻¹ * D = ((Complex.normSq (f t) : ℝ)⁻¹ : ℂ) * (starRingEnd ℂ (f t) * D) := by
        rw [Complex.inv_def]; push_cast; ring
      rw [hrw, ← Complex.ofReal_inv, Complex.re_ofReal_mul]
    rw [hre]; ring
  rw [hval] at hlog
  have hdiv := hlog.div_const 2
  have heq2 : (fun u => Real.log (Complex.normSq (f u)) / 2) = fun u => Real.log ‖f u‖ := by
    funext u
    rw [Complex.norm_def, Real.log_sqrt (Complex.normSq_nonneg _)]
  rw [heq2] at hdiv
  have hval2 : 2 * (((f t)⁻¹ * D).re) / 2 = ((f t)⁻¹ * D).re := by ring
  rwa [hval2] at hdiv

/-- **The real part of the plain-piece contour integral telescopes to the log-norm difference of
its endpoints**, with no slit-plane hypothesis needed: the real part of `Complex.log` never
depends on a branch, unlike its imaginary part (the argument), which is exactly the content the
generalized winding number keeps track of. -/
private theorem re_integral_inv_sub_mul_deriv_eq_log_norm {γ : ℝ → ℂ} {s : ℂ} {l u : ℝ}
    {P : Set ℝ} (hlu : l ≤ u) (hP : P.Countable) (hγ_cont : ContinuousOn γ (Icc l u))
    (hγ_diff : ∀ t ∈ Ioo l u \ P, DifferentiableAt ℝ γ t) (h_ne : ∀ t ∈ Icc l u, γ t ≠ s)
    (h_int : IntervalIntegrable (fun t => (γ t - s)⁻¹ * deriv γ t) volume l u) :
    (∫ t in l..u, (γ t - s)⁻¹ * deriv γ t).re = Real.log ‖γ u - s‖ - Real.log ‖γ l - s‖ := by
  have hγ_cont' : ContinuousOn γ [[l, u]] := by rwa [uIcc_of_le hlu]
  have h_ne' : ∀ t ∈ [[l, u]], γ t - s ≠ 0 := fun t ht =>
    sub_ne_zero.mpr (h_ne t (by rwa [uIcc_of_le hlu] at ht))
  have hcont : ContinuousOn (fun t => Real.log ‖γ t - s‖) [[l, u]] := fun t ht => by
    have h2 : ContinuousWithinAt (fun t => ‖γ t - s‖) [[l, u]] t :=
      ((hγ_cont' t ht).sub continuousWithinAt_const).norm
    exact (Real.continuousAt_log (norm_ne_zero_iff.mpr (h_ne' t ht))).tendsto.comp h2
  have hderiv : ∀ t ∈ Ioo (min l u) (max l u) \ P,
      HasDerivAt (fun t => Real.log ‖γ t - s‖) (((γ t - s)⁻¹ * deriv γ t).re) t := by
    intro t ht
    rw [min_eq_left hlu, max_eq_right hlu] at ht
    have hγt : DifferentiableAt ℝ γ t := hγ_diff t ht
    have hγt' : HasDerivAt (fun t => γ t - s) (deriv γ t) t := hγt.hasDerivAt.sub_const s
    have hne_t : γ t - s ≠ 0 := sub_ne_zero.mpr (h_ne t (Ioo_subset_Icc_self ht.1))
    exact hasDerivAt_log_norm hγt' hne_t
  have hint_re : IntervalIntegrable (fun t => ((γ t - s)⁻¹ * deriv γ t).re) volume l u :=
    ⟨h_int.1.re, h_int.2.re⟩
  have hFTC := integral_eq_of_hasDerivAt_off_countable
    (fun t => Real.log ‖γ t - s‖) (fun t => ((γ t - s)⁻¹ * deriv γ t).re) hP hcont hderiv hint_re
  rw [← RCLike.re_to_complex, ← intervalIntegral_re h_int]
  simpa only [RCLike.re_to_complex] using hFTC

/-! ### Interval-integrability of the real winding integrand, allowing crossings -/

/-- **The real winding integrand is interval-integrable on a small enough right-window at a
`C^{1,1}` crossing, from the right.** Bounded on a window of radius `ρ_lip ≤ ε_D`
(`exists_isBounded_image_realWindingIntegrand_of_lipschitzOnWith_derivWithin_right`), shrunk
further to any `ρ ≤ ρ_lip`, and measurable: `γ` and `derivWithin γ (Icc t₀ (t₀ + εD))` are
continuous throughout `[t₀, t₀ + ρ]`, agreeing with `deriv γ` off the single point `t₀` (measure
zero, so invisible to a.e. strong measurability), so `(γ · - s)⁻¹ * deriv γ` is a.e. strongly
measurable there, exactly as in `intervalIntegrable_inv_sub_truncated`, without needing an
avoidance hypothesis or the two sides of the crossing to agree. -/
private theorem intervalIntegrable_realWindingIntegrand_window_right {γ : ℝ → ℂ} {s : ℂ}
    {t₀ ρ ρ_lip εD : ℝ} (hρ_pos : 0 < ρ) (hρ_le_ρlip : ρ ≤ ρ_lip) (hρlip_le_εD : ρ_lip ≤ εD)
    (hC1 : ContDiffOn ℝ 1 γ (Icc t₀ (t₀ + εD)))
    (hbdd : Bornology.IsBounded
      ((fun t => realWindingIntegrand (γ t - s) (deriv γ t)) '' Icc t₀ (t₀ + ρ_lip))) :
    IntervalIntegrable (fun t => realWindingIntegrand (γ t - s) (deriv γ t)) volume
      t₀ (t₀ + ρ) := by
  have hsub_lip : Icc t₀ (t₀ + ρ) ⊆ Icc t₀ (t₀ + ρ_lip) := Icc_subset_Icc le_rfl (by linarith)
  have hsub_εD : Icc t₀ (t₀ + ρ) ⊆ Icc t₀ (t₀ + εD) := Icc_subset_Icc le_rfl (by linarith)
  obtain ⟨C, hC⟩ := (hbdd.subset (Set.image_mono hsub_lip)).exists_norm_le
  have hγc : ContinuousOn γ (Icc t₀ (t₀ + ρ)) := hC1.continuousOn.mono hsub_εD
  have hdw : ContinuousOn (derivWithin γ (Icc t₀ (t₀ + εD))) (Icc t₀ (t₀ + ρ)) :=
    (hC1.continuousOn_derivWithin (uniqueDiffOn_Icc (by linarith)) le_rfl).mono hsub_εD
  have huIoc_eq : uIoc t₀ (t₀ + ρ) = Ioc t₀ (t₀ + ρ) := uIoc_of_le (by linarith)
  have huIoc_sub : uIoc t₀ (t₀ + ρ) ⊆ Icc t₀ (t₀ + ρ) :=
    (uIoc_subset_uIcc).trans (by rw [uIcc_of_le (by linarith : t₀ ≤ t₀ + ρ)])
  have haesm : AEStronglyMeasurable (fun t => (γ t - s)⁻¹ * derivWithin γ (Icc t₀ (t₀ + εD)) t)
      (volume.restrict (uIoc t₀ (t₀ + ρ))) := by
    have hγ_aem : AEMeasurable γ (volume.restrict (uIoc t₀ (t₀ + ρ))) :=
      ((hγc.aestronglyMeasurable measurableSet_Icc).mono_measure
        (Measure.restrict_mono huIoc_sub le_rfl)).aemeasurable
    have hd_aem : AEMeasurable (derivWithin γ (Icc t₀ (t₀ + εD)))
        (volume.restrict (uIoc t₀ (t₀ + ρ))) :=
      ((hdw.aestronglyMeasurable measurableSet_Icc).mono_measure
        (Measure.restrict_mono huIoc_sub le_rfl)).aemeasurable
    exact ((hγ_aem.sub_const s).inv.mul hd_aem).aestronglyMeasurable
  have haesm_h : AEStronglyMeasurable
      (fun t => realWindingIntegrand (γ t - s) (derivWithin γ (Icc t₀ (t₀ + εD)) t))
      (volume.restrict (uIoc t₀ (t₀ + ρ))) := by
    refine (Complex.imCLM.continuous.comp_aestronglyMeasurable haesm).congr
      (MeasureTheory.ae_of_all _ fun t => ?_)
    simp only [Complex.imCLM_apply, realWindingIntegrand_def]
  have hcongr : (fun t => realWindingIntegrand (γ t - s) (deriv γ t))
      =ᶠ[ae (volume.restrict (uIoc t₀ (t₀ + ρ)))]
      (fun t => realWindingIntegrand (γ t - s) (derivWithin γ (Icc t₀ (t₀ + εD)) t)) := by
    rw [huIoc_eq, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
    congr 1
    exact (derivWithin_of_mem_nhds (Icc_mem_nhds (by linarith [ht.1]) (by linarith [ht.2]))).symm
  have haesm_h' : AEStronglyMeasurable (fun t => realWindingIntegrand (γ t - s) (deriv γ t))
      (volume.restrict (uIoc t₀ (t₀ + ρ))) := haesm_h.congr hcongr.symm
  rw [intervalIntegrable_iff]
  have : IsFiniteMeasure (volume.restrict (uIoc t₀ (t₀ + ρ))) :=
    isFiniteMeasure_restrict.mpr ((measure_mono uIoc_subset_uIcc).trans_lt
      (by rw [uIcc_of_le (by linarith : t₀ ≤ t₀ + ρ)]
          exact isCompact_Icc.measure_lt_top)).ne
  refine Integrable.of_bound haesm_h' C ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with t ht
  exact hC _ ⟨t, huIoc_sub ht, rfl⟩

/-- **The real winding integrand is interval-integrable on a small enough left-window at a
`C^{1,1}` crossing, from the left.** The left-hand mirror of
`intervalIntegrable_realWindingIntegrand_window_right`. -/
private theorem intervalIntegrable_realWindingIntegrand_window_left {γ : ℝ → ℂ} {s : ℂ}
    {t₀ ρ ρ_lip εD : ℝ} (hρ_pos : 0 < ρ) (hρ_le_ρlip : ρ ≤ ρ_lip) (hρlip_le_εD : ρ_lip ≤ εD)
    (hC1 : ContDiffOn ℝ 1 γ (Icc (t₀ - εD) t₀))
    (hbdd : Bornology.IsBounded
      ((fun t => realWindingIntegrand (γ t - s) (deriv γ t)) '' Icc (t₀ - ρ_lip) t₀)) :
    IntervalIntegrable (fun t => realWindingIntegrand (γ t - s) (deriv γ t)) volume
      (t₀ - ρ) t₀ := by
  have hsub_lip : Icc (t₀ - ρ) t₀ ⊆ Icc (t₀ - ρ_lip) t₀ := Icc_subset_Icc (by linarith) le_rfl
  have hsub_εD : Icc (t₀ - ρ) t₀ ⊆ Icc (t₀ - εD) t₀ := Icc_subset_Icc (by linarith) le_rfl
  obtain ⟨C, hC⟩ := (hbdd.subset (Set.image_mono hsub_lip)).exists_norm_le
  have hγc : ContinuousOn γ (Icc (t₀ - ρ) t₀) := hC1.continuousOn.mono hsub_εD
  have hdw : ContinuousOn (derivWithin γ (Icc (t₀ - εD) t₀)) (Icc (t₀ - ρ) t₀) :=
    (hC1.continuousOn_derivWithin (uniqueDiffOn_Icc (by linarith)) le_rfl).mono hsub_εD
  have huIoc_eq : uIoc (t₀ - ρ) t₀ = Ioc (t₀ - ρ) t₀ := uIoc_of_le (by linarith)
  have huIoc_sub : uIoc (t₀ - ρ) t₀ ⊆ Icc (t₀ - ρ) t₀ :=
    (uIoc_subset_uIcc).trans (by rw [uIcc_of_le (by linarith : t₀ - ρ ≤ t₀)])
  have haesm : AEStronglyMeasurable (fun t => (γ t - s)⁻¹ * derivWithin γ (Icc (t₀ - εD) t₀) t)
      (volume.restrict (uIoc (t₀ - ρ) t₀)) := by
    have hγ_aem : AEMeasurable γ (volume.restrict (uIoc (t₀ - ρ) t₀)) :=
      ((hγc.aestronglyMeasurable measurableSet_Icc).mono_measure
        (Measure.restrict_mono huIoc_sub le_rfl)).aemeasurable
    have hd_aem : AEMeasurable (derivWithin γ (Icc (t₀ - εD) t₀))
        (volume.restrict (uIoc (t₀ - ρ) t₀)) :=
      ((hdw.aestronglyMeasurable measurableSet_Icc).mono_measure
        (Measure.restrict_mono huIoc_sub le_rfl)).aemeasurable
    exact ((hγ_aem.sub_const s).inv.mul hd_aem).aestronglyMeasurable
  have haesm_h : AEStronglyMeasurable
      (fun t => realWindingIntegrand (γ t - s) (derivWithin γ (Icc (t₀ - εD) t₀) t))
      (volume.restrict (uIoc (t₀ - ρ) t₀)) := by
    refine (Complex.imCLM.continuous.comp_aestronglyMeasurable haesm).congr
      (MeasureTheory.ae_of_all _ fun t => ?_)
    simp only [Complex.imCLM_apply, realWindingIntegrand_def]
  have hcongr : (fun t => realWindingIntegrand (γ t - s) (deriv γ t))
      =ᶠ[ae (volume.restrict (uIoc (t₀ - ρ) t₀))]
      (fun t => realWindingIntegrand (γ t - s) (derivWithin γ (Icc (t₀ - εD) t₀) t)) := by
    rw [huIoc_eq, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
    congr 1
    exact (derivWithin_of_mem_nhds (Icc_mem_nhds (by linarith [ht.1]) (by linarith [ht.2]))).symm
  have haesm_h' : AEStronglyMeasurable (fun t => realWindingIntegrand (γ t - s) (deriv γ t))
      (volume.restrict (uIoc (t₀ - ρ) t₀)) := haesm_h.congr hcongr.symm
  rw [intervalIntegrable_iff]
  have : IsFiniteMeasure (volume.restrict (uIoc (t₀ - ρ) t₀)) :=
    isFiniteMeasure_restrict.mpr ((measure_mono uIoc_subset_uIcc).trans_lt
      (by rw [uIcc_of_le (by linarith : t₀ - ρ ≤ t₀)]
          exact isCompact_Icc.measure_lt_top)).ne
  refine Integrable.of_bound haesm_h' C ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with t ht
  exact hC _ ⟨t, huIoc_sub ht, rfl⟩

/-- **Gluing interval-integrability of the real winding integrand along the sorted crossing
list.** An instance of `sorted_crossing_gluing_aux`: only needs `IntervalIntegrable.trans` to
concatenate plain pieces with windows — no limiting value to track. -/
private theorem intervalIntegrable_along_sorted {γ : ℝ → ℂ} {s : ℂ} {A b r m : ℝ}
    (h_piece : ∀ l u : ℝ, A ≤ l → l ≤ u → u ≤ b → (∀ t ∈ Icc l u, m ≤ ‖γ t - s‖) →
      IntervalIntegrable (fun t => realWindingIntegrand (γ t - s) (deriv γ t)) volume l u) :
    ∀ (sorted : List ℝ), sorted.SortedLT → (sorted ≠ [] → 0 ≤ r) →
    ∀ a : ℝ, A ≤ a → a ≤ b → (∀ t ∈ sorted, a ≤ t - r) → (∀ t ∈ sorted, t + r ≤ b) →
      (∀ t ∈ sorted, ∀ t' ∈ sorted, t' ≠ t → 2 * r ≤ |t - t'|) →
      (∀ t ∈ sorted, IntervalIntegrable
        (fun t => realWindingIntegrand (γ t - s) (deriv γ t)) volume (t - r) (t + r)) →
      (∀ u ∈ Icc a b, (∀ t ∈ sorted, u ∉ Ioo (t - r) (t + r)) → m ≤ ‖γ u - s‖) →
      IntervalIntegrable (fun t => realWindingIntegrand (γ t - s) (deriv γ t)) volume a b :=
  sorted_crossing_gluing_aux h_piece (fun _ _ _ _ _ h₁ h₂ => h₁.trans h₂)

/-! ### Boundedness of the derivative of a piecewise-`C¹` curve -/

/-- The derivative of a curve that is `C¹` on `[c, d]` has bounded image on `[c, d]`: the
within-interval derivative is continuous on the compact piece, hence bounded there by
compactness, and agrees with `deriv` on the interior; the two endpoints contribute at most two
further (arbitrary, automatically bounded) values. -/
private theorem isBounded_image_deriv_of_contDiffOn {γ : ℝ → ℂ} {c d : ℝ} (hcd : c ≤ d)
    (hC1 : ContDiffOn ℝ 1 γ (Icc c d)) :
    Bornology.IsBounded (deriv γ '' Icc c d) := by
  rcases hcd.eq_or_lt with heq | hlt
  · obtain rfl := heq
    rw [Set.Icc_self, Set.image_singleton]
    exact (Set.finite_singleton _).isBounded
  have hdw : ContinuousOn (derivWithin γ (Icc c d)) (Icc c d) :=
    hC1.continuousOn_derivWithin (uniqueDiffOn_Icc hlt) le_rfl
  have hdw_bdd : Bornology.IsBounded (derivWithin γ (Icc c d) '' Icc c d) :=
    (isCompact_Icc.image_of_continuousOn hdw).isBounded
  refine (hdw_bdd.union
    ((Set.finite_singleton (deriv γ d)).insert (deriv γ c)).isBounded).subset ?_
  rintro y ⟨t, ht, rfl⟩
  rcases eq_or_ne t c with rfl | htc
  · exact Or.inr (by simp)
  rcases eq_or_ne t d with rfl | htd
  · exact Or.inr (by simp)
  exact Or.inl ⟨t, ht, derivWithin_of_mem_nhds (Icc_mem_nhds (lt_of_le_of_ne ht.1 (Ne.symm htc))
    (lt_of_le_of_ne ht.2 htd))⟩

/-- Gluing step for `isBounded_image_deriv_Icc`: boundedness of the derivative's image on any
subinterval `[c, d] ⊆ [[a, b]]`. An instance of `piecewise_gluing_aux`, shared with
`IsPiecewiseC1On.intervalIntegrable_deriv`'s identical breakpoint-splitting induction. -/
private theorem isBounded_image_deriv_aux {γ : ℝ → ℂ} {a b : ℝ} {p : Finset ℝ}
    (hC1 : ∀ c d : ℝ, Icc c d ⊆ uIcc a b → Disjoint (↑p : Set ℝ) (Ioo c d) →
      ContDiffOn ℝ 1 γ (Icc c d)) :
    ∀ n (c d : ℝ), (p.filter (· ∈ Ioo c d)).card ≤ n → c ≤ d → Icc c d ⊆ uIcc a b →
      Bornology.IsBounded (deriv γ '' Icc c d) :=
  piecewise_gluing_aux
    (fun c d hcd hsub hdisj => isBounded_image_deriv_of_contDiffOn hcd (hC1 c d hsub hdisj))
    (fun c m d hcm hmd h₁ h₂ => by
      -- Split at the shared breakpoint `m` so the two pieces' boundedness facts `h₁`, `h₂`
      -- combine via `Set.image_union` into one on the whole `Icc c d`.
      rw [show Icc c d = Icc c m ∪ Icc m d from (Set.Icc_union_Icc_eq_Icc hcm hmd).symm,
        Set.image_union]
      exact h₁.union h₂)

/-- **Boundedness of the derivative of a piecewise-`C¹` curve on its whole parameter interval.**
Mirrors `IsPiecewiseC1On.intervalIntegrable_deriv`'s gluing-across-breakpoints argument, but for
boundedness of the image rather than interval-integrability. -/
private theorem isBounded_image_deriv_Icc {γ : ℝ → ℂ} {a b : ℝ} (h : IsPiecewiseC1On γ a b)
    (hab : a ≤ b) : Bornology.IsBounded (deriv γ '' Icc a b) := by
  obtain ⟨p, -, hC1⟩ := h.exists_breakpoints
  have key := isBounded_image_deriv_aux hC1 (p.filter (· ∈ Ioo (min a b) (max a b))).card
    (min a b) (max a b) le_rfl min_le_max Icc_min_max.subset
  simpa [min_eq_left hab, max_eq_right hab] using key

/-- **A crude bound on the real winding integrand away from its singularity.** No quadratic
remainder estimate is needed once `‖z‖` is bounded below: the numerator is `|Im(v · conj z)| ≤
‖v‖ · ‖z‖` and the denominator is `‖z‖ ^ 2`, so the quotient is at most `‖v‖ / ‖z‖ ≤ ‖v‖ / m`. -/
private theorem abs_realWindingIntegrand_le_div_of_norm_le {z v : ℂ} {m : ℝ} (hm : 0 < m)
    (hz : m ≤ ‖z‖) : |realWindingIntegrand z v| ≤ ‖v‖ / m := by
  have hz_pos : 0 < ‖z‖ := lt_of_lt_of_le hm hz
  have hnum : |z.re * v.im - z.im * v.re| ≤ ‖v‖ * ‖z‖ := by
    have heq : z.re * v.im - z.im * v.re = (v * (starRingEnd ℂ) z).im := by
      rw [Complex.mul_im, Complex.conj_re, Complex.conj_im]; ring
    rw [heq]
    calc |(v * (starRingEnd ℂ) z).im| ≤ ‖v * (starRingEnd ℂ) z‖ := by
          rw [← RCLike.im_eq_complex_im]; exact RCLike.abs_im_le_norm _
      _ = ‖v‖ * ‖z‖ := by rw [norm_mul, RCLike.norm_conj]
  rw [realWindingIntegrand_eq_div, abs_div, Complex.normSq_eq_norm_sq,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖z‖ ^ 2), div_le_div_iff₀ (by positivity) hm]
  calc |z.re * v.im - z.im * v.re| * m ≤ (‖v‖ * ‖z‖) * m :=
        mul_le_mul_of_nonneg_right hnum hm.le
    _ ≤ ‖v‖ * ‖z‖ * ‖z‖ := mul_le_mul_of_nonneg_left hz (mul_nonneg (norm_nonneg v) (norm_nonneg z))
    _ = ‖v‖ * ‖z‖ ^ 2 := by ring

/-! ### Non-vanishing one-sided velocity from the immersion, not assumed separately -/

/-- **A crossing's one-sided velocity is non-zero, from the immersion alone.** No need to assume
this alongside a `C^{1,1}` window at a crossing: `IsPwC1ImmersionOn` already forces a non-zero
`derivWithin`-derivative at every point of the breakpoint-free piece to the right of `t`
(`IsPwC1ImmersionOn.exists_Icc_piece_right`), including at `t` itself, and `derivWithin` at `t`
does not depend on which (`C¹` on `[t, d]`) right-piece it is computed against, since both agree
with the same `HasDerivWithinAt` witness on their common initial segment. -/
private theorem derivWithin_ne_zero_of_isPwC1ImmersionOn_right {γ : ℝ → ℂ} {a b t d : ℝ}
    (h_imm : IsPwC1ImmersionOn γ a b) (ht₀ : t ∈ Ico (min a b) (max a b))
    (hC1 : ContDiffOn ℝ 1 γ (Icc t d)) (htd : t < d) :
    derivWithin γ (Icc t d) t ≠ 0 := by
  obtain ⟨d', hlt', -, hC1', hne'⟩ := h_imm.exists_Icc_piece_right ht₀
  have hte : t < min d d' := lt_min htd hlt'
  have h1 : HasDerivWithinAt γ (derivWithin γ (Icc t d) t) (Icc t (min d d')) t :=
    ((hC1.differentiableOn one_ne_zero) t (left_mem_Icc.mpr htd.le)).hasDerivWithinAt.mono
      (Icc_subset_Icc le_rfl (min_le_left d d'))
  have h2 : HasDerivWithinAt γ (derivWithin γ (Icc t d') t) (Icc t (min d d')) t :=
    ((hC1'.differentiableOn one_ne_zero) t (left_mem_Icc.mpr hlt'.le)).hasDerivWithinAt.mono
      (Icc_subset_Icc le_rfl (min_le_right d d'))
  have hud : UniqueDiffWithinAt ℝ (Icc t (min d d')) t :=
    (uniqueDiffOn_Icc hte).uniqueDiffWithinAt (left_mem_Icc.mpr hte.le)
  have heq : derivWithin γ (Icc t d) t = derivWithin γ (Icc t d') t :=
    (h1.derivWithin hud).symm.trans (h2.derivWithin hud)
  rw [heq]
  exact hne' t (left_mem_Icc.mpr hlt'.le)

/-- **A crossing's one-sided velocity is non-zero, from the immersion alone, from the left.** The
mirror of `derivWithin_ne_zero_of_isPwC1ImmersionOn_right` above. -/
private theorem derivWithin_ne_zero_of_isPwC1ImmersionOn_left {γ : ℝ → ℂ} {a b c t : ℝ}
    (h_imm : IsPwC1ImmersionOn γ a b) (ht₀ : t ∈ Ioc (min a b) (max a b))
    (hC1 : ContDiffOn ℝ 1 γ (Icc c t)) (hct : c < t) :
    derivWithin γ (Icc c t) t ≠ 0 := by
  obtain ⟨c', hlt', -, hC1', hne'⟩ := h_imm.exists_Icc_piece_left ht₀
  have het : max c c' < t := max_lt hct hlt'
  have h1 : HasDerivWithinAt γ (derivWithin γ (Icc c t) t) (Icc (max c c') t) t :=
    ((hC1.differentiableOn one_ne_zero) t (right_mem_Icc.mpr hct.le)).hasDerivWithinAt.mono
      (Icc_subset_Icc (le_max_left c c') le_rfl)
  have h2 : HasDerivWithinAt γ (derivWithin γ (Icc c' t) t) (Icc (max c c') t) t :=
    ((hC1'.differentiableOn one_ne_zero) t (right_mem_Icc.mpr hlt'.le)).hasDerivWithinAt.mono
      (Icc_subset_Icc (le_max_right c c') le_rfl)
  have hud : UniqueDiffWithinAt ℝ (Icc (max c c') t) t :=
    (uniqueDiffOn_Icc het).uniqueDiffWithinAt (right_mem_Icc.mpr het.le)
  have heq : derivWithin γ (Icc c t) t = derivWithin γ (Icc c' t) t :=
    (h1.derivWithin hud).symm.trans (h2.derivWithin hud)
  rw [heq]
  exact hne' t (right_mem_Icc.mpr hlt'.le)

/-! ### Assembly -/

/-- **The real bounded-integrand formula, allowing crossings** (Hungerbühler–Wasem Prop 2.3).
For a closed piecewise-`C¹` immersion `γ` on `[a, b]` all of whose value-`s` parameters are
interior and `C^{1,1}` there (`deriv γ` Lipschitz on a neighborhood) — in particular satisfied
vacuously if `γ` never meets `s` — the real winding integrand `h t := realWindingIntegrand (γ t -
s) (deriv γ t)` has bounded image on `[a, b]` (not just off the crossings, where it is continuous
on the compact avoiding piece, but *at* them too, via the `C^{1,1}` regularity), is a fortiori
genuinely interval-integrable there (not merely assigned Mathlib's junk `0` value for a
non-integrable integrand), and the generalized winding number `n_s(γ)` is a real number equal to
its ordinary (non-principal-value) integral:

`n_s(γ) = (1 / 2π) ∫_a^b (x ẏ - y ẋ) / (x² + y²) dt`, `x + i y = γ - s`.

Unlike the off-curve case, `h`'s boundedness and interval-integrability are not assumed here: both
are derived from the crossing regularity, via
`exists_isBounded_image_realWindingIntegrand_of_lipschitzOnWith_derivWithin_right`/`_left`'s
boundedness at each `C^{1,1}` crossing and the ordinary avoidance argument between crossings — the
actual content of HW Prop 2.3. The two sides of a crossing need not agree: `hγ_lip` allows the
crossing to coincide with a breakpoint of the piecewise-`C¹` immersion (a corner), matching
Hungerbühler–Wasem's own proof of Prop 2.3, which handles that case via the same one-sided
splitting (arXiv:1808.00997, p. 9). -/
theorem windingNumber_eq_real_integral_of_closed_of_interior_crossings {γ : ℝ → ℂ} {a b : ℝ}
    {s : ℂ} (h_imm : IsPwC1ImmersionOn γ a b) (hab : a ≤ b) (hclosed : γ a = γ b)
    (h_interior : ∀ t ∈ Icc a b, γ t = s → t ∈ Ioo a b)
    (hγ_lip : ∀ t ∈ Icc a b, γ t = s → ∃ ε > 0, ∃ K : ℝ≥0,
      ContDiffOn ℝ 1 γ (Icc t (t + ε)) ∧ LipschitzOnWith K (derivWithin γ (Icc t (t + ε)))
        (Icc t (t + ε)) ∧
      ContDiffOn ℝ 1 γ (Icc (t - ε) t) ∧ LipschitzOnWith K (derivWithin γ (Icc (t - ε) t))
        (Icc (t - ε) t)) :
    Bornology.IsBounded ((fun t => realWindingIntegrand (γ t - s) (deriv γ t)) '' Icc a b) ∧
    IntervalIntegrable (fun t => realWindingIntegrand (γ t - s) (deriv γ t)) volume a b ∧
    windingNumber γ a b s
      = ((1 / (2 * Real.pi)
          * ∫ t in a..b, realWindingIntegrand (γ t - s) (deriv γ t) : ℝ) : ℂ) := by
  classical
  rcases hab.eq_or_lt with rfl | hab
  · refine ⟨?_, .refl, by simp⟩
    -- A degenerate `[a, a]` interval is a single point, trivially bounded.
    rw [show Icc a a = {a} from Set.Icc_self a, Set.image_singleton]
    exact (Set.finite_singleton _).isBounded
  set T : Finset ℝ := (h_imm.finite_crossings (z₀ := s)).toFinset with hT_def
  have hT_mem : ∀ {t : ℝ}, t ∈ T ↔ t ∈ Icc a b ∧ γ t = s := fun {_} => by
    rw [hT_def, h_imm.mem_toFinset_finite_crossings, uIcc_of_le hab.le]
  have h_complete : ∀ t ∈ Icc a b, γ t = s → t ∈ T := fun t ht h_eq => hT_mem.mpr ⟨ht, h_eq⟩
  have h_Ioo : ∀ t ∈ T, t ∈ Ioo a b := fun t ht => h_interior t (hT_mem.mp ht).1 (hT_mem.mp ht).2
  have hγ_cont : ContinuousOn γ (Icc a b) := h_imm.continuousOn.mono (uIcc_of_le hab.le).ge
  have h_int_tr : ∀ ε : ℝ, 0 < ε → IntervalIntegrable
      (fun t => if ‖γ t - s‖ > ε then (γ t - s)⁻¹ * deriv γ t else 0) volume a b :=
    fun _ hε => intervalIntegrable_inv_sub_truncated h_imm.continuousOn
      h_imm.isPiecewiseC1On.intervalIntegrable_deriv hε
  obtain ⟨p, hp⟩ := h_imm.isPiecewiseC1On.exists_finset_differentiableAt
  have hP : (↑p : Set ℝ).Countable := p.countable_toSet
  have hγ_diff : ∀ t ∈ Ioo a b \ (↑p : Set ℝ), DifferentiableAt ℝ γ t := fun t ht => by
    rw [min_eq_left hab.le, max_eq_right hab.le] at hp
    exact hp t ht
  -- The window value: the explicit log-norm-plus-argument limit at each crossing.
  choose! R hR_pos L_R L_L hL_R hL_L h_spec using
    fun t₀ (ht₀ : t₀ ∈ T) => exists_radius_perWindow_tendsto_value h_imm hab (h_Ioo t₀ ht₀)
      (hT_mem.mp ht₀).2
  -- The crossing regularity: a `C^{1,1}` neighborhood on each side of each crossing (possibly a
  -- corner, so the two sides may disagree), and the boundedness of the real winding integrand
  -- each side already buys on a (possibly smaller) one-sided window. Each side's forced non-zero
  -- velocity is not assumed here -- `IsPwC1ImmersionOn` already forces it.
  choose! εD hεD_pos K hC1R hlipR hC1L hlipL using fun t₀ (ht₀ : t₀ ∈ T) =>
    hγ_lip t₀ (hT_mem.mp ht₀).1 (hT_mem.mp ht₀).2
  have h_Ico : ∀ t ∈ T, t ∈ Ico (min a b) (max a b) := fun t ht => by
    rw [min_eq_left hab.le, max_eq_right hab.le]; exact ⟨(h_Ioo t ht).1.le, (h_Ioo t ht).2⟩
  have h_Ioc : ∀ t ∈ T, t ∈ Ioc (min a b) (max a b) := fun t ht => by
    rw [min_eq_left hab.le, max_eq_right hab.le]; exact ⟨(h_Ioo t ht).1, (h_Ioo t ht).2.le⟩
  choose! ρ_lipR hρ_lipR_pos hρ_lipR_lt hbddR using fun t₀ (ht₀ : t₀ ∈ T) =>
    exists_isBounded_image_realWindingIntegrand_of_lipschitzOnWith_derivWithin_right
      (show t₀ < t₀ + εD t₀ by linarith [hεD_pos t₀ ht₀])
      ((hC1R t₀ ht₀).differentiableOn one_ne_zero) (hlipR t₀ ht₀) (hT_mem.mp ht₀).2
      (derivWithin_ne_zero_of_isPwC1ImmersionOn_right h_imm (h_Ico t₀ ht₀) (hC1R t₀ ht₀)
        (by linarith [hεD_pos t₀ ht₀]))
  choose! ρ_lipL hρ_lipL_pos hρ_lipL_lt hbddL using fun t₀ (ht₀ : t₀ ∈ T) =>
    exists_isBounded_image_realWindingIntegrand_of_lipschitzOnWith_derivWithin_left
      (show t₀ - εD t₀ < t₀ by linarith [hεD_pos t₀ ht₀])
      ((hC1L t₀ ht₀).differentiableOn one_ne_zero) (hlipL t₀ ht₀) (hT_mem.mp ht₀).2
      (derivWithin_ne_zero_of_isPwC1ImmersionOn_left h_imm (h_Ioc t₀ ht₀) (hC1L t₀ ht₀)
        (by linarith [hεD_pos t₀ ht₀]))
  -- Combine the two one-sided windows into one symmetric bounded window per crossing.
  set ρ_lip : ℝ → ℝ := fun t => min (ρ_lipR t) (ρ_lipL t) with hρ_lip_def
  have hρ_lip_pos : ∀ t ∈ T, 0 < ρ_lip t := fun t ht => lt_min (hρ_lipR_pos t ht) (hρ_lipL_pos t ht)
  have hρ_lip_bdd : ∀ t₀ ∈ T, Bornology.IsBounded
      ((fun t => realWindingIntegrand (γ t - s) (deriv γ t)) ''
        Icc (t₀ - ρ_lip t₀) (t₀ + ρ_lip t₀)) := fun t₀ ht₀ => by
    have hRsub : Icc t₀ (t₀ + ρ_lip t₀) ⊆ Icc t₀ (t₀ + ρ_lipR t₀) :=
      Icc_subset_Icc le_rfl (by linarith [min_le_left (ρ_lipR t₀) (ρ_lipL t₀)])
    have hLsub : Icc (t₀ - ρ_lip t₀) t₀ ⊆ Icc (t₀ - ρ_lipL t₀) t₀ :=
      Icc_subset_Icc (by linarith [min_le_right (ρ_lipR t₀) (ρ_lipL t₀)]) le_rfl
    -- Split the symmetric window at `t₀` so the left/right one-sided boundedness facts
    -- `hbddL`/`hbddR` combine via `Set.image_union` into one on the whole window.
    rw [show Icc (t₀ - ρ_lip t₀) (t₀ + ρ_lip t₀)
          = Icc (t₀ - ρ_lip t₀) t₀ ∪ Icc t₀ (t₀ + ρ_lip t₀) from
        (Set.Icc_union_Icc_eq_Icc (by linarith [hρ_lip_pos t₀ ht₀])
          (by linarith [hρ_lip_pos t₀ ht₀])).symm,
      Set.image_union]
    exact ((hbddL t₀ ht₀).subset (Set.image_mono hLsub)).union
      ((hbddR t₀ ht₀).subset (Set.image_mono hRsub))
  -- Shrink the common window radius to also stay inside every crossing's bounded window.
  set R' : ℝ → ℝ := fun t => min (R t) (ρ_lip t) with hR'_def
  have hR'_pos : ∀ t ∈ T, 0 < R' t := fun t ht => lt_min (hR_pos t ht) (hρ_lip_pos t ht)
  obtain ⟨ρ, hρ_pos, h_endpts, h_pair, hρ_le_R'⟩ := exists_common_window_radius_le h_Ioo R' hR'_pos
  have hρ_le_R : ∀ t ∈ T, ρ ≤ R t := fun t ht => (hρ_le_R' t ht).trans (min_le_left _ _)
  have hρ_le_ρlip : ∀ t ∈ T, ρ ≤ ρ_lip t := fun t ht => (hρ_le_R' t ht).trans (min_le_right _ _)
  have h_unique : ∀ t₀ ∈ T, ∀ t ∈ Icc (t₀ - ρ) (t₀ + ρ), γ t = s → t = t₀ := fun t₀ ht₀ t ht h_eq =>
    eq_of_mem_window_of_eq_of_lt_of_two_mul_lt (h_endpts t₀ ht₀) (h_pair t₀ ht₀) h_complete ht h_eq
  have h_far := exists_complement_windows_dist_lower_bound hγ_cont h_complete (fun _ => ρ)
    fun t _ => hρ_pos
  -- The real winding integrand's interval-integrability: away from crossings it's the imaginary
  -- part of the already-integrable index integrand; at each crossing, boundedness from the
  -- crossing's `C^{1,1}` regularity.
  have h_int : IntervalIntegrable (fun t => realWindingIntegrand (γ t - s) (deriv γ t)) volume
      a b := by
    refine intervalIntegrable_along_sorted
      (fun l u hA hlu hu h_far' => ?_)
      (T.sort (· ≤ ·)) (Finset.sortedLT_sort T)
      (fun _ => hρ_pos.le) a le_rfl hab.le
      (fun t ht => by linarith [(h_endpts t ((Finset.mem_sort _).mp ht)).1])
      (fun t ht => by linarith [(h_endpts t ((Finset.mem_sort _).mp ht)).2])
      (fun t ht t' ht' hne => (h_pair t ((Finset.mem_sort _).mp ht) t'
        ((Finset.mem_sort _).mp ht') hne).le)
      (fun t ht => by
        have ht' := (Finset.mem_sort _).mp ht
        have hL : ρ_lipL t ≤ εD t := by linarith [hρ_lipL_lt t ht']
        have hR : ρ_lipR t ≤ εD t := by linarith [hρ_lipR_lt t ht']
        exact (intervalIntegrable_realWindingIntegrand_window_left hρ_pos
            ((hρ_le_ρlip t ht').trans (min_le_right _ _)) hL
            (hC1L t ht') (hbddL t ht')).trans
          (intervalIntegrable_realWindingIntegrand_window_right hρ_pos
            ((hρ_le_ρlip t ht').trans (min_le_left _ _)) hR
            (hC1R t ht') (hbddR t ht')))
      (fun u hu h_avoid => h_far.choose_spec.2 u hu
        fun t ht => h_avoid t ((Finset.mem_sort _).mpr ht))
    have h_ne : ∀ t ∈ Icc l u, γ t ≠ s := fun t ht h_eq => by
      have := h_far' t ht
      rw [h_eq, sub_self, norm_zero] at this
      linarith [h_far.choose_spec.1]
    have hcplx : IntervalIntegrable (fun t => (γ t - s)⁻¹ * deriv γ t) volume l u :=
      intervalIntegrable_inv_sub_mul_deriv
        (by rw [uIcc_of_le hlu]; exact hγ_cont.mono (Icc_subset_Icc hA hu))
        (by intro t ht; rw [uIcc_of_le hlu] at ht; exact h_ne t ht)
        (h_imm.isPiecewiseC1On.intervalIntegrable_deriv.mono_set (by
          rw [uIcc_of_le hlu, uIcc_of_le hab.le]
          exact Icc_subset_Icc hA hu))
    have hfun_eq : (fun t => realWindingIntegrand (γ t - s) (deriv γ t))
        = (fun t => ((γ t - s)⁻¹ * deriv γ t).im) :=
      funext fun t => realWindingIntegrand_def (γ t - s) (deriv γ t)
    rw [hfun_eq]
    exact ⟨hcplx.1.im, hcplx.2.im⟩
  -- Both the principal-value witness and the real-part telescoping are read off in one call:
  -- the plain pieces telescope in real part to the log-norm difference
  -- (`re_integral_inv_sub_mul_deriv_eq_log_norm`), and each window's explicit limit value has
  -- exactly that real part built in already (`exists_radius_perWindow_tendsto_value`).
  obtain ⟨L, hHCPV, hRe0⟩ := hasCauchyPVAt_of_perWindow_tendsto_of_interiorDisjoint_re_boundary
    (g := fun z => (z - s)⁻¹) (Ψ := fun t => Real.log ‖γ t - s‖) hab.le T
    (fun _ => hρ_pos.le)
    (fun t ht => by linarith [(h_endpts t ht).1])
    (fun t ht => by linarith [(h_endpts t ht).2])
    (fun t ht t' ht' hne => (h_pair t ht t' ht' hne).le)
    h_int_tr
    (fun l u hA hlu hu h_far' => by
      have h_ne : ∀ t ∈ Icc l u, γ t ≠ s := fun t ht h_eq => by
        have := h_far' t ht
        rw [h_eq, sub_self, norm_zero] at this
        linarith [h_far.choose_spec.1]
      refine re_integral_inv_sub_mul_deriv_eq_log_norm hlu hP
        (hγ_cont.mono (Icc_subset_Icc hA hu))
        (fun t ht => hγ_diff t ⟨Ioo_subset_Ioo hA hu ht.1, ht.2⟩) h_ne ?_
      refine intervalIntegrable_inv_sub_mul_deriv ?_ ?_
        (h_imm.isPiecewiseC1On.intervalIntegrable_deriv.mono_set (by
          rw [uIcc_of_le hlu, uIcc_of_le hab.le]
          exact Icc_subset_Icc hA hu))
      · rw [uIcc_of_le hlu]; exact hγ_cont.mono (Icc_subset_Icc hA hu)
      · intro t ht; rw [uIcc_of_le hlu] at ht; exact h_ne t ht)
    (fun t ht => ⟨((Real.log ‖γ (t + ρ) - s‖ - Real.log ‖γ (t - ρ) - s‖ : ℝ) : ℂ) +
        ((((-L_L t) / (γ (t - ρ) - s)).arg + ((γ (t + ρ) - s) / L_R t).arg : ℝ) : ℂ) * Complex.I,
      by simp,
      h_spec t ht ρ hρ_pos (hρ_le_R t ht) (by linarith [(h_endpts t ht).1])
        (by linarith [(h_endpts t ht).2]) (h_unique t ht)⟩)
    ⟨h_far.choose_spec.1, h_far.choose_spec.2⟩
  have hwind : windingNumber γ a b s = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * L :=
    windingNumber_eq_of_hasCauchyPVAt hHCPV
  have hRe : L.re = 0 := by rw [hRe0, hclosed, sub_self]
  -- The integral identity: the imaginary part is the ordinary integral of the real integrand.
  -- Reuses the upstream principal-value/real-integrand bridge directly, rather than re-deriving
  -- its dominated-convergence argument here.
  have hIm : L.im = ∫ t in a..b, realWindingIntegrand (γ t - s) (deriv γ t) :=
    hHCPV.im_eq_integral_realWindingIntegrand h_int
  -- The real winding integrand is bounded on all of `[a, b]`: bounded on each of the finitely
  -- many crossing windows (from the `C^{1,1}` regularity), and bounded away from every window by
  -- the crude `‖v‖ / m` estimate, `m` the lower bound on `‖γ - s‖` there and `Cd` a bound on
  -- `‖deriv γ‖` over all of `[a, b]` (piecewise-`C¹`, hence bounded on finitely many pieces).
  have hm_pos : 0 < h_far.choose := h_far.choose_spec.1
  obtain ⟨Cd, hCd⟩ := (isBounded_image_deriv_Icc h_imm.isPiecewiseC1On hab.le).exists_norm_le
  have hwin_union_bdd : Bornology.IsBounded
      (⋃ t₀ ∈ T, (fun t => realWindingIntegrand (γ t - s) (deriv γ t)) ''
        Icc (t₀ - ρ) (t₀ + ρ)) :=
    (Bornology.isBounded_biUnion_finset T).mpr fun t₀ ht₀ => by
      have hsub : Icc (t₀ - ρ) (t₀ + ρ) ⊆ Icc (t₀ - ρ_lip t₀) (t₀ + ρ_lip t₀) :=
        Icc_subset_Icc (by linarith [hρ_le_ρlip t₀ ht₀]) (by linarith [hρ_le_ρlip t₀ ht₀])
      exact (hρ_lip_bdd t₀ ht₀).subset (Set.image_mono hsub)
  have h_bdd : Bornology.IsBounded
      ((fun t => realWindingIntegrand (γ t - s) (deriv γ t)) '' Icc a b) := by
    refine (hwin_union_bdd.union (Metric.isBounded_closedBall
      (x := (0 : ℝ)) (r := Cd / h_far.choose))).subset ?_
    rintro y ⟨t, ht, rfl⟩
    by_cases hcase : ∀ t₀ ∈ T, t ∉ Ioo (t₀ - ρ) (t₀ + ρ)
    · refine Or.inr ?_
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
      have hm_le : h_far.choose ≤ ‖γ t - s‖ := h_far.choose_spec.2 t ht hcase
      have hv_le : ‖deriv γ t‖ ≤ Cd := hCd _ ⟨t, ht, rfl⟩
      calc |realWindingIntegrand (γ t - s) (deriv γ t)| ≤ ‖deriv γ t‖ / h_far.choose :=
            abs_realWindingIntegrand_le_div_of_norm_le hm_pos hm_le
        _ ≤ Cd / h_far.choose := by gcongr
    · push Not at hcase
      obtain ⟨t₀, ht₀, htwin⟩ := hcase
      exact Or.inl (Set.mem_biUnion ht₀ ⟨t, Ioo_subset_Icc_self htwin, rfl⟩)
  refine ⟨h_bdd, h_int, ?_⟩
  rw [hwind, ← Complex.re_add_im L, hRe, hIm]
  have h2πI_ne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := Complex.two_pi_I_ne_zero
  push_cast
  field_simp
  ring

end TauCeti.Contour

end

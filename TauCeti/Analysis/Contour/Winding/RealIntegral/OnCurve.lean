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
to the same bounded real integral, whenever that integral is interval-integrable. (The hypothesis
is satisfied vacuously when `γ` never meets `s`, so this also reproves the avoiding case, but the
two are kept as separate theorems since their proofs are unrelated.)

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

private theorem hasDerivAt_re {f : ℝ → ℂ} {t : ℝ} {D : ℂ} (hf : HasDerivAt f D t) :
    HasDerivAt (fun u => (f u).re) D.re t :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hf

private theorem hasDerivAt_im {f : ℝ → ℂ} {t : ℝ} {D : ℂ} (hf : HasDerivAt f D t) :
    HasDerivAt (fun u => (f u).im) D.im t :=
  Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hf

/-- The derivative of the squared complex modulus, in the real-parameter chain-rule form used to
differentiate the log-norm below. -/
private theorem hasDerivAt_normSq {f : ℝ → ℂ} {t : ℝ} {D : ℂ} (hf : HasDerivAt f D t) :
    HasDerivAt (fun u => Complex.normSq (f u)) (2 * ((starRingEnd ℂ (f t) * D).re)) t := by
  have hre := hasDerivAt_re hf
  have him := hasDerivAt_im hf
  have h1 : HasDerivAt (fun u => (f u).re * (f u).re) (D.re * (f t).re + (f t).re * D.re) t :=
    hre.mul hre
  have h2 : HasDerivAt (fun u => (f u).im * (f u).im) (D.im * (f t).im + (f t).im * D.im) t :=
    him.mul him
  have key : HasDerivAt (fun u => Complex.normSq (f u))
      (D.re * (f t).re + (f t).re * D.re + (D.im * (f t).im + (f t).im * D.im)) t :=
    (h1.add h2).congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => by
      simp [Complex.normSq_apply])
  have hval : D.re * (f t).re + (f t).re * D.re + (D.im * (f t).im + (f t).im * D.im)
      = 2 * ((starRingEnd ℂ (f t) * D).re) := by
    simp [Complex.mul_re]; ring
  rwa [hval] at key

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

/-- **The velocity at a `C^{1,1}` crossing of a piecewise-`C¹` immersion is non-zero.** The
immersion's one-sided tangent there is non-zero (`IsPwC1ImmersionOn.exists_deriv_right_limit`),
and `deriv γ`'s continuity on a neighborhood (from Lipschitz continuity there) forces the
ordinary derivative to agree with that one-sided limit. -/
private theorem deriv_ne_zero_of_lipschitzOnWith_deriv {γ : ℝ → ℂ} {a b t₀ ε : ℝ} {K : ℝ≥0}
    (h_imm : IsPwC1ImmersionOn γ a b) (hab : a ≤ b) (ht₀ : t₀ ∈ Ioo a b) (hε_pos : 0 < ε)
    (hlip : LipschitzOnWith K (deriv γ) (Icc (t₀ - ε) (t₀ + ε))) :
    deriv γ t₀ ≠ 0 := by
  have htendsto : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 (deriv γ t₀)) :=
    ((hlip.continuousOn.continuousAt
      (Icc_mem_nhds (by linarith) (by linarith))).tendsto).mono_left nhdsWithin_le_nhds
  obtain ⟨L, hL_ne, hL_tendsto⟩ := h_imm.exists_deriv_right_limit
    (show t₀ ∈ Ico (min a b) (max a b) by
      rw [min_eq_left hab, max_eq_right hab]; exact ⟨ht₀.1.le, ht₀.2⟩)
  rwa [tendsto_nhds_unique htendsto hL_tendsto]

/-- **The real winding integrand is interval-integrable on a small enough symmetric window around
a `C^{1,1}` crossing.** Bounded on a window of radius `ρ_lip ≤ ε_D`
(`exists_isBounded_image_realWindingIntegrand_of_lipschitzOnWith_deriv`, from Lipschitz
regularity of `deriv γ` and its non-zero velocity at the crossing itself, the window's only
value-`s` parameter), shrunk further to any `ρ ≤ ρ_lip`, and measurable (γ and `deriv γ` are
genuinely continuous throughout the window, so `(γ · - s)⁻¹ * deriv γ` is a.e. strongly
measurable exactly as in `intervalIntegrable_inv_sub_truncated`, without needing an avoidance
hypothesis), hence integrable on the finite-measure window. -/
private theorem intervalIntegrable_realWindingIntegrand_window {γ : ℝ → ℂ} {s : ℂ}
    {t₀ ρ ρ_lip εD : ℝ} {K : ℝ≥0}
    (hρ_pos : 0 < ρ) (hρ_le_ρlip : ρ ≤ ρ_lip) (hρlip_le_εD : ρ_lip ≤ εD)
    (hderiv : ∀ u ∈ Icc (t₀ - εD) (t₀ + εD), HasDerivAt γ (deriv γ u) u)
    (hlip : LipschitzOnWith K (deriv γ) (Icc (t₀ - εD) (t₀ + εD)))
    (hbdd : Bornology.IsBounded
      ((fun t => realWindingIntegrand (γ t - s) (deriv γ t)) '' Icc (t₀ - ρ_lip) (t₀ + ρ_lip))) :
    IntervalIntegrable (fun t => realWindingIntegrand (γ t - s) (deriv γ t)) volume
      (t₀ - ρ) (t₀ + ρ) := by
  have hsub_lip : Icc (t₀ - ρ) (t₀ + ρ) ⊆ Icc (t₀ - ρ_lip) (t₀ + ρ_lip) :=
    Icc_subset_Icc (by linarith) (by linarith)
  have hsub_εD : Icc (t₀ - ρ) (t₀ + ρ) ⊆ Icc (t₀ - εD) (t₀ + εD) :=
    Icc_subset_Icc (by linarith) (by linarith)
  obtain ⟨C, hC⟩ := (hbdd.subset (Set.image_mono hsub_lip)).exists_norm_le
  have hγc : ContinuousOn γ (Icc (t₀ - ρ) (t₀ + ρ)) := fun t ht =>
    (hderiv t (hsub_εD ht)).continuousAt.continuousWithinAt
  have hdc : ContinuousOn (deriv γ) (Icc (t₀ - ρ) (t₀ + ρ)) := hlip.continuousOn.mono hsub_εD
  have huIoc_sub : uIoc (t₀ - ρ) (t₀ + ρ) ⊆ Icc (t₀ - ρ) (t₀ + ρ) :=
    (uIoc_subset_uIcc).trans (by rw [uIcc_of_le (by linarith : t₀ - ρ ≤ t₀ + ρ)])
  have haesm : AEStronglyMeasurable (fun t => (γ t - s)⁻¹ * deriv γ t)
      (volume.restrict (uIoc (t₀ - ρ) (t₀ + ρ))) := by
    have hγ_aem : AEMeasurable γ (volume.restrict (uIoc (t₀ - ρ) (t₀ + ρ))) :=
      ((hγc.aestronglyMeasurable measurableSet_Icc).mono_measure
        (Measure.restrict_mono huIoc_sub le_rfl)).aemeasurable
    have hd_aem : AEMeasurable (deriv γ) (volume.restrict (uIoc (t₀ - ρ) (t₀ + ρ))) :=
      ((hdc.aestronglyMeasurable measurableSet_Icc).mono_measure
        (Measure.restrict_mono huIoc_sub le_rfl)).aemeasurable
    exact ((hγ_aem.sub_const s).inv.mul hd_aem).aestronglyMeasurable
  have haesm_h : AEStronglyMeasurable (fun t => realWindingIntegrand (γ t - s) (deriv γ t))
      (volume.restrict (uIoc (t₀ - ρ) (t₀ + ρ))) := by
    refine (Complex.imCLM.continuous.comp_aestronglyMeasurable haesm).congr
      (MeasureTheory.ae_of_all _ fun t => ?_)
    simp only [Complex.imCLM_apply, realWindingIntegrand_def]
  rw [intervalIntegrable_iff]
  have : IsFiniteMeasure (volume.restrict (uIoc (t₀ - ρ) (t₀ + ρ))) :=
    isFiniteMeasure_restrict.mpr ((measure_mono uIoc_subset_uIcc).trans_lt
      (by rw [uIcc_of_le (by linarith : t₀ - ρ ≤ t₀ + ρ)]
          exact isCompact_Icc.measure_lt_top)).ne
  refine Integrable.of_bound haesm_h C ?_
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
`exists_isBounded_image_realWindingIntegrand_of_lipschitzOnWith_deriv`'s boundedness at each
`C^{1,1}` crossing and the ordinary avoidance argument between crossings — the actual content of
HW Prop 2.3. -/
theorem windingNumber_eq_real_integral_of_closed_of_interior_crossings {γ : ℝ → ℂ} {a b : ℝ}
    {s : ℂ} (h_imm : IsPwC1ImmersionOn γ a b) (hab : a ≤ b) (hclosed : γ a = γ b)
    (h_interior : ∀ t ∈ Icc a b, γ t = s → t ∈ Ioo a b)
    (hγ_lip : ∀ t ∈ Icc a b, γ t = s → ∃ ε > 0, ∃ K : ℝ≥0,
      (∀ u ∈ Icc (t - ε) (t + ε), HasDerivAt γ (deriv γ u) u) ∧
        LipschitzOnWith K (deriv γ) (Icc (t - ε) (t + ε))) :
    Bornology.IsBounded ((fun t => realWindingIntegrand (γ t - s) (deriv γ t)) '' Icc a b) ∧
    IntervalIntegrable (fun t => realWindingIntegrand (γ t - s) (deriv γ t)) volume a b ∧
    windingNumber γ a b s
      = ((1 / (2 * Real.pi)
          * ∫ t in a..b, realWindingIntegrand (γ t - s) (deriv γ t) : ℝ) : ℂ) := by
  classical
  rcases hab.eq_or_lt with rfl | hab
  · refine ⟨?_, .refl, by simp⟩
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
  -- The crossing regularity: a `C^{1,1}` neighborhood around each crossing, its forced non-zero
  -- velocity, and the boundedness of the real winding integrand this already buys on a
  -- (possibly smaller) window.
  choose! εD hεD_pos K hderivD hlipD using fun t₀ (ht₀ : t₀ ∈ T) =>
    hγ_lip t₀ (hT_mem.mp ht₀).1 (hT_mem.mp ht₀).2
  have hvel : ∀ t₀ ∈ T, deriv γ t₀ ≠ 0 := fun t₀ ht₀ =>
    deriv_ne_zero_of_lipschitzOnWith_deriv h_imm hab.le (h_Ioo t₀ ht₀) (hεD_pos t₀ ht₀)
      (hlipD t₀ ht₀)
  choose! ρ_lip hρ_lip_pos hρ_lip_le_εD hρ_lip_bdd using fun t₀ (ht₀ : t₀ ∈ T) =>
    exists_isBounded_image_realWindingIntegrand_of_lipschitzOnWith_deriv (hεD_pos t₀ ht₀)
      (hderivD t₀ ht₀) (hlipD t₀ ht₀) (hT_mem.mp ht₀).2 (hvel t₀ ht₀)
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
      (fun t ht => intervalIntegrable_realWindingIntegrand_window hρ_pos
        (hρ_le_ρlip t ((Finset.mem_sort _).mp ht)) (hρ_lip_le_εD t ((Finset.mem_sort _).mp ht))
        (hderivD t ((Finset.mem_sort _).mp ht)) (hlipD t ((Finset.mem_sort _).mp ht))
        (hρ_lip_bdd t ((Finset.mem_sort _).mp ht)))
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

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Contour.Winding.RealIntegral.Basic
public import TauCeti.Analysis.Contour.PwC1ImmersionOn
import TauCeti.Analysis.Contour.Argument.Lift
import TauCeti.Analysis.Contour.Crossing.Finiteness
import TauCeti.Analysis.Contour.Crossing.PVAggregation
import TauCeti.Analysis.Contour.Crossing.Windows
import TauCeti.Analysis.Contour.InvSubCPVExistence
import TauCeti.Analysis.Contour.PerWindow.CPV
import TauCeti.Analysis.Contour.Winding.LipschitzBoundedIntegrand
import TauCeti.Analysis.Contour.Winding.SegmentSum
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
`s` is interior to `[a, b]` **and** `derivWithin γ` is Lipschitz on a one-sided closed piece
ending or starting there (`C^{1,1}`, possibly a different piece on each side, so a crossing may
coincide with a breakpoint of the immersion). The generalized winding number is then a genuine
Cauchy principal value rather than an ordinary index integral, and this theorem shows it is still
real and equal
to the same bounded real integral. Unlike the avoiding case, interval-integrability of that
integral is not assumed here: it follows from a.e. strong measurability (continuity off the
crossings, no different from the avoiding case) together with the boundedness above, both drawn
from the same `C^{1,1}` crossing regularity this file's boundedness result needs. (That
regularity hypothesis is satisfied vacuously when `γ` never meets `s`, so this also reproves the
avoiding case, but the two are kept as separate theorems since their proofs are unrelated.)

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

* `TauCeti.Contour.windingNumber_eq_real_integral_of_closed_interior_crossings` — the real
  bounded-integrand formula for a closed immersion that avoids `s` at its basepoint (so every
  crossing of `s`, if any, is automatically interior).
* `TauCeti.Contour.isBounded_image_realWindingIntegrand_of_interior_crossings` and
  `TauCeti.Contour.intervalIntegrable_realWindingIntegrand_of_interior_crossings` — the
  boundedness and interval-integrability facts the formula above is built from, for callers that
  need those facts rather than just the equality.

## Provenance

New assembly for this roadmap target (HW Prop 2.3), built from existing Tau Ceti
contour-integration infrastructure: the per-crossing window value
(`exists_radius_perWindow_tendsto_log_norm_add_arg`), the existence-and-real-part aggregation
(`cauchyPVExistsAt_of_perWindow_tendsto_of_interiorDisjoint_re_boundary`), and the integral-identity
bridge (`HasCauchyPVAt.im_eq_integral_realWindingIntegrand`). This file's own content is the
log-norm derivative machinery (feeding the real-part telescoping hypothesis of the aggregation
theorem) and deriving the real winding integrand's boundedness and interval-integrability from
the crossing regularity rather than assuming them, via `Winding.LipschitzBoundedIntegrand`'s
one-sided bounds instantiating `Crossing.PVAggregation`'s generic sorted-crossing-list gluing
induction (`sorted_crossing_gluing_induction`) with that integrability invariant -- the first
consumer of that combinator outside its own file, which uses the same induction shape by hand for
its own per-crossing-window construction rather than through the generic combinator; the assembly
of all of the above into the final formula is this file's content too. The per-crossing window
value this file reads off (`exists_radius_perWindow_tendsto_log_norm_add_arg`), with both its
real and imaginary parts, is proved once, generically, in `InvSubCPVExistence`.

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

/-- **The real part of the plain-piece contour integral telescopes to the log-norm difference of
its endpoints**, with no slit-plane hypothesis needed: taking real parts of
`integral_inv_sub_mul_deriv_eq_log_norm_add_I_mul_sum_log_im`'s decomposition discards its
imaginary sum term (a real number times `Complex.I`), leaving exactly the log-norm difference,
independent of any branch choice on the partition
`exists_continuousOn_arg_lift_with_partition` supplies. -/
private theorem re_integral_inv_sub_mul_deriv_eq_log_norm {γ : ℝ → ℂ} {s : ℂ} {l u : ℝ}
    {P : Set ℝ} (hlu : l ≤ u) (hP : P.Countable) (hγ_cont : ContinuousOn γ (Icc l u))
    (hγ_diff : ∀ t ∈ Ioo l u \ P, DifferentiableAt ℝ γ t) (h_ne : ∀ t ∈ Icc l u, γ t ≠ s)
    (h_int : IntervalIntegrable (fun t => (γ t - s)⁻¹ * deriv γ t) volume l u) :
    (∫ t in l..u, (γ t - s)⁻¹ * deriv γ t).re = Real.log ‖γ u - s‖ - Real.log ‖γ l - s‖ := by
  obtain ⟨N, part, -, hpart_zero, hpart_N, hpart_mono, -, -, h_slit, -, -⟩ :=
    exists_continuousOn_arg_lift_with_partition hlu hγ_cont h_ne
  have heq := integral_inv_sub_mul_deriv_eq_log_norm_add_I_mul_sum_log_im hP hpart_zero hpart_N
    hpart_mono hγ_cont hγ_diff h_slit h_int
  simp [heq]

/-! ### Interval-integrability of the real winding integrand, allowing crossings -/

/-- **The real winding integrand is interval-integrable on a small enough window at a `C^{1,1}`
crossing, orientation-generic.** Bounded on a window `[p', q']` (typically
`exists_isBounded_image_realWindingIntegrand_of_lipschitzOnWith_derivWithin_right`/`_left`'s
window), shrunk further to any sub-window `[p, q] ⊆ [p', q']`, and measurable: `γ` and
`derivWithin γ (Icc c d)` are continuous throughout `[p, q]`, agreeing with `deriv γ` off the
single point `t₀` (measure zero, so invisible to a.e. strong measurability), so `(γ · - s)⁻¹ *
deriv γ` is a.e. strongly measurable there, exactly as in `intervalIntegrable_inv_sub_truncated`,
without needing an avoidance hypothesis or the two sides of the crossing to agree. One instance
of `[c, d]`, `[p', q']`, `[p, q]` sharing their left endpoint gives the right-window case; sharing
their right endpoint gives the left-window case -- both proved at once here rather than by two
near-identical arguments differing only in which side grows from the crossing. -/
private theorem intervalIntegrable_realWindingIntegrand_window {γ : ℝ → ℂ} {s : ℂ}
    {c d p q p' q' : ℝ} {K : ℝ≥0} (hpq : p ≤ q) (h_sub_bdd : Icc p q ⊆ Icc p' q')
    (h_sub_cd : Icc p' q' ⊆ Icc c d) (hdiff : DifferentiableOn ℝ γ (Icc c d))
    (hlip : LipschitzOnWith K (derivWithin γ (Icc c d)) (Icc c d))
    (hbdd : Bornology.IsBounded
      ((fun t => realWindingIntegrand (γ t - s) (deriv γ t)) '' Icc p' q')) :
    IntervalIntegrable (fun t => realWindingIntegrand (γ t - s) (deriv γ t)) volume p q := by
  have hsub_cd : Icc p q ⊆ Icc c d := h_sub_bdd.trans h_sub_cd
  have hcp : c ≤ p := (hsub_cd (left_mem_Icc.mpr hpq)).1
  have hqd : q ≤ d := (hsub_cd (right_mem_Icc.mpr hpq)).2
  obtain ⟨C, hC⟩ := (hbdd.subset (Set.image_mono h_sub_bdd)).exists_norm_le
  have hγc : ContinuousOn γ (Icc p q) := hdiff.continuousOn.mono hsub_cd
  have hdw : ContinuousOn (derivWithin γ (Icc c d)) (Icc p q) := hlip.continuousOn.mono hsub_cd
  have huIoc_eq : uIoc p q = Ioc p q := uIoc_of_le hpq
  have huIoc_sub : uIoc p q ⊆ Icc p q := (uIoc_subset_uIcc).trans (by rw [uIcc_of_le hpq])
  have haesm : AEStronglyMeasurable (fun t => (γ t - s)⁻¹ * derivWithin γ (Icc c d) t)
      (volume.restrict (uIoc p q)) := by
    have hγ_aem : AEMeasurable γ (volume.restrict (uIoc p q)) :=
      ((hγc.aestronglyMeasurable measurableSet_Icc).mono_measure
        (Measure.restrict_mono huIoc_sub le_rfl)).aemeasurable
    have hd_aem : AEMeasurable (derivWithin γ (Icc c d)) (volume.restrict (uIoc p q)) :=
      ((hdw.aestronglyMeasurable measurableSet_Icc).mono_measure
        (Measure.restrict_mono huIoc_sub le_rfl)).aemeasurable
    exact ((hγ_aem.sub_const s).inv.mul hd_aem).aestronglyMeasurable
  have haesm_h : AEStronglyMeasurable
      (fun t => realWindingIntegrand (γ t - s) (derivWithin γ (Icc c d) t))
      (volume.restrict (uIoc p q)) := by
    refine (Complex.imCLM.continuous.comp_aestronglyMeasurable haesm).congr
      (MeasureTheory.ae_of_all _ fun t => ?_)
    simp only [Complex.imCLM_apply, realWindingIntegrand_def]
  have hcongr : (fun t => realWindingIntegrand (γ t - s) (deriv γ t))
      =ᶠ[ae (volume.restrict (uIoc p q))]
      (fun t => realWindingIntegrand (γ t - s) (derivWithin γ (Icc c d) t)) := by
    rw [huIoc_eq, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
    congr 1
    exact (derivWithin_of_mem_nhds
      (Icc_mem_nhds (lt_of_le_of_lt hcp ht.1) (lt_of_lt_of_le ht.2 hqd))).symm
  have haesm_h' : AEStronglyMeasurable (fun t => realWindingIntegrand (γ t - s) (deriv γ t))
      (volume.restrict (uIoc p q)) := haesm_h.congr hcongr.symm
  rw [intervalIntegrable_iff]
  have : IsFiniteMeasure (volume.restrict (uIoc p q)) :=
    isFiniteMeasure_restrict.mpr ((measure_mono uIoc_subset_uIcc).trans_lt
      (by rw [uIcc_of_le hpq]; exact isCompact_Icc.measure_lt_top)).ne
  refine Integrable.of_bound haesm_h' C ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with t ht
  exact hC _ ⟨t, huIoc_sub ht, rfl⟩

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
subinterval `[c, d] ⊆ [[a, b]]`. An instance of `piecewise_gluing_induction`, shared with
`IsPiecewiseC1On.intervalIntegrable_deriv`'s identical breakpoint-splitting induction. -/
private theorem isBounded_image_deriv_aux {γ : ℝ → ℂ} {a b : ℝ} {p : Finset ℝ}
    (hC1 : ∀ c d : ℝ, Icc c d ⊆ uIcc a b → Disjoint (↑p : Set ℝ) (Ioo c d) →
      ContDiffOn ℝ 1 γ (Icc c d)) :
    ∀ n (c d : ℝ), (p.filter (· ∈ Ioo c d)).card ≤ n → c ≤ d → Icc c d ⊆ uIcc a b →
      Bornology.IsBounded (deriv γ '' Icc c d) :=
  piecewise_gluing_induction
    (fun c d hcd hsub hdisj => isBounded_image_deriv_of_contDiffOn hcd (hC1 c d hsub hdisj))
    (fun c m d hcm hmd h₁ h₂ => by
      -- Split at the shared breakpoint `m` so the two pieces' boundedness facts `h₁`, `h₂`
      -- combine via `Set.image_union` into one on the whole `Icc c d`.
      have hsplit : Icc c d = Icc c m ∪ Icc m d := (Set.Icc_union_Icc_eq_Icc hcm hmd).symm
      rw [hsplit, Set.image_union]
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
    (hdiff : DifferentiableOn ℝ γ (Icc t d)) (htd : t < d) :
    derivWithin γ (Icc t d) t ≠ 0 := by
  obtain ⟨d', hlt', -, hC1', hne'⟩ := h_imm.exists_Icc_piece_right ht₀
  have hte : t < min d d' := lt_min htd hlt'
  have h1 : HasDerivWithinAt γ (derivWithin γ (Icc t d) t) (Icc t (min d d')) t :=
    (hdiff t (left_mem_Icc.mpr htd.le)).hasDerivWithinAt.mono
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
    (hdiff : DifferentiableOn ℝ γ (Icc c t)) (hct : c < t) :
    derivWithin γ (Icc c t) t ≠ 0 := by
  obtain ⟨c', hlt', -, hC1', hne'⟩ := h_imm.exists_Icc_piece_left ht₀
  have het : max c c' < t := max_lt hct hlt'
  have h1 : HasDerivWithinAt γ (derivWithin γ (Icc c t) t) (Icc (max c c') t) t :=
    (hdiff t (right_mem_Icc.mpr hct.le)).hasDerivWithinAt.mono
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

/-- **The real bounded-integrand formula's boundedness, integrability, and Cauchy-PV facts, from
interior crossings alone** (Hungerbühler–Wasem Prop 2.3's analytic content). Unlike
`bounded_integrable_eq_real_integral_of_closed_interior_crossings` below, this needs no closedness
assumption: closedness is only used to show the principal value's real part vanishes, which is a
one-line addition on top of what this theorem already supplies (`L.re = Real.log ‖γ b - s‖ -
Real.log ‖γ a - s‖`, zero exactly when `γ a = γ b`).

Unlike the off-curve case, the real winding integrand `h t := realWindingIntegrand (γ t - s)
(deriv γ t)`'s boundedness and interval-integrability are not assumed here: both are derived from
the crossing regularity, via
`exists_isBounded_image_realWindingIntegrand_of_lipschitzOnWith_derivWithin_corner`'s boundedness
at each `C^{1,1}` crossing, its continuity off the crossing itself giving the measurability half,
and the ordinary avoidance argument between crossings — the actual content of HW Prop 2.3. -/
private theorem isBounded_intervalIntegrable_cauchyPV_of_interior_crossings
    {γ : ℝ → ℂ} {a b : ℝ} {s : ℂ} (h_imm : IsPwC1ImmersionOn γ a b) (hab : a ≤ b)
    (h_interior : ∀ t ∈ Icc a b, γ t = s → t ∈ Ioo a b)
    (hγ_lip : ∀ t ∈ Icc a b, γ t = s → ∃ εR > 0, ∃ KR : ℝ≥0,
      DifferentiableOn ℝ γ (Icc t (t + εR)) ∧ LipschitzOnWith KR (derivWithin γ (Icc t (t + εR)))
        (Icc t (t + εR)) ∧
      ∃ εL > 0, ∃ KL : ℝ≥0,
      DifferentiableOn ℝ γ (Icc (t - εL) t) ∧ LipschitzOnWith KL (derivWithin γ (Icc (t - εL) t))
        (Icc (t - εL) t)) :
    Bornology.IsBounded ((fun t => realWindingIntegrand (γ t - s) (deriv γ t)) '' Icc a b) ∧
    IntervalIntegrable (fun t => realWindingIntegrand (γ t - s) (deriv γ t)) volume a b ∧
    ∃ L : ℂ, HasCauchyPVAt γ a b (fun z => (z - s)⁻¹) s L ∧
      L.re = Real.log ‖γ b - s‖ - Real.log ‖γ a - s‖ ∧
      L.im = ∫ t in a..b, realWindingIntegrand (γ t - s) (deriv γ t) := by
  classical
  rcases hab.eq_or_lt with rfl | hab
  · refine ⟨?_, .refl, 0, HasCauchyPVAt.of_eq γ rfl _ s, by simp, by simp⟩
    -- A degenerate `[a, a]` interval is a single point, trivially bounded.
    have hsingle : Icc a a = {a} := Set.Icc_self a
    rw [hsingle, Set.image_singleton]
    exact (Set.finite_singleton _).isBounded
  set T : Finset ℝ := (h_imm.finite_crossings (z₀ := s)).toFinset with hT_def
  have hT_mem : ∀ {t : ℝ}, t ∈ T ↔ t ∈ Icc a b ∧ γ t = s := fun {_} => by
    rw [hT_def, h_imm.mem_toFinset_finite_crossings, uIcc_of_le hab.le]
  have h_complete : ∀ t ∈ Icc a b, γ t = s → t ∈ T := fun t ht h_eq => hT_mem.mpr ⟨ht, h_eq⟩
  have h_Ioo : ∀ t ∈ T, t ∈ Ioo a b := fun t ht =>
    h_interior t (hT_mem.mp ht).1 (hT_mem.mp ht).2
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
    fun t₀ (ht₀ : t₀ ∈ T) =>
      exists_radius_perWindow_tendsto_log_norm_add_arg h_imm hab (h_Ioo t₀ ht₀)
        (hT_mem.mp ht₀).2
  -- The crossing regularity: a `C^{1,1}` neighborhood on each side of each crossing (possibly a
  -- corner, so the two sides may disagree), and the boundedness of the real winding integrand
  -- each side already buys on a (possibly smaller) one-sided window. Each side's forced non-zero
  -- velocity is not assumed here -- `IsPwC1ImmersionOn` already forces it.
  choose! εR hεR_pos KR hdiffR hlipR εL hεL_pos KL hdiffL hlipL using fun t₀ (ht₀ : t₀ ∈ T) =>
    hγ_lip t₀ (hT_mem.mp ht₀).1 (hT_mem.mp ht₀).2
  have h_Ico : ∀ t ∈ T, t ∈ Ico (min a b) (max a b) := fun t ht => by
    rw [min_eq_left hab.le, max_eq_right hab.le]; exact ⟨(h_Ioo t ht).1.le, (h_Ioo t ht).2⟩
  have h_Ioc : ∀ t ∈ T, t ∈ Ioc (min a b) (max a b) := fun t ht => by
    rw [min_eq_left hab.le, max_eq_right hab.le]; exact ⟨(h_Ioo t ht).1, (h_Ioo t ht).2.le⟩
  -- `_corner` gives one bounded symmetric window per crossing directly, so the one-sided
  -- `_right`/`_left` windows never need computing and re-combining by hand.
  choose! ρ_lip hρ_lip_pos hρ_lip_lt hρ_lip_bdd using fun t₀ (ht₀ : t₀ ∈ T) =>
    exists_isBounded_image_realWindingIntegrand_of_lipschitzOnWith_derivWithin_corner
      (c := t₀ - εL t₀) (d := t₀ + εR t₀) (by linarith [hεL_pos t₀ ht₀])
      (by linarith [hεR_pos t₀ ht₀])
      (hdiffR t₀ ht₀) (hlipR t₀ ht₀) (hdiffL t₀ ht₀) (hlipL t₀ ht₀) (hT_mem.mp ht₀).2
      (derivWithin_ne_zero_of_isPwC1ImmersionOn_right h_imm (h_Ico t₀ ht₀) (hdiffR t₀ ht₀)
        (by linarith [hεR_pos t₀ ht₀]))
      (derivWithin_ne_zero_of_isPwC1ImmersionOn_left h_imm (h_Ioc t₀ ht₀) (hdiffL t₀ ht₀)
        (by linarith [hεL_pos t₀ ht₀]))
  -- The one-sided windows the window-integrability lemma needs are just the two halves of the
  -- symmetric window `_corner` already bounded.
  have hbddR : ∀ t₀ ∈ T, Bornology.IsBounded
      ((fun t => realWindingIntegrand (γ t - s) (deriv γ t)) '' Icc t₀ (t₀ + ρ_lip t₀)) :=
    fun t₀ ht₀ => (hρ_lip_bdd t₀ ht₀).subset (Set.image_mono
      (Icc_subset_Icc (by linarith [hρ_lip_pos t₀ ht₀]) le_rfl))
  have hbddL : ∀ t₀ ∈ T, Bornology.IsBounded
      ((fun t => realWindingIntegrand (γ t - s) (deriv γ t)) '' Icc (t₀ - ρ_lip t₀) t₀) :=
    fun t₀ ht₀ => (hρ_lip_bdd t₀ ht₀).subset (Set.image_mono
      (Icc_subset_Icc le_rfl (by linarith [hρ_lip_pos t₀ ht₀])))
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
    refine sorted_crossing_gluing_induction
      (fun l u hA hlu hu h_far' => ?_) (fun _ _ _ _ _ h₁ h₂ => h₁.trans h₂)
      (T.sort (· ≤ ·)) (Finset.sortedLT_sort T)
      (fun _ => hρ_pos.le) a le_rfl hab.le
      (fun t ht => by linarith [(h_endpts t ((Finset.mem_sort _).mp ht)).1])
      (fun t ht => by linarith [(h_endpts t ((Finset.mem_sort _).mp ht)).2])
      (fun t ht t' ht' hne => (h_pair t ((Finset.mem_sort _).mp ht) t'
        ((Finset.mem_sort _).mp ht') hne).le)
      (fun t ht => by
        have ht' := (Finset.mem_sort _).mp ht
        have hlt := hρ_lip_lt t ht'
        have hL : ρ_lip t ≤ εL t := by
          linarith [min_le_right (t + εR t - t) (t - (t - εL t))]
        have hR : ρ_lip t ≤ εR t := by
          linarith [min_le_left (t + εR t - t) (t - (t - εL t))]
        have hρ_le_ρlip' : ρ ≤ ρ_lip t := hρ_le_ρlip t ht'
        exact (intervalIntegrable_realWindingIntegrand_window (by linarith [hρ_pos])
            (Icc_subset_Icc (by linarith) le_rfl) (Icc_subset_Icc (by linarith) le_rfl)
            (hdiffL t ht') (hlipL t ht') (hbddL t ht')).trans
          (intervalIntegrable_realWindingIntegrand_window (by linarith [hρ_pos])
            (Icc_subset_Icc le_rfl (by linarith)) (Icc_subset_Icc le_rfl (by linarith))
            (hdiffR t ht') (hlipR t ht') (hbddR t ht')))
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
  -- exactly that real part built in already (`exists_radius_perWindow_tendsto_log_norm_add_arg`).
  obtain ⟨L, hHCPV, hRe0⟩ := cauchyPVExistsAt_of_perWindow_tendsto_of_interiorDisjoint_re_boundary
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
  exact ⟨h_bdd, h_int, L, hHCPV, hRe0, hIm⟩

/-- **The real bounded-integrand formula, allowing crossings** (Hungerbühler–Wasem Prop 2.3),
bundled with the boundedness and interval-integrability facts it is built from. Kept private and
conjunctive to avoid an overlong public name; see
`isBounded_image_realWindingIntegrand_of_interior_crossings`,
`intervalIntegrable_realWindingIntegrand_of_interior_crossings`, and
`windingNumber_eq_real_integral_of_closed_interior_crossings` below for its three public
projections, and for the full documentation of the hypotheses.

A thin closedness wrapper around
`isBounded_intervalIntegrable_cauchyPV_of_interior_crossings`: closedness (`hclosed`, `hsa`) is
used only to show every crossing is interior and that the principal value's real part vanishes
(`Real.log ‖γ b - s‖ - Real.log ‖γ a - s‖ = 0` when `γ a = γ b`); the boundedness, integrability,
and Cauchy-PV construction themselves need no closedness assumption. -/
private theorem bounded_integrable_eq_real_integral_of_closed_interior_crossings
    {γ : ℝ → ℂ} {a b : ℝ}
    {s : ℂ} (h_imm : IsPwC1ImmersionOn γ a b) (hab : a ≤ b) (hclosed : γ a = γ b) (hsa : γ a ≠ s)
    (hγ_lip : ∀ t ∈ Icc a b, γ t = s → ∃ εR > 0, ∃ KR : ℝ≥0,
      DifferentiableOn ℝ γ (Icc t (t + εR)) ∧ LipschitzOnWith KR (derivWithin γ (Icc t (t + εR)))
        (Icc t (t + εR)) ∧
      ∃ εL > 0, ∃ KL : ℝ≥0,
      DifferentiableOn ℝ γ (Icc (t - εL) t) ∧ LipschitzOnWith KL (derivWithin γ (Icc (t - εL) t))
        (Icc (t - εL) t)) :
    Bornology.IsBounded ((fun t => realWindingIntegrand (γ t - s) (deriv γ t)) '' Icc a b) ∧
    IntervalIntegrable (fun t => realWindingIntegrand (γ t - s) (deriv γ t)) volume a b ∧
    windingNumber γ a b s
      = ((1 / (2 * Real.pi)
          * ∫ t in a..b, realWindingIntegrand (γ t - s) (deriv γ t) : ℝ) : ℂ) := by
  -- Every crossing is interior: on `[a, b]`, `t ∈ Ioo a b` reduces to `t ≠ a ∧ t ≠ b`, and both
  -- endpoints avoid `s` -- `a` directly by `hsa`, `b` via `hclosed : γ a = γ b`.
  have h_interior : ∀ t ∈ Icc a b, γ t = s → t ∈ Ioo a b := fun t ht h_eq =>
    ⟨ht.1.lt_of_ne (by rintro rfl; exact hsa h_eq),
      ht.2.lt_of_ne (by intro h; exact hsa (hclosed.trans (h ▸ h_eq)))⟩
  obtain ⟨h_bdd, h_int, L, hHCPV, hRe0, hIm⟩ :=
    isBounded_intervalIntegrable_cauchyPV_of_interior_crossings h_imm hab h_interior hγ_lip
  refine ⟨h_bdd, h_int, ?_⟩
  have hwind : windingNumber γ a b s = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * L :=
    windingNumber_eq_of_hasCauchyPVAt hHCPV
  have hRe : L.re = 0 := by rw [hRe0, hclosed, sub_self]
  rw [hwind, ← Complex.re_add_im L, hRe, hIm]
  have h2πI_ne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := Complex.two_pi_I_ne_zero
  push_cast
  field_simp
  ring

/-- **The real winding integrand is bounded on all of `[a, b]` for an immersion with interior
crossings** (Hungerbühler–Wasem Prop 2.3, boundedness half). Projection of
`isBounded_intervalIntegrable_cauchyPV_of_interior_crossings`; needs no closedness, only that
every crossing of `s` is interior to `[a, b]`. See
`windingNumber_eq_real_integral_of_closed_interior_crossings` below for the closed-curve
equality and the full documentation of `hγ_lip`. -/
theorem isBounded_image_realWindingIntegrand_of_interior_crossings
    {γ : ℝ → ℂ} {a b : ℝ} {s : ℂ} (h_imm : IsPwC1ImmersionOn γ a b) (hab : a ≤ b)
    (h_interior : ∀ t ∈ Icc a b, γ t = s → t ∈ Ioo a b)
    (hγ_lip : ∀ t ∈ Icc a b, γ t = s → ∃ εR > 0, ∃ KR : ℝ≥0,
      DifferentiableOn ℝ γ (Icc t (t + εR)) ∧ LipschitzOnWith KR (derivWithin γ (Icc t (t + εR)))
        (Icc t (t + εR)) ∧
      ∃ εL > 0, ∃ KL : ℝ≥0,
      DifferentiableOn ℝ γ (Icc (t - εL) t) ∧ LipschitzOnWith KL (derivWithin γ (Icc (t - εL) t))
        (Icc (t - εL) t)) :
    Bornology.IsBounded ((fun t => realWindingIntegrand (γ t - s) (deriv γ t)) '' Icc a b) :=
  (isBounded_intervalIntegrable_cauchyPV_of_interior_crossings h_imm hab h_interior hγ_lip).1

/-- **The real winding integrand is interval-integrable along an immersion with interior
crossings** (Hungerbühler–Wasem Prop 2.3, integrability half). Projection of
`isBounded_intervalIntegrable_cauchyPV_of_interior_crossings`; needs no closedness, only that
every crossing of `s` is interior to `[a, b]`. See
`windingNumber_eq_real_integral_of_closed_interior_crossings` below for the closed-curve
equality and the full documentation of `hγ_lip`. -/
theorem intervalIntegrable_realWindingIntegrand_of_interior_crossings
    {γ : ℝ → ℂ} {a b : ℝ} {s : ℂ} (h_imm : IsPwC1ImmersionOn γ a b) (hab : a ≤ b)
    (h_interior : ∀ t ∈ Icc a b, γ t = s → t ∈ Ioo a b)
    (hγ_lip : ∀ t ∈ Icc a b, γ t = s → ∃ εR > 0, ∃ KR : ℝ≥0,
      DifferentiableOn ℝ γ (Icc t (t + εR)) ∧ LipschitzOnWith KR (derivWithin γ (Icc t (t + εR)))
        (Icc t (t + εR)) ∧
      ∃ εL > 0, ∃ KL : ℝ≥0,
      DifferentiableOn ℝ γ (Icc (t - εL) t) ∧ LipschitzOnWith KL (derivWithin γ (Icc (t - εL) t))
        (Icc (t - εL) t)) :
    IntervalIntegrable (fun t => realWindingIntegrand (γ t - s) (deriv γ t)) volume a b :=
  (isBounded_intervalIntegrable_cauchyPV_of_interior_crossings h_imm hab h_interior hγ_lip).2.1

/-- **The real bounded-integrand formula, allowing crossings** (Hungerbühler–Wasem Prop 2.3).
For a closed piecewise-`C¹` immersion `γ` on `[a, b]` that avoids `s` at the basepoint `a`
(`hsa`, so also at `b` by closedness — every other crossing of `s`, if any, is automatically
interior to `[a, b]`) and is `C^{1,1}` on each side of any such crossing (`derivWithin γ`
Lipschitz on a one-sided closed piece ending or starting there, `hγ_lip` — the two sides need not
agree, so a crossing may coincide with a breakpoint of the immersion) — in particular satisfied
vacuously if `γ` never meets `s` — the generalized winding number `n_s(γ)` is a real number equal
to its ordinary (non-principal-value) integral:

`n_s(γ) = (1 / 2π) ∫_a^b (x ẏ - y ẋ) / (x² + y²) dt`, `x + i y = γ - s`.

The two sides of a crossing need not agree: `hγ_lip` allows the crossing to coincide with a
breakpoint of the piecewise-`C¹` immersion (a corner), matching Hungerbühler–Wasem's own proof of
Prop 2.3, which handles that case via the same one-sided splitting (arXiv:1808.00997, p. 9). -/
theorem windingNumber_eq_real_integral_of_closed_interior_crossings
    {γ : ℝ → ℂ} {a b : ℝ} {s : ℂ} (h_imm : IsPwC1ImmersionOn γ a b) (hab : a ≤ b)
    (hclosed : γ a = γ b) (hsa : γ a ≠ s)
    (hγ_lip : ∀ t ∈ Icc a b, γ t = s → ∃ εR > 0, ∃ KR : ℝ≥0,
      DifferentiableOn ℝ γ (Icc t (t + εR)) ∧ LipschitzOnWith KR (derivWithin γ (Icc t (t + εR)))
        (Icc t (t + εR)) ∧
      ∃ εL > 0, ∃ KL : ℝ≥0,
      DifferentiableOn ℝ γ (Icc (t - εL) t) ∧ LipschitzOnWith KL (derivWithin γ (Icc (t - εL) t))
        (Icc (t - εL) t)) :
    windingNumber γ a b s
      = ((1 / (2 * Real.pi)
          * ∫ t in a..b, realWindingIntegrand (γ t - s) (deriv γ t) : ℝ) : ℂ) :=
  (bounded_integrable_eq_real_integral_of_closed_interior_crossings
    h_imm hab hclosed hsa hγ_lip).2.2

end TauCeti.Contour

end

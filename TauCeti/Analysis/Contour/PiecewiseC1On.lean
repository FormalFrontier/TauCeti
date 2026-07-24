/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Piecewise `C¹` curves on an interval

The contour-integration roadmap states its objects — the generalized winding number, the contour
integral, and the Hungerbühler--Wasem regularity conditions — for a **piecewise `C¹`** curve
`γ : ℝ → ℂ` on the closed interval `[[a, b]]` between two parameters (in either order): continuous
there, and `C¹` on each piece between finitely many breakpoints. This file introduces
that regularity as a predicate `Contour.IsPiecewiseC1On γ a b` on the raw function `γ` itself —
following the roadmap's function-based design, with no bundled path type — together with its API.

The predicate is the regularity a "regularity package" will use to *discharge* the integrand-level
hypotheses — continuity, pointwise differentiability, and integrability — that the raw
contour-integral lemmas take directly. Those lemmas do not consume the predicate themselves: the
fundamental theorem of calculus along a contour in `Contour.ArcFTC`, for instance, is stated on the
integrand so it works with any regularity package that supplies these hypotheses. The predicate is a
prerequisite for the homology Cauchy theorem and the generalized residue theorem.

## Main definitions

* `Contour.IsPiecewiseC1On γ a b` — `γ` is continuous on `[[a, b]]` and `C¹` on every closed
  subinterval whose interior avoids a fixed finite breakpoint set in `(min a b, max a b)`.

## Main results

* `Contour.isPiecewiseC1On_iff` — unfold the predicate to its defining clauses.
* `Contour.IsPiecewiseC1On.continuousOn` — the underlying continuity on `[[a, b]]`.
* `Contour.IsPiecewiseC1On.of_contDiffOn` — a `C¹` curve is piecewise `C¹`, with no breakpoints.
* `Contour.IsPiecewiseC1On.of_breakpoints`, `Contour.IsPiecewiseC1On.exists_breakpoints` —
  introduce the predicate from, and eliminate it to, a finite breakpoint witness.
* `Contour.IsPiecewiseC1On.mono` — restrict the regularity to a subinterval `[[c, d]] ⊆ [[a, b]]`.
* `Contour.isPiecewiseC1On_comm`, `Contour.IsPiecewiseC1On.symm` — endpoint-swap invariance.
* `Contour.IsPiecewiseC1On.exists_finset_differentiableAt`,
  `Contour.IsPiecewiseC1On.exists_countable_differentiableAt` — differentiability off a finite
  (hence countable) set, in the exact shapes the raw contour-integral lemmas consume.
* `Contour.IsPiecewiseC1On.eventually_differentiableAt` (and its `_right`/`_left` one-sided
  corollaries) — eventual differentiability near an interior parameter.
* `Contour.IsPiecewiseC1On.intervalIntegrable_deriv` — the derivative is interval-integrable on
  `a..b`, glued across the breakpoints from the `C¹` pieces.

## Provenance

Adapted from the regularity fields of the `PiecewiseC1PathOn` structure in the AINTLIB
`LeanModularForms` development, re-expressed as a predicate on a raw function `γ : ℝ → ℂ` per the
roadmap's function-based contour design rather than as a bundled path type. The piece-level
integrability of the derivative and its gluing across the breakpoints
(`IsPiecewiseC1On.intervalIntegrable_deriv`) follow `ClosedPwC1Curve.deriv_intervalIntegrable_piece`
and `ClosedPwC1Curve.deriv_extend_intervalIntegrable` in the same development's
`PaperPwC1Immersion.lean`, restated for the raw curve.
-/

public section

noncomputable section

namespace TauCeti.Contour

open Filter MeasureTheory Set Topology

variable {γ : ℝ → ℂ} {a b : ℝ}

/-- **Piecewise `C¹` on the interval between `a` and `b`.** The curve `γ : ℝ → ℂ` is continuous on
the closed interval `[[a, b]]` (unordered, hence orientation-robust), and there is a finite set of
breakpoints `p ⊆ (min a b, max a b)` such that `γ` is `C¹` on every closed subinterval of `[[a, b]]`
whose interior avoids `p`. Equivalently `γ` is continuously differentiable on each piece between
consecutive breakpoints, with corners allowed only at the breakpoints; an unbounded-derivative cusp
such as `t ↦ √|t|` is excluded, being not `C¹` up to the breakpoint. This is the raw-function form
of the roadmap's piecewise-`C¹` curve — a `Prop` on `γ` itself, with no bundled path type. -/
def IsPiecewiseC1On (γ : ℝ → ℂ) (a b : ℝ) : Prop :=
  ContinuousOn γ (uIcc a b) ∧
    ∃ p : Finset ℝ, ↑p ⊆ Ioo (min a b) (max a b) ∧
      ∀ c d : ℝ, Icc c d ⊆ uIcc a b → Disjoint (↑p : Set ℝ) (Ioo c d) →
        ContDiffOn ℝ 1 γ (Icc c d)

/-- `IsPiecewiseC1On` unfolded to its defining clauses: continuity on `[[a, b]]`, and a finite
breakpoint set off which every breakpoint-free closed subinterval carries a `C¹` restriction. -/
theorem isPiecewiseC1On_iff :
    IsPiecewiseC1On γ a b ↔
      ContinuousOn γ (uIcc a b) ∧
        ∃ p : Finset ℝ, ↑p ⊆ Ioo (min a b) (max a b) ∧
          ∀ c d : ℝ, Icc c d ⊆ uIcc a b → Disjoint (↑p : Set ℝ) (Ioo c d) →
            ContDiffOn ℝ 1 γ (Icc c d) :=
  Iff.rfl

/-- A piecewise-`C¹` curve is continuous on the parameter interval `[[a, b]]`. -/
theorem IsPiecewiseC1On.continuousOn (h : IsPiecewiseC1On γ a b) :
    ContinuousOn γ (uIcc a b) :=
  h.1

/-- A `C¹` curve on `[[a, b]]` is piecewise `C¹`, with no breakpoints. -/
theorem IsPiecewiseC1On.of_contDiffOn (h : ContDiffOn ℝ 1 γ (uIcc a b)) :
    IsPiecewiseC1On γ a b :=
  ⟨h.continuousOn, ∅, by simp, fun c d hcd _ => h.mono hcd⟩

/-- Build a piecewise-`C¹` curve from continuity on `[[a, b]]` together with a finite breakpoint set
off which every breakpoint-free closed subinterval carries a `C¹` restriction. -/
theorem IsPiecewiseC1On.of_breakpoints (hcont : ContinuousOn γ (uIcc a b)) (p : Finset ℝ)
    (hp : ↑p ⊆ Ioo (min a b) (max a b))
    (hC1 : ∀ c d : ℝ, Icc c d ⊆ uIcc a b → Disjoint (↑p : Set ℝ) (Ioo c d) →
      ContDiffOn ℝ 1 γ (Icc c d)) :
    IsPiecewiseC1On γ a b :=
  ⟨hcont, p, hp, hC1⟩

/-- Extract the finite breakpoint set of a piecewise-`C¹` curve, together with the `C¹` restriction
it induces on every breakpoint-free closed subinterval of `[[a, b]]`. -/
theorem IsPiecewiseC1On.exists_breakpoints (h : IsPiecewiseC1On γ a b) :
    ∃ p : Finset ℝ, ↑p ⊆ Ioo (min a b) (max a b) ∧
      ∀ c d : ℝ, Icc c d ⊆ uIcc a b → Disjoint (↑p : Set ℝ) (Ioo c d) →
        ContDiffOn ℝ 1 γ (Icc c d) :=
  h.2

/-- Piecewise-`C¹` regularity restricts to any subinterval: if `γ` is piecewise `C¹` on `[[a, b]]`
and `[[c, d]] ⊆ [[a, b]]`, then `γ` is piecewise `C¹` on `[[c, d]]`, with the breakpoint set cut
down to the smaller interior. -/
theorem IsPiecewiseC1On.mono (h : IsPiecewiseC1On γ a b) {c d : ℝ}
    (hsub : uIcc c d ⊆ uIcc a b) : IsPiecewiseC1On γ c d := by
  obtain ⟨p, _, hC1⟩ := h.exists_breakpoints
  refine ⟨h.continuousOn.mono hsub, p.filter (fun x => x ∈ Ioo (min c d) (max c d)), ?_, ?_⟩
  · intro x hx
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx
    exact hx.2
  · intro u v huv hdis
    refine hC1 u v (huv.trans hsub) ?_
    rw [Set.disjoint_left] at hdis ⊢
    intro x hxp hxuv
    rw [← Set.Icc_min_max] at huv
    obtain ⟨hlu, hvu⟩ := (Set.Icc_subset_Icc_iff (hxuv.1.trans hxuv.2).le).1 huv
    refine hdis ?_ hxuv
    simp only [Finset.coe_filter, Set.mem_setOf_eq]
    exact ⟨hxp, lt_of_le_of_lt hlu hxuv.1, lt_of_lt_of_le hxuv.2 hvu⟩

/-- Piecewise-`C¹` regularity is symmetric in the endpoints, since `[[a, b]] = [[b, a]]`. -/
theorem isPiecewiseC1On_comm : IsPiecewiseC1On γ a b ↔ IsPiecewiseC1On γ b a := by
  simp only [isPiecewiseC1On_iff, Set.uIcc_comm a b, min_comm a b, max_comm a b]

/-- Piecewise-`C¹` regularity is invariant under swapping the endpoints of the interval. -/
theorem IsPiecewiseC1On.symm (h : IsPiecewiseC1On γ a b) : IsPiecewiseC1On γ b a :=
  isPiecewiseC1On_comm.mp h

/-- Around any interior parameter outside a closed set `s` there is a closed subinterval of
`[[a, b]]` whose interior contains `t` and is disjoint from `s`. -/
theorem exists_Icc_subset_uIcc_disjoint {s : Set ℝ} (hs : IsClosed s) {t : ℝ}
    (ht : t ∈ Ioo (min a b) (max a b)) (hts : t ∉ s) :
    ∃ c d : ℝ, t ∈ Ioo c d ∧ Icc c d ⊆ uIcc a b ∧ Disjoint s (Ioo c d) := by
  have hopen : IsOpen (Ioo (min a b) (max a b) \ s) := isOpen_Ioo.sdiff hs
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen t ⟨ht, hts⟩
  rw [Real.ball_eq_Ioo] at hball
  refine ⟨t - ε / 2, t + ε / 2, by constructor <;> linarith, fun x hx => ?_, ?_⟩
  · have hxs := hball (show x ∈ Ioo (t - ε) (t + ε) from ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    exact Icc_min_max.subset (Ioo_subset_Icc_self hxs.1)
  · rw [Set.disjoint_right]
    intro x hx
    exact (hball (show x ∈ Ioo (t - ε) (t + ε) from
      ⟨by linarith [hx.1], by linarith [hx.2]⟩)).2

/-- **Differentiability off a finite set.** A piecewise-`C¹` curve is differentiable at every
interior parameter outside a finite set — the breakpoints. -/
theorem IsPiecewiseC1On.exists_finset_differentiableAt (h : IsPiecewiseC1On γ a b) :
    ∃ p : Finset ℝ,
      ∀ t ∈ Ioo (min a b) (max a b) \ (↑p : Set ℝ), DifferentiableAt ℝ γ t := by
  obtain ⟨p, -, hC1⟩ := h.exists_breakpoints
  refine ⟨p, fun t ht => ?_⟩
  obtain ⟨c, d, htcd, hsub, hdisj⟩ :=
    exists_Icc_subset_uIcc_disjoint p.finite_toSet.isClosed ht.1 ht.2
  exact ((hC1 c d hsub hdisj).differentiableOn one_ne_zero).differentiableAt
    (Icc_mem_nhds htcd.1 htcd.2)

/-- **Differentiability off a countable set.** A piecewise-`C¹` curve is differentiable at every
interior parameter outside a countable set — the breakpoints. This is the exact regularity shape
consumed by the raw contour-integral development (Dixon's argument and the winding-number
machinery). -/
theorem IsPiecewiseC1On.exists_countable_differentiableAt (h : IsPiecewiseC1On γ a b) :
    ∃ P : Set ℝ, P.Countable ∧
      ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ t :=
  let ⟨p, hp⟩ := h.exists_finset_differentiableAt
  ⟨↑p, p.countable_toSet, hp⟩

/-- **Eventual differentiability near an interior parameter**, on any within-filter avoiding
the parameter itself. -/
theorem IsPiecewiseC1On.eventually_differentiableAt (h : IsPiecewiseC1On γ a b) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo (min a b) (max a b)) {u : Set ℝ} (hu : t₀ ∉ u) :
    ∀ᶠ t in 𝓝[u] t₀, DifferentiableAt ℝ γ t := by
  obtain ⟨p, hp⟩ := h.exists_finset_differentiableAt
  have hcl : IsClosed ((↑p \ {t₀} : Set ℝ)) := (p.finite_toSet.subset sdiff_subset).isClosed
  filter_upwards [nhdsWithin_le_nhds (hcl.isOpen_compl.mem_nhds (by simp)),
    nhdsWithin_le_nhds (isOpen_Ioo.mem_nhds ht₀), self_mem_nhdsWithin] with t htc htIoo htu
  exact hp t ⟨htIoo, fun htp => htc ⟨htp, fun h_eq => hu (h_eq ▸ htu)⟩⟩

/-- Eventual differentiability from the right at an interior parameter. -/
theorem IsPiecewiseC1On.eventually_differentiableAt_right (h : IsPiecewiseC1On γ a b)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (min a b) (max a b)) :
    ∀ᶠ t in 𝓝[>] t₀, DifferentiableAt ℝ γ t :=
  h.eventually_differentiableAt ht₀ self_notMem_Ioi

/-- Eventual differentiability from the left at an interior parameter. -/
theorem IsPiecewiseC1On.eventually_differentiableAt_left (h : IsPiecewiseC1On γ a b)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (min a b) (max a b)) :
    ∀ᶠ t in 𝓝[<] t₀, DifferentiableAt ℝ γ t :=
  h.eventually_differentiableAt ht₀ self_notMem_Iio

/-- The derivative of a curve that is `C¹` on `[c, d]` is interval-integrable on `c..d`: the
within-interval derivative is continuous on the compact piece, and agrees with `deriv` on the
interior, hence almost everywhere. -/
private theorem intervalIntegrable_deriv_of_contDiffOn {c d : ℝ} (hcd : c ≤ d)
    (hC1 : ContDiffOn ℝ 1 γ (Icc c d)) :
    IntervalIntegrable (fun t ↦ deriv γ t) volume c d := by
  rcases eq_or_lt_of_le hcd with rfl | hlt
  · exact IntervalIntegrable.refl
  have hdw : ContinuousOn (derivWithin γ (Icc c d)) (Icc c d) :=
    hC1.continuousOn_derivWithin (uniqueDiffOn_Icc hlt) le_rfl
  have hint : IntervalIntegrable (derivWithin γ (Icc c d)) volume c d :=
    (hdw.mono (uIcc_of_le hcd).le).intervalIntegrable
  rw [intervalIntegrable_iff] at hint ⊢
  refine hint.congr ?_
  rw [uIoc_of_le hcd, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)

/-- Gluing step for `IsPiecewiseC1On.intervalIntegrable_deriv`: interval-integrability of the
derivative on any subinterval `[c, d] ⊆ [[a, b]]`, by induction on the number of breakpoints
strictly inside `(c, d)`, splitting off the largest one. -/
private theorem intervalIntegrable_deriv_aux {p : Finset ℝ}
    (hC1 : ∀ c d : ℝ, Icc c d ⊆ uIcc a b → Disjoint (↑p : Set ℝ) (Ioo c d) →
      ContDiffOn ℝ 1 γ (Icc c d)) :
    ∀ n (c d : ℝ), (p.filter (· ∈ Ioo c d)).card ≤ n → c ≤ d → Icc c d ⊆ uIcc a b →
      IntervalIntegrable (fun t ↦ deriv γ t) volume c d := by
  have hdisj : ∀ {c d : ℝ}, p.filter (· ∈ Ioo c d) = ∅ → Disjoint (↑p : Set ℝ) (Ioo c d) :=
    fun he => Set.disjoint_left.mpr fun x hxp hx =>
      Finset.notMem_empty x (he ▸ Finset.mem_filter.mpr ⟨Finset.mem_coe.mp hxp, hx⟩)
  intro n
  induction n with
  | zero =>
    intro c d hcard hcd hsub
    have he : p.filter (· ∈ Ioo c d) = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    exact intervalIntegrable_deriv_of_contDiffOn hcd (hC1 c d hsub (hdisj he))
  | succ n ih =>
    intro c d hcard hcd hsub
    rcases (p.filter (· ∈ Ioo c d)).eq_empty_or_nonempty with he | hne
    · exact intervalIntegrable_deriv_of_contDiffOn hcd (hC1 c d hsub (hdisj he))
    set m := (p.filter (· ∈ Ioo c d)).max' hne with hm_def
    obtain ⟨hmp, hm⟩ := Finset.mem_filter.mp ((p.filter (· ∈ Ioo c d)).max'_mem hne)
    have hssub : p.filter (· ∈ Ioo c m) ⊂ p.filter (· ∈ Ioo c d) :=
      (Finset.ssubset_iff_of_subset (Finset.monotone_filter_right _ fun x _ hx =>
          ⟨hx.1, hx.2.trans hm.2⟩)).mpr
        ⟨m, Finset.mem_filter.mpr ⟨hmp, hm⟩, fun hmem =>
          (Finset.mem_filter.mp hmem).2.2.false⟩
    have h₁ : IntervalIntegrable (fun t ↦ deriv γ t) volume c m :=
      ih c m (Nat.le_of_lt_succ ((Finset.card_lt_card hssub).trans_le hcard)) hm.1.le
        ((Icc_subset_Icc le_rfl hm.2.le).trans hsub)
    have h₂ : IntervalIntegrable (fun t ↦ deriv γ t) volume m d := by
      refine intervalIntegrable_deriv_of_contDiffOn hm.2.le
        (hC1 m d ((Icc_subset_Icc hm.1.le le_rfl).trans hsub) (Set.disjoint_left.mpr ?_))
      intro x hxp hx
      exact absurd ((p.filter (· ∈ Ioo c d)).le_max' x
          (Finset.mem_filter.mpr ⟨Finset.mem_coe.mp hxp, hm.1.trans hx.1, hx.2⟩))
        (not_le.mpr hx.1)
    exact h₁.trans h₂

/-- **Interval-integrability of the derivative.** The derivative of a piecewise-`C¹` curve is
interval-integrable on `a..b`: on each piece the within-derivative is continuous on a compact
interval and agrees with `deriv` almost everywhere, and the pieces glue across the finitely many
breakpoints. This discharges the `hderiv_int` hypothesis of the raw contour-integral lemmas. -/
theorem IsPiecewiseC1On.intervalIntegrable_deriv (h : IsPiecewiseC1On γ a b) :
    IntervalIntegrable (fun t ↦ deriv γ t) volume a b := by
  obtain ⟨p, -, hC1⟩ := h.exists_breakpoints
  have key := intervalIntegrable_deriv_aux hC1 (p.filter (· ∈ Ioo (min a b) (max a b))).card
    (min a b) (max a b) le_rfl min_le_max Icc_min_max.subset
  rcases le_total a b with hab | hab
  · simpa [min_eq_left hab, max_eq_right hab] using key
  · have key' : IntervalIntegrable (fun t ↦ deriv γ t) volume b a := by
      simpa [min_eq_right hab, max_eq_left hab] using key
    exact key'.symm

end TauCeti.Contour

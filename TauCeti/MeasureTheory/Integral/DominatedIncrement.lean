/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Maps of the line whose increments are dominated by a density

A map `g` defined on a set `s ⊆ ℝ` is said here to have its **increments dominated** by a density
`φ : ℝ → ℝ≥0∞` when

> `edist (g x) (g y) ≤ ∫⁻ t in Ioc x y, φ t` for all `x ≤ y` in `s`.

This is the conclusion the fundamental theorem of calculus delivers for a `C¹` map, with
`φ = ‖deriv g‖ₑ`; it is also the conclusion the chord bound of the length–area method delivers for
a holomorphic map restricted to a circular arc, with `φ` the angular length density
(`TauCeti.ofReal_dist_le_mul_lintegral_Ioc` in `Analysis/Complex/Conformal/LengthArea.lean`). What
this file records is that, on an order-connected `s` and for a density of **finite total
integral**, the domination alone forces two things:

* `g` has **bounded range** — indeed `Metric.ediam (g '' s) ≤ ∫⁻ t in s, φ t`, with no finiteness
  hypothesis at all (`TauCeti.ediam_image_le_of_edist_le_setLIntegral`); and
* `g` is **uniformly continuous** on `s`
  (`TauCeti.uniformContinuousOn_of_edist_le_setLIntegral`).

The second is the one with content, and it is the one that does not follow from bounded variation:
domination by a *finite* integral is an absolute-continuity statement, and the modulus of continuity
it yields comes from `MeasureTheory.exists_pos_setLIntegral_lt_of_measure_lt` — a short subinterval
carries little of the total integral, uniformly in where it sits. Nothing here needs `s` to be an
interval, only order-connected, so a half-line and the whole line are covered along with `Ioo a b`;
and nothing needs `φ` to be measurable, the integrals being lower integrals throughout.

## Why uniform continuity is the right conclusion

Uniform continuity is what a boundary-limit argument spends: on a complete target it turns the
Cauchy criterion at an endpoint of `s` into an honest limit there, so a map dominated by a density
of finite integral over `Ioo a b` extends continuously to `Icc a b`. The two statements below are
therefore stated in the packaged `UniformContinuousOn` / `Metric.ediam` vocabulary rather than in
`ε`–`δ` form; `Metric.uniformContinuousOn_iff_le` unpacks the first for a consumer that wants an
explicit modulus, and `Metric.isBounded_iff_ediam_ne_top` the second.

The target is an arbitrary pseudo-metric space: the domination hypothesis is a statement about
`edist`, and neither conclusion sees any linear structure. The domain is `ℝ` with Lebesgue measure,
which is where `Ioc x y` and its measure `ENNReal.ofReal (y - x)` — the two things the modulus
argument uses — live.

## Main results

* `TauCeti.ediam_image_le_of_edist_le_setLIntegral` — the image of an order-connected `s` under a
  map whose increments are dominated by `φ` has diameter at most `∫⁻ t in s, φ t`.
* `TauCeti.isBounded_image_of_edist_le_setLIntegral` — hence that image is bounded as soon as the
  total integral is finite.
* `TauCeti.uniformContinuousOn_of_edist_le_setLIntegral` — and the map is uniformly continuous on
  `s`, by absolute continuity of the integral.
-/

public section

namespace TauCeti

open MeasureTheory Set
open scoped ENNReal

variable {X : Type*} [PseudoMetricSpace X] {g : ℝ → X} {φ : ℝ → ℝ≥0∞} {s : Set ℝ}

/-- **The increments of `g` are dominated over all of `s`, not merely over subintervals.** On an
order-connected `s` the interval `Ioc x y` spanned by two of its points is again inside `s`, so the
domination hypothesis, stated for increasing pairs, extends to all pairs and to the total integral.

This is the whole of the order-connectedness hypothesis: it is what lets a bound over a subinterval
be compared with the total integral. -/
private lemma edist_le_setLIntegral (hs : s.OrdConnected)
    (hdom : ∀ x ∈ s, ∀ y ∈ s, x ≤ y → edist (g x) (g y) ≤ ∫⁻ t in Ioc x y, φ t)
    {x : ℝ} (hx : x ∈ s) {y : ℝ} (hy : y ∈ s) :
    edist (g x) (g y) ≤ ∫⁻ t in s, φ t := by
  have key : ∀ u ∈ s, ∀ v ∈ s, u ≤ v → edist (g u) (g v) ≤ ∫⁻ t in s, φ t := fun u hu v hv huv =>
    (hdom u hu v hv huv).trans
      (lintegral_mono_set (Ioc_subset_Icc_self.trans (hs.out hu hv)))
  rcases le_total x y with hxy | hxy
  · exact key x hx y hy hxy
  · rw [edist_comm]
    exact key y hy x hx hxy

/-- **A map whose increments are dominated by `φ` has image of diameter at most the total integral
of `φ`.** For an order-connected `s ⊆ ℝ` and a map `g` with
`edist (g x) (g y) ≤ ∫⁻ t in Ioc x y, φ t` for every increasing pair in `s`, the image `g '' s` has
`Metric.ediam` at most `∫⁻ t in s, φ t`.

No finiteness is assumed: the statement is in `ℝ≥0∞` and is vacuously true when the total integral
is infinite. Read for `φ = ‖deriv g‖ₑ` it is the statement that a curve is no wider than it is
long. -/
theorem ediam_image_le_of_edist_le_setLIntegral (hs : s.OrdConnected)
    (hdom : ∀ x ∈ s, ∀ y ∈ s, x ≤ y → edist (g x) (g y) ≤ ∫⁻ t in Ioc x y, φ t) :
    Metric.ediam (g '' s) ≤ ∫⁻ t in s, φ t := by
  refine Metric.ediam_le ?_
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact edist_le_setLIntegral hs hdom hx hy

/-- **A map whose increments are dominated by a density of finite integral has bounded image.**
The finiteness form of `TauCeti.ediam_image_le_of_edist_le_setLIntegral`, and the form a
compactness argument consumes: an unbounded set carries the junk value `0` for `Metric.diam`, so
boundedness is what makes a real-valued diameter bound meaningful. -/
theorem isBounded_image_of_edist_le_setLIntegral (hs : s.OrdConnected)
    (hdom : ∀ x ∈ s, ∀ y ∈ s, x ≤ y → edist (g x) (g y) ≤ ∫⁻ t in Ioc x y, φ t)
    (hfin : (∫⁻ t in s, φ t) ≠ ⊤) :
    Bornology.IsBounded (g '' s) :=
  Metric.isBounded_iff_ediam_ne_top.2
    (ne_top_of_le_ne_top hfin (ediam_image_le_of_edist_le_setLIntegral hs hdom))

/-- **A map whose increments are dominated by a density of finite integral is uniformly
continuous.** For an order-connected `s ⊆ ℝ` and a map `g` with
`edist (g x) (g y) ≤ ∫⁻ t in Ioc x y, φ t` for every increasing pair in `s`, finiteness of
`∫⁻ t in s, φ t` makes `g` uniformly continuous on `s`.

The modulus is uniform over `s` — in particular it does not degrade as an endpoint of `s` is
approached, which is the whole content — and it comes from the absolute continuity of the integral,
`MeasureTheory.exists_pos_setLIntegral_lt_of_measure_lt`: a subinterval short enough carries less
than `ENNReal.ofReal ε` of the total, wherever in `s` it sits, and by hypothesis the amount a
subinterval carries bounds the increment across it.

Absolute continuity is the exact input. Domination by a density that is merely *integrable over
compacts* would give continuity but no uniform modulus, and a bound on the total variation alone
would give neither: a monotone jump function has bounded variation and is not uniformly
continuous. -/
theorem uniformContinuousOn_of_edist_le_setLIntegral (hs : s.OrdConnected)
    (hdom : ∀ x ∈ s, ∀ y ∈ s, x ≤ y → edist (g x) (g y) ≤ ∫⁻ t in Ioc x y, φ t)
    (hfin : (∫⁻ t in s, φ t) ≠ ⊤) :
    UniformContinuousOn g s := by
  rw [Metric.uniformContinuousOn_iff_le]
  intro ε hε
  obtain ⟨δ, hδ, hδlt⟩ := exists_pos_setLIntegral_lt_of_measure_lt
    (μ := volume.restrict s) (f := φ) hfin (ENNReal.ofReal_pos.mpr hε).ne'
  -- a finite gauge below `δ`, so that a real-valued length may be compared with it
  obtain ⟨d, hd0, hdδ⟩ := exists_between hδ
  have hdtop : d ≠ ⊤ := (hdδ.trans_le le_top).ne
  -- the estimate for a pair in increasing order
  have key : ∀ x ∈ s, ∀ y ∈ s, x ≤ y → y - x ≤ d.toReal → dist (g x) (g y) ≤ ε := by
    intro x hx y hy hxy hgap
    have hsub : Ioc x y ⊆ s := Ioc_subset_Icc_self.trans (hs.out hx hy)
    have hmeas : (volume.restrict s) (Ioc x y) < δ := by
      refine lt_of_le_of_lt ((Measure.restrict_apply_le _ _).trans ?_) hdδ
      rw [Real.volume_Ioc, ← ENNReal.ofReal_toReal hdtop]
      exact ENNReal.ofReal_le_ofReal hgap
    have hres : (volume.restrict s).restrict (Ioc x y) = volume.restrict (Ioc x y) := by
      rw [Measure.restrict_restrict measurableSet_Ioc, inter_eq_self_of_subset_left hsub]
    have hlt : ∫⁻ t in Ioc x y, φ t < ENNReal.ofReal ε := by
      have hbound := hδlt (Ioc x y) hmeas
      rwa [hres] at hbound
    have hedist := (hdom x hx y hy hxy).trans_lt hlt
    rw [edist_dist] at hedist
    exact ((ENNReal.ofReal_lt_ofReal_iff hε).mp hedist).le
  refine ⟨d.toReal, ENNReal.toReal_pos hd0.ne' hdtop, fun x hx y hy hxy => ?_⟩
  rw [Real.dist_eq] at hxy
  rcases le_total x y with hle | hle
  · refine key x hx y hy hle ?_
    rw [abs_of_nonpos (by linarith)] at hxy
    linarith
  · rw [dist_comm]
    refine key y hy x hx hle ?_
    rw [abs_of_nonneg (by linarith)] at hxy
    linarith

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import TauCeti.Analysis.Complex.Conformal.Area
public import TauCeti.MeasureTheory.Integral.CircleLIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

/-!
# The length–area inequality for a holomorphic map

The **length–area method** converts the finiteness of the Dirichlet integral
`∫⁻ z in s, ‖deriv f z‖ₑ ^ 2` — which `TauCeti/Analysis/Complex/Conformal/Area.lean` identifies
with the area of `f '' s` — into a statement about *lengths*: among the circles `‖z - ζ‖ = ρ`
with `r < ρ < R`, at least one has a short image. This file is the holomorphic half of that
method. The measure-theoretic half is
`TauCeti/MeasureTheory/Integral/CircleLIntegral.lean`, which proves the length–area inequality and
Wolff's lemma for an arbitrary measurable weight `g : ℂ → ℝ≥0∞` on the plane, out of
Cauchy–Schwarz on each circle and polar Fubini. All this file does is instantiate that weight at
the **length density of `f`**, namely `‖deriv f‖ₑ` cut off outside `s`, and identify what the two
sides of the general estimates then mean:

* the circle integral `TauCeti.circleLIntegral` of that weight is
  `TauCeti.circleImageLength f s ζ ρ`, which for `ρ > 0`, measurable `s` and holomorphic `f` is the
  arc length of the parametrised curve `f ∘ circleMap ζ ρ` over the angles landing in `s` (for
  `ρ ≤ 0` it is `0` by the `ENNReal.ofReal ρ` convention of `TauCeti.circleLIntegral`, and carries
  no geometric reading);
* its plane integral of squares is the Dirichlet integral of `f` over `s`, hence by
  `Conformal/Area.lean` the area of `f '' s`.

So the length–area inequality reads
`∫⁻ ρ in Ioi 0, ℓ ρ ^ 2 / ρ ≤ 2 π * volume (f '' s)`, and Wolff's lemma reads: on every annulus,
and for every `c` strictly above the average `2 π A / log (R / r)`, there is a radius with
`ℓ ρ ^ 2 < c` — a threshold that falls without limit as the annulus is made longer. Letting it fall
below an arbitrary `c ≠ 0`, which a finite Dirichlet integral allows, gives the form the crosscut
estimates consume: `ℓ ρ < c` at some radius below every prescribed bound
(`TauCeti.exists_circleImageLength_lt_of_lintegral_ne_top`), equivalently `ℓ` has lower limit `0` at
the centre (`TauCeti.liminf_circleImageLength_nhdsGT_eq_zero`). A *limit* is not available and is
false in general; only some arbitrarily small radii carry a short circle.

The genuinely holomorphic content added here is the **chord bound**
`TauCeti.ofReal_dist_le_circleImageLength`, which is what makes `ℓ` a length: the fundamental
theorem of calculus along the arc bounds the distance between the images of the endpoints of a
sub-arc by `ℓ ρ`. That is the form in which Wolff's lemma is used, and it is the analytic engine of
layer **L5** of the conformal-mapping roadmap (`ConformalMapping/README.md`), Carathéodory's
boundary correspondence. Only that quantitative input is proved here: a radius whose circle has
short image, and a bound on the chords of its arcs. The crosscuts of a Riemann map at a boundary
point `ζ` are not constructed here, nor is the bound on their diameter that a later file is to draw
from these estimates in order to force the cluster set at `ζ` to degenerate to a point.

## Main results

* `TauCeti.circleImageLength` — the circle integral of the length density of `f` cut off outside
  `s`; for `ρ > 0`, measurable `s` and holomorphic `f` this is the arc length of `f ∘ circleMap ζ ρ`
  over the angles landing in `s`, a length along the parametrisation, counted with multiplicity,
  rather than a measure of the image set.
* `TauCeti.ofReal_dist_le_mul_lintegral_Ioc` — the chord bound in its primitive, set-free form:
  the images of the endpoints of an arc of angles are at distance at most `|ρ|` times the angular
  integral of `‖deriv f‖` over that arc, for a radius `ρ` of either sign.
* `TauCeti.ofReal_dist_le_circleImageLength` — the chord bound justifying the name, and the only
  claim made here about lengths that is actually proved: a sub-arc of angular width at most `2 * π`
  that stays in `s` and in a set on which `f` is holomorphic has the distance between the images of
  its endpoints bounded by that quantity.
* `TauCeti.circleImageLength_eq_lintegral_Ioc` — the angular integral may be taken over any period,
  so the branch cut chosen in the definition is immaterial.
* `TauCeti.lintegral_circleImageLength_sq_div_le_lintegral_enorm_deriv_sq` — the **length–area
  inequality**, and `TauCeti.lintegral_circleImageLength_sq_div_le_volume_image` its form with the
  area of `f '' s` on the right, through the area formula of `Conformal/Area.lean`.
* `TauCeti.exists_circleImageLength_sq_lt` and
  `TauCeti.exists_circleImageLength_sq_lt_of_volume_image` — **Wolff's lemma**: a radius with
  `ℓ ρ ^ 2 < c` exists in every annulus `r < ρ < R` on which `2 π A < c * log (R / r)`.
* `TauCeti.exists_circleImageLength_lt_of_lintegral_ne_top` — its limiting form, the one a crosscut
  estimate consumes: for a finite Dirichlet integral, below every bound `R` there is a radius at
  which `ℓ ρ` is smaller than any prescribed `c ≠ 0`.
* `TauCeti.liminf_circleImageLength_nhdsGT_eq_zero` — the same statement as a lower limit at the
  centre, which is the exact sense in which the method makes arcs short.

Holomorphy is used in exactly two places: through `Conformal/Area.lean`, to replace the Dirichlet
integral by the area of the image, and in the chord bound, where the fundamental theorem of calculus
along the arc is applied. The estimates themselves hold for the measurable function `deriv f`
whatever it is, which is why they are proved for a general weight one file down.

## Coordination with upstream Mathlib

Layer L5 is absent from [mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505),
the in-progress human-curated Riemann-mapping-theorem effort, which stops at the mapping theorem
itself, and the pinned Mathlib has no length–area estimate; so this file is new Lean formalization
rather than a temporary shim. Its Mathlib inputs — the measurability of `deriv` and the increment
bound `MeasureTheory.enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc` along an arc — are consumed,
not restated.

## References

* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, §2.2 (the length–area method and
  Wolff's lemma).
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. IX.
-/

public section

namespace TauCeti

open Complex MeasureTheory Metric Set Topology
open scoped ENNReal Real

variable {U s t : Set ℂ} {f : ℂ → ℂ} {ζ : ℂ}

/-! ### The length density of a holomorphic map, and its circle integrals -/

/-- The **derivative-weighted angular integral** over a circle: the circle integral
`TauCeti.circleLIntegral` of the length density `‖deriv f‖` — the factor by which `f` stretches
lengths, whose *square* is the area distortion — with the part of the circle outside `s` discarded
by an indicator.

Nothing is assumed of `s`, so this is a lower integral of a possibly non-measurable integrand, and
the angles `s` selects need not form a single arc, or any arc at all; for such an `s` the quantity
carries no geometric meaning. What is proved of it here is
`TauCeti.ofReal_dist_le_circleImageLength`, which for `f` holomorphic bounds the chord across an
arc of angles lying in `s` by this quantity, and that is what justifies the name.

For `0 < ρ`, measurable `s` and holomorphic `f` the informal reading is the arc length of the
parametrised curve `f ∘ circleMap ζ ρ` restricted to the angles whose points lie in `s`, whose
speed at angle `θ` is `ρ * ‖deriv f (circleMap ζ ρ θ)‖`. For `ρ ≤ 0` the quantity is `0` by the
`ENNReal.ofReal ρ` convention of `TauCeti.circleLIntegral`, so no arc-length reading applies there.
Even for `0 < ρ` it is length along the *parametrisation*, so
points covered several times are counted with multiplicity, and it is a length of the image *set*
only when `f` is in addition injective on that part of the circle; neither reading is formalised
here. For a map with no complex derivative the reading fails outright, since `deriv` is then the
junk value `0`: for `f = conj` the quantity is `0` while the image circle still has length
`2 π ρ`. -/
noncomputable def circleImageLength (f : ℂ → ℂ) (s : Set ℂ) (ζ : ℂ) (ρ : ℝ) : ℝ≥0∞ :=
  circleLIntegral (s.indicator fun z => ‖deriv f z‖ₑ) ζ ρ

/-- The defining circle integral. The body of `TauCeti.circleImageLength` is not `@[expose]`d, so
this is the form in which downstream files — and the lemmas below — reach the definition; unfolding
it directly fails outside this module with `Expected a definition with an exposed body`. Through it
the whole API of `TauCeti.circleLIntegral` applies to the length density of `f`. -/
theorem circleImageLength_def (f : ℂ → ℂ) (s : Set ℂ) (ζ : ℂ) (ρ : ℝ) :
    circleImageLength f s ζ ρ = circleLIntegral (s.indicator fun z => ‖deriv f z‖ₑ) ζ ρ := by
  rw [circleImageLength]

/-- Enlarging the set can only increase the arc length measured inside it. -/
theorem circleImageLength_mono (f : ℂ → ℂ) (ζ : ℂ) (ρ : ℝ) (hst : s ⊆ t) :
    circleImageLength f s ζ ρ ≤ circleImageLength f t ζ ρ := by
  rw [circleImageLength_def, circleImageLength_def]
  refine circleLIntegral_mono_on ζ ρ (fun _ z _ => ?_)
  by_cases hz : z ∈ s
  · simp [Set.indicator_of_mem hz, Set.indicator_of_mem (hst hz)]
  · simp [Set.indicator_of_notMem hz]

/-- The quantity vanishes at a nonpositive radius, inheriting the `ENNReal.ofReal ρ` convention of
`TauCeti.circleLIntegral`: it is that convention rather than a statement about lengths. -/
@[simp]
theorem circleImageLength_of_nonpos (f : ℂ → ℂ) (s : Set ℂ) (ζ : ℂ) {ρ : ℝ} (hρ : ρ ≤ 0) :
    circleImageLength f s ζ ρ = 0 := by
  rw [circleImageLength_def]
  exact circleLIntegral_of_nonpos _ ζ hρ

/-- Measuring inside the empty set gives no length: the indicator kills the whole integrand. -/
@[simp]
theorem circleImageLength_empty (f : ℂ → ℂ) (ζ : ℂ) (ρ : ℝ) :
    circleImageLength f ∅ ζ ρ = 0 := by
  rw [circleImageLength_def, Set.indicator_empty]
  exact circleLIntegral_zero ζ ρ

/-- **The angular integral may be taken over any period.** The interval `Ioo (-π) π` fixed in the
definition of `TauCeti.circleLIntegral` can be replaced by any `Ioc t (t + 2 * π)`, so nothing
about the quantity depends on the branch cut at `±π`; in particular an arc of the circle that
crosses the seam is handled by choosing `t` beyond its far endpoint. -/
theorem circleImageLength_eq_lintegral_Ioc (f : ℂ → ℂ) (s : Set ℂ) (ζ : ℂ) (ρ : ℝ) (t : ℝ) :
    circleImageLength f s ζ ρ =
      ENNReal.ofReal ρ *
        ∫⁻ θ in Ioc t (t + 2 * π), s.indicator (fun z => ‖deriv f z‖ₑ) (circleMap ζ ρ θ) := by
  rw [circleImageLength_def]
  exact circleLIntegral_eq_lintegral_Ioc _ ζ ρ t

/-! ### The length–area inequality and Wolff's lemma -/

/-- The length density of `f` cut off outside a measurable set is measurable, so the estimates of
`TauCeti/MeasureTheory/Integral/CircleLIntegral.lean` apply to it. -/
private theorem measurable_indicator_enorm_deriv (f : ℂ → ℂ) (hs : MeasurableSet s) :
    Measurable (s.indicator fun z => ‖deriv f z‖ₑ) :=
  (measurable_deriv f).enorm.indicator hs

/-- The plane integral of the square of the length density of `f` cut off outside `s` is the
Dirichlet integral of `f` over `s`: the indicator commutes with squaring. -/
private theorem lintegral_indicator_enorm_deriv_sq (f : ℂ → ℂ) (hs : MeasurableSet s) :
    ∫⁻ z, s.indicator (fun z => ‖deriv f z‖ₑ) z ^ 2 = ∫⁻ z in s, ‖deriv f z‖ₑ ^ 2 := by
  rw [← lintegral_indicator hs]
  refine lintegral_congr fun z => ?_
  by_cases hz : z ∈ s <;> simp [hz]

/-- **The length–area inequality.** The integral of `ℓ ρ ^ 2 / ρ` over all radii, where `ℓ ρ` is
`TauCeti.circleImageLength f s ζ ρ` — the derivative-weighted angular integral over the part inside
`s` of the circle of radius `ρ` about `ζ`, an arc length counted with multiplicity when `f` is
holomorphic there — is at most `2 π` times the Dirichlet integral of `f` over `s`.

This is `TauCeti.lintegral_circleLIntegral_sq_div_le_lintegral_sq` at the weight `‖deriv f‖ₑ` cut
off outside `s`. Nothing is assumed of `f`; the holomorphic content of the method is the
identification of the right-hand side with the area of `f '' s` in
`TauCeti.lintegral_circleImageLength_sq_div_le_volume_image`. -/
theorem lintegral_circleImageLength_sq_div_le_lintegral_enorm_deriv_sq (f : ℂ → ℂ)
    (hs : MeasurableSet s) (ζ : ℂ) :
    ∫⁻ ρ in Ioi (0 : ℝ), circleImageLength f s ζ ρ ^ 2 / ENNReal.ofReal ρ ≤
      ENNReal.ofReal (2 * π) * ∫⁻ z in s, ‖deriv f z‖ₑ ^ 2 := by
  simp only [circleImageLength_def]
  rw [← lintegral_indicator_enorm_deriv_sq f hs]
  exact lintegral_circleLIntegral_sq_div_le_lintegral_sq (measurable_indicator_enorm_deriv f hs) ζ

/-- **The length–area inequality, area form.** On a measurable subset `s` of the domain of
holomorphy on which `f` is injective the Dirichlet integral is the area of `f '' s`, so the total
weighted length `∫⁻ ρ, ℓ ρ ^ 2 / ρ` is at most `2 π` times that area. -/
theorem lintegral_circleImageLength_sq_div_le_volume_image (hUo : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hs : MeasurableSet s) (hsU : s ⊆ U) (hinj : Set.InjOn f s)
    (ζ : ℂ) :
    ∫⁻ ρ in Ioi (0 : ℝ), circleImageLength f s ζ ρ ^ 2 / ENNReal.ofReal ρ ≤
      ENNReal.ofReal (2 * π) * volume (f '' s) := by
  rw [volume_image_eq_lintegral_enorm_deriv_sq hUo hf hs.nullMeasurableSet hsU hinj]
  exact lintegral_circleImageLength_sq_div_le_lintegral_enorm_deriv_sq f hs ζ

/-- **Wolff's lemma.** If `2 π` times the Dirichlet integral of `f` over `s` is smaller than
`c * log (R / r)`, then some circle of radius `ρ` between `r` and `R` has `ℓ ρ ^ 2 < c`.

Since `log (R / r)` grows without bound as the annulus is made longer while the Dirichlet integral
stays fixed, this makes `ℓ` arbitrarily small at arbitrarily small radii; for a holomorphic `f`
that is the geometric statement that a map of finite Dirichlet integral cannot keep every circular
arc about `ζ` long. -/
theorem exists_circleImageLength_sq_lt (f : ℂ → ℂ) (hs : MeasurableSet s) (ζ : ℂ) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) {c : ℝ≥0∞}
    (hc : ENNReal.ofReal (2 * π) * (∫⁻ z in s, ‖deriv f z‖ₑ ^ 2) <
      c * ENNReal.ofReal (Real.log (R / r))) :
    ∃ ρ ∈ Ioo r R, circleImageLength f s ζ ρ ^ 2 < c := by
  simp only [circleImageLength_def]
  refine exists_circleLIntegral_sq_lt (measurable_indicator_enorm_deriv f hs) ζ hr hrR ?_
  rwa [lintegral_indicator_enorm_deriv_sq f hs]

/-- **Wolff's lemma, area form.** On a measurable subset `s` of the domain of holomorphy on which
`f` is injective the Dirichlet integral is the area of `f '' s`, so a radius with `ℓ ρ ^ 2 < c`
exists as soon as `2 π * area (f '' s) < c * log (R / r)`. -/
theorem exists_circleImageLength_sq_lt_of_volume_image (hUo : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hs : MeasurableSet s) (hsU : s ⊆ U) (hinj : Set.InjOn f s)
    (ζ : ℂ) {r R : ℝ} (hr : 0 < r) (hrR : r < R) {c : ℝ≥0∞}
    (hc : ENNReal.ofReal (2 * π) * volume (f '' s) < c * ENNReal.ofReal (Real.log (R / r))) :
    ∃ ρ ∈ Ioo r R, circleImageLength f s ζ ρ ^ 2 < c := by
  refine exists_circleImageLength_sq_lt f hs ζ hr hrR ?_
  rwa [volume_image_eq_lintegral_enorm_deriv_sq hUo hf hs.nullMeasurableSet hsU hinj] at hc

/-! ### Short circles at arbitrarily small radii -/

/-- **A finite Dirichlet integral makes the circles about any point short at arbitrarily small
radii.** If `∫⁻ z in s, ‖deriv f z‖ₑ ^ 2` is finite, then below every bound `R > 0` there is a
radius `ρ` at which `TauCeti.circleImageLength f s ζ ρ` is smaller than any prescribed `c ≠ 0`.

This is the limiting form `TauCeti.exists_circleLIntegral_lt_of_lintegral_sq_ne_top` of Wolff's
lemma at the length density of `f`: the annulus in which
`TauCeti.exists_circleImageLength_sq_lt` is applied is chosen there, logarithmically long enough
that its average is beaten, and shrunk against `R`. It is the statement the crosscut estimate of
`Conformal/ShortCrosscut.lean` runs on, the bound `R` being what confines the radius to a genuine
crosscut. -/
theorem exists_circleImageLength_lt_of_lintegral_ne_top (f : ℂ → ℂ) (hs : MeasurableSet s) (ζ : ℂ)
    (hfin : (∫⁻ z in s, ‖deriv f z‖ₑ ^ 2) ≠ ⊤) {c : ℝ≥0∞} (hc : c ≠ 0) {R : ℝ} (hR : 0 < R) :
    ∃ ρ ∈ Ioo 0 R, circleImageLength f s ζ ρ < c := by
  simp only [circleImageLength_def]
  refine exists_circleLIntegral_lt_of_lintegral_sq_ne_top
    (measurable_indicator_enorm_deriv f hs) ?_ ζ hc hR
  rwa [lintegral_indicator_enorm_deriv_sq f hs]

/-- **The circles about any point have lower limit `0` in length.** The sharp form of
`TauCeti.exists_circleImageLength_lt_of_lintegral_ne_top`, and the exact sense in which the
length–area method makes arcs short: only *some* arbitrarily small radii carry a short circle, not
all of them. -/
theorem liminf_circleImageLength_nhdsGT_eq_zero (f : ℂ → ℂ) (hs : MeasurableSet s) (ζ : ℂ)
    (hfin : (∫⁻ z in s, ‖deriv f z‖ₑ ^ 2) ≠ ⊤) :
    Filter.liminf (fun ρ => circleImageLength f s ζ ρ) (𝓝[>] (0 : ℝ)) = 0 := by
  simp only [circleImageLength_def]
  refine liminf_circleLIntegral_nhdsGT_eq_zero (measurable_indicator_enorm_deriv f hs) ?_ ζ
  rwa [lintegral_indicator_enorm_deriv_sq f hs]

/-! ### The chord bound -/


/-- **The chord bound over a sub-arc.** For `f` holomorphic on an open `U` containing the piece of
the circle of radius `ρ` about `ζ` cut out by the angles `Icc a b`, the distance between the images
of the two endpoints of that arc is at most `|ρ|` times the angular integral of `‖deriv f‖` over it.

This is the fundamental theorem of calculus along the arc, and it is the primitive form of the
chord bound: the right-hand side is the length of the image of *this* arc, with no reference to
any set `s`, no restriction on the angular width and none on the sign of the radius — a negative
`ρ` traces the same circle in the other sense, and `ρ = 0` makes both sides `0`. Enlarging the arc
to a whole period and inserting the indicator of `s` gives
`TauCeti.ofReal_dist_le_circleImageLength`, which is the form the length–area estimates chain with
and which does need `0 < ρ`, since `TauCeti.circleImageLength` vanishes at a nonpositive radius;
the form here is what a *local* estimate near one end of the arc needs, since there the arc is
shrunk rather than the radius.

The analytic step is Mathlib's `MeasureTheory.enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc`,
applied to `f ∘ circleMap ζ ρ`, which is `C¹` on the arc because `f` is analytic on `U` and
`circleMap` is smooth. All that remains is the chain rule, which replaces the derivative of the
composite by `deriv f (circleMap ζ ρ θ)` times the velocity `circleMap 0 ρ θ * I`, of norm `|ρ|`. -/
theorem ofReal_dist_le_mul_lintegral_Ioc (hUo : IsOpen U) (hf : DifferentiableOn ℂ f U) (ζ : ℂ)
    {ρ : ℝ} {a b : ℝ} (hab : a ≤ b)
    (hmemU : ∀ θ ∈ Icc a b, circleMap ζ ρ θ ∈ U) :
    ENNReal.ofReal (dist (f (circleMap ζ ρ a)) (f (circleMap ζ ρ b))) ≤
      ENNReal.ofReal |ρ| * ∫⁻ θ in Ioc a b, ‖deriv f (circleMap ζ ρ θ)‖ₑ := by
  have hcd : ContDiffOn ℝ 1 (fun θ => f (circleMap ζ ρ θ)) (Icc a b) := fun θ hθ =>
    (((hf.analyticAt (hUo.mem_nhds (hmemU θ hθ))).contDiffAt.restrict_scalars ℝ).comp θ
      (contDiff_circleMap ζ ρ).contDiffAt).contDiffWithinAt
  have hderiv : ∀ θ ∈ Ioc a b, ‖deriv (fun θ => f (circleMap ζ ρ θ)) θ‖ₑ =
      ENNReal.ofReal |ρ| * ‖deriv f (circleMap ζ ρ θ)‖ₑ := by
    intro θ hθ
    have hmem := hmemU θ (Set.Ioc_subset_Icc_self hθ)
    have h : HasDerivAt (fun θ => f (circleMap ζ ρ θ))
        ((circleMap 0 ρ θ * I) • deriv f (circleMap ζ ρ θ)) θ :=
      ((hf _ hmem).differentiableAt (hUo.mem_nhds hmem)).hasDerivAt.scomp θ
        (hasDerivAt_circleMap ζ ρ θ)
    rw [h.deriv, smul_eq_mul, enorm_mul]
    congr 1
    rw [← ofReal_norm, norm_mul, norm_circleMap_zero, Complex.norm_I, mul_one]
  calc ENNReal.ofReal (dist (f (circleMap ζ ρ a)) (f (circleMap ζ ρ b)))
      = ‖f (circleMap ζ ρ b) - f (circleMap ζ ρ a)‖ₑ := by
        rw [dist_comm, dist_eq_norm, ofReal_norm]
    _ ≤ ∫⁻ θ in Icc a b, ‖deriv (fun θ => f (circleMap ζ ρ θ)) θ‖ₑ :=
        enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hcd hab
    _ = ∫⁻ θ in Ioc a b, ‖deriv (fun θ => f (circleMap ζ ρ θ)) θ‖ₑ := by
        rw [← restrict_Ioc_eq_restrict_Icc]
    _ = ∫⁻ θ in Ioc a b, ENNReal.ofReal |ρ| * ‖deriv f (circleMap ζ ρ θ)‖ₑ :=
        setLIntegral_congr_fun measurableSet_Ioc hderiv
    _ = ENNReal.ofReal |ρ| * ∫⁻ θ in Ioc a b, ‖deriv f (circleMap ζ ρ θ)‖ₑ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- **The chord bound.** If the closed arc of angles `Icc a b` has angular width at most `2 * π`
and the corresponding piece of the circle of radius `ρ` lies both in `s` and in an open set `U` on
which `f` is holomorphic, then the distance between the images of its endpoints is at most
`TauCeti.circleImageLength f s ζ ρ`.

Both hypotheses are arc-local: `s` is constrained only along the arc, so the rest of it — the rest
of the circle included — may lie outside the domain of holomorphy, and `U` need only be a
neighbourhood of the arc rather than of `s`. That is what chains with
`TauCeti.exists_circleImageLength_sq_lt`, whose conclusion is a bound on
`TauCeti.circleImageLength f s ζ ρ` for a `s` chosen for the area estimate rather than for this
arc; when `s ⊆ U` the containment along the arc is immediate from membership in `s`.

The arc is unrestricted apart from its width: it may start anywhere and cross the branch cut at
`±π` fixed in the definition, since by `TauCeti.circleImageLength_eq_lintegral_Ioc` the period of
integration can be moved to `Ioc a (a + 2 * π)`.

This is what makes `TauCeti.circleImageLength` a length rather than an abstract integral, and it is
the form in which Wolff's lemma is used: a short image arc has small chords. Turning that into a
crosscut of small diameter at a boundary point is left to the later file that constructs the
crosscuts. -/
theorem ofReal_dist_le_circleImageLength (hUo : IsOpen U) (hf : DifferentiableOn ℂ f U) (ζ : ℂ)
    {ρ : ℝ} (hρ : 0 < ρ) {a b : ℝ} (hab : a ≤ b) (hb : b ≤ a + 2 * π)
    (hmem : ∀ θ ∈ Icc a b, circleMap ζ ρ θ ∈ s)
    (hmemU : ∀ θ ∈ Icc a b, circleMap ζ ρ θ ∈ U) :
    ENNReal.ofReal (dist (f (circleMap ζ ρ a)) (f (circleMap ζ ρ b))) ≤
      circleImageLength f s ζ ρ := by
  calc ENNReal.ofReal (dist (f (circleMap ζ ρ a)) (f (circleMap ζ ρ b)))
      ≤ ENNReal.ofReal |ρ| * ∫⁻ θ in Ioc a b, ‖deriv f (circleMap ζ ρ θ)‖ₑ :=
        ofReal_dist_le_mul_lintegral_Ioc hUo hf ζ hab hmemU
    _ = ENNReal.ofReal ρ * ∫⁻ θ in Ioc a b, ‖deriv f (circleMap ζ ρ θ)‖ₑ := by
        rw [abs_of_pos hρ]
    _ = ENNReal.ofReal ρ *
          ∫⁻ θ in Ioc a b, s.indicator (fun z => ‖deriv f z‖ₑ) (circleMap ζ ρ θ) := by
        congr 1
        refine setLIntegral_congr_fun measurableSet_Ioc fun θ hθ => ?_
        rw [Set.indicator_of_mem (hmem θ (Set.Ioc_subset_Icc_self hθ))]
    _ ≤ ENNReal.ofReal ρ *
          ∫⁻ θ in Ioc a (a + 2 * π), s.indicator (fun z => ‖deriv f z‖ₑ) (circleMap ζ ρ θ) :=
        by gcongr
    _ = circleImageLength f s ζ ρ := (circleImageLength_eq_lintegral_Ioc f s ζ ρ a).symm

end TauCeti

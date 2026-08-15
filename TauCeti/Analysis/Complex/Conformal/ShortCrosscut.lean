/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Crosscut.Basic
public import TauCeti.Analysis.Complex.Conformal.LengthArea
import TauCeti.Topology.Circle.Metric

/-!
# A circular crosscut with a short image

`Conformal/LengthArea.lean` proves Wolff's lemma — among the circles `‖z - ζ‖ = ρ` with
`r < ρ < R`, one has small `TauCeti.circleImageLength f s ζ ρ` — and the chord bound
`TauCeti.ofReal_dist_le_circleImageLength`, which controls the distance between the images of the
two endpoints of an *arc of angles*. It leaves open, in its own words, the step of "turning that
into a crosscut of small diameter at a boundary point". This file takes that step: it reads the
intersection `ball c r ∩ sphere ζ ρ` of the circle `sphere ζ ρ` with the disc — at a boundary
point, `dist ζ c = r`, the **circular crosscut** of `Conformal/Crosscut/Basic.lean` when
`ρ < 2 * r`, and empty otherwise — as an arc of angles, and concludes that its image under a
conformal map has small diameter at suitable radii `ρ`.

That is the first of the two geometric inputs
`TauCeti.exists_continuousOn_closure_eqOn_of_forall_exists_diam_union_le` of
`Conformal/CutDiameter.lean` runs on, and hence of layer **L5** of
`TauCetiRoadmap/ConformalMapping/README.md`, Carathéodory's boundary correspondence. The second —
a small set `E` enclosing the boundary points of the image domain that cling to the piece the
crosscut cuts off — is a matter of local connectedness of that boundary and is not treated here.

## The intersection is an arc

Everything rests on the angular description of the intersection proved in
`TauCeti/Topology/Circle/Metric.lean`. Writing `α = arg (c - ζ)` for the direction from `ζ` to the
centre of the disc and `d = dist ζ c`, the criterion `TauCeti.circleMap_mem_ball_iff_sq` read off
the law of cosines says that

> `circleMap ζ ρ θ ∈ ball c r ↔ ρ ^ 2 + d ^ 2 - r ^ 2 < 2 * ρ * d * cos (θ - α)`,

and `TauCeti.circleMap_mem_ball_of_mem_Icc` deduces that the condition holds throughout an interval
of angles inside the period centred at `α` as soon as it holds at both ends. Every point of the
circle `sphere ζ ρ` is `circleMap ζ ρ (α + t)` for some `t ∈ [-π, π]`, so any two points of the
intersection are the endpoints of such an interval, of width at most `2 * π`, along which the chord
bound applies.

Nothing in that description relates `ζ` to the disc, so the estimates below are stated for an
arbitrary centre `ζ` of the cutting circle. The Carathéodory correspondence spends them at a
boundary point, `dist ζ c = r`, which together with `ρ < 2 * r` is where `ball c r ∩ sphere ζ ρ`
is a circular crosscut in the sense of `Conformal/Crosscut/Basic.lean`; neither hypothesis is
needed for the estimates themselves, whose statements cover every centre and radius.

## Main results

* `TauCeti.ofReal_dist_le_circleImageLength_of_mem_ball_inter_sphere` — the chord bound for
  `ball c r ∩ sphere ζ ρ`: any two of its points have images at distance at most
  `TauCeti.circleImageLength f (ball c r) ζ ρ`.
* `TauCeti.diam_image_ball_inter_sphere_le` — hence the image of `ball c r ∩ sphere ζ ρ` is no
  wider than that quantity.
* `TauCeti.isBounded_image_ball_inter_sphere_of_circleImageLength_ne_top` — and when that quantity
  is finite the image is bounded, so its diameter is a genuine bound on the distances inside it.
* `TauCeti.exists_diam_image_ball_inter_sphere_le_of_lintegral_ne_top` — the conclusion, from
  Wolff's lemma: a holomorphic map of a disc with finite Dirichlet integral has, at every centre
  `ζ` and below every positive radius, a radius `ρ` at which `f '' (ball c r ∩ sphere ζ ρ)` has
  diameter at most `ε`.
* `TauCeti.exists_diam_image_ball_inter_sphere_le_and_circleImageLength_ne_top` — the same
  selection returning also the finite circle-image length and the boundedness that follows from
  it, which is the form the crosscut theorems downstream consume.
* `TauCeti.exists_diam_image_ball_inter_sphere_le` — its corollary for an injective map with
  bounded image, the case a Riemann map falls under.

## Generality

In accordance with the generality bar of `ConformalMapping/README.md`, which fixes scalar `ℂ` for
every theorem added in layers L0–L6, everything below is stated for maps of `ℂ`. The disc is a
general `ball c r` rather than the unit disc, since nothing is cheaper in the normalised case, and
the centre `ζ` of the cutting circle is unrestricted, since the arc description that carries the
chord bound never uses `dist ζ c = r`. The radius `ρ` of that circle is unrestricted as well, the
three estimates on `ball c r ∩ sphere ζ ρ` asking nothing of it: `sphere ζ ρ` is empty for `ρ < 0`
and the single point `ζ` for `ρ = 0`, so both degenerate cases hold for want of a second point.

## Coordination with upstream Mathlib

Layer L5 is absent from
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), the in-progress
human-curated Riemann-mapping-theorem effort, which stops at the mapping theorem itself, and
Mathlib has no boundary correspondence for conformal maps. So this file is new Lean formalization
rather than a temporary shim; it consumes no L0–L3 shim, its analytic inputs being the length–area
estimates of `Conformal/LengthArea.lean` and the area formula they rest on.

## References

* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, §2.2 (the length–area method, Wolff's
  lemma and crosscuts).
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. IX.
-/

public section

namespace TauCeti

open Bornology Complex MeasureTheory Metric Set
open scoped ENNReal Real

variable {f : ℂ → ℂ} {c ζ : ℂ} {r ρ : ℝ}

/-! ## The chord bound on the intersection `ball c r ∩ sphere ζ ρ` -/

/-- **The chord bound on `ball c r ∩ sphere ζ ρ`.** For `f` holomorphic on `ball c r` and an
arbitrary centre `ζ`, any two points of `ball c r ∩ sphere ζ ρ` have images at distance at most
`TauCeti.circleImageLength f (ball c r) ζ ρ`.

The two points are `circleMap ζ ρ (α + t₁)` and `circleMap ζ ρ (α + t₂)` for angles
`t₁, t₂ ∈ [-π, π]` off the direction `α = arg (c - ζ)` of the centre of the disc; the arc of angles
between them has width at most `2 * π` and stays in the disc by
`TauCeti.circleMap_mem_ball_of_mem_Icc`, so `TauCeti.ofReal_dist_le_circleImageLength` applies to
it with `s = U = ball c r`.

The centre `ζ` of the cutting circle is unrestricted: `ball c r ∩ sphere ζ ρ` is an arc of angles
wherever `ζ` lies, so the bound is not confined to the circular crosscuts at a boundary point
`ζ ∈ sphere c r` that the Carathéodory correspondence cuts with. The radius `ρ` is unrestricted
too, the hypotheses forcing `0 ≤ ρ`: a negative radius leaves `sphere ζ ρ` empty, and `ρ = 0`
leaves it the single point `ζ`, so in both degenerate cases `z = w` and the chord is `0`. -/
theorem ofReal_dist_le_circleImageLength_of_mem_ball_inter_sphere
    (hf : DifferentiableOn ℂ f (ball c r)) {z w : ℂ} (hz : z ∈ ball c r ∩ sphere ζ ρ)
    (hw : w ∈ ball c r ∩ sphere ζ ρ) :
    ENNReal.ofReal (dist (f z) (f w)) ≤ circleImageLength f (ball c r) ζ ρ := by
  rcases (nonneg_of_mem_sphere hz.2).eq_or_lt with hρ | hρ
  · -- a circle of radius zero: both points are its centre
    have hzζ : z = ζ := by simpa [← hρ] using hz.2
    have hwζ : w = ζ := by simpa [← hρ] using hw.2
    simp [hzζ, hwζ]
  -- it suffices to treat a pair of angles in increasing order
  suffices h : ∀ z' w' : ℂ, z' ∈ ball c r ∩ sphere ζ ρ → w' ∈ ball c r ∩ sphere ζ ρ →
      ∀ t₁ ∈ Icc (-π) π, ∀ t₂ ∈ Icc (-π) π, t₁ ≤ t₂ →
      circleMap ζ ρ ((c - ζ).arg + t₁) = z' → circleMap ζ ρ ((c - ζ).arg + t₂) = w' →
      ENNReal.ofReal (dist (f z') (f w')) ≤ circleImageLength f (ball c r) ζ ρ by
    obtain ⟨t₁, ht₁, hz'⟩ := exists_mem_Icc_circleMap_eq (c - ζ).arg hz.2
    obtain ⟨t₂, ht₂, hw'⟩ := exists_mem_Icc_circleMap_eq (c - ζ).arg hw.2
    rcases le_total t₁ t₂ with hle | hle
    · exact h z w hz hw t₁ ht₁ t₂ ht₂ hle hz' hw'
    · rw [dist_comm]
      exact h w z hw hz t₂ ht₂ t₁ ht₁ hle hw' hz'
  rintro z' w' hz' hw' t₁ ht₁ t₂ ht₂ hle rfl rfl
  have harc : ∀ θ ∈ Icc ((c - ζ).arg + t₁) ((c - ζ).arg + t₂), circleMap ζ ρ θ ∈ ball c r :=
    fun θ hθ =>
      circleMap_mem_ball_of_mem_Icc hρ.le (by rw [add_sub_cancel_left]; exact ht₁.1)
        (by rw [add_sub_cancel_left]; exact ht₂.2) hθ hz'.1 hw'.1
  exact ofReal_dist_le_circleImageLength isOpen_ball hf ζ hρ (by linarith)
    (by linarith [ht₁.1, ht₂.2, Real.pi_pos]) harc harc

/-- **The image of `ball c r ∩ sphere ζ ρ` is no wider than its length.** A bound `ε` on
`TauCeti.circleImageLength f (ball c r) ζ ρ` bounds the diameter of the image of
`ball c r ∩ sphere ζ ρ`, by the chord bound
`TauCeti.ofReal_dist_le_circleImageLength_of_mem_ball_inter_sphere`, from which it inherits its
indifference to the centre and the radius of the cutting circle. -/
theorem diam_image_ball_inter_sphere_le
    (hf : DifferentiableOn ℂ f (ball c r)) {ε : ℝ} (hε : 0 ≤ ε)
    (hlen : circleImageLength f (ball c r) ζ ρ ≤ ENNReal.ofReal ε) :
    diam (f '' (ball c r ∩ sphere ζ ρ)) ≤ ε := by
  refine diam_le_of_forall_dist_le hε ?_
  rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩
  exact (ENNReal.ofReal_le_ofReal_iff hε).mp
    ((ofReal_dist_le_circleImageLength_of_mem_ball_inter_sphere hf hz hw).trans hlen)

/-- **An image of finite length is bounded.** The chord bound
`TauCeti.ofReal_dist_le_circleImageLength_of_mem_ball_inter_sphere` keeps every pair of points of
`f '' (ball c r ∩ sphere ζ ρ)` within the finite number
`(TauCeti.circleImageLength f (ball c r) ζ ρ).toReal` of each other.

This is what makes `Metric.diam (f '' (ball c r ∩ sphere ζ ρ))` a bound on the distances inside
that image rather than the junk value `0` that an unbounded set carries; it is the disc counterpart
of `TauCeti.isBounded_image_circleMap_image_Ioo_of_lintegral_ne_top`, stated against the
intersection rather than against an arc of angles. -/
theorem isBounded_image_ball_inter_sphere_of_circleImageLength_ne_top
    (hf : DifferentiableOn ℂ f (ball c r))
    (hfin : circleImageLength f (ball c r) ζ ρ ≠ ⊤) :
    IsBounded (f '' (ball c r ∩ sphere ζ ρ)) := by
  rw [isBounded_iff]
  refine ⟨(circleImageLength f (ball c r) ζ ρ).toReal, ?_⟩
  rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩
  exact (ENNReal.ofReal_le_iff_le_toReal hfin).mp
    (ofReal_dist_le_circleImageLength_of_mem_ball_inter_sphere hf hz hw)

/-! ## Circle intersections with a short image -/

/-- **A holomorphic map of finite Dirichlet integral has short images of small circle
intersections, together with the length witness that produced the bound.** For `f` holomorphic on
`ball c r` with finite Dirichlet integral and an arbitrary `ζ`, every tolerance `ε > 0` and every
bound `R > 0` admit a radius `ρ < R` at which `circleImageLength f (ball c r) ζ ρ` is finite, the
image of `ball c r ∩ sphere ζ ρ` has diameter at most `ε`, and that image is bounded.

`TauCeti.exists_diam_image_ball_inter_sphere_le_of_lintegral_ne_top` is the diameter conjunct
alone. Callers that go on to talk about the crosscut itself need the finite length as well --
the endpoint-limit and Jordan-closing theorems both take it -- and boundedness follows from it,
so all three are returned here rather than reconstructed at each call site. A caller wanting a
genuine circular crosscut applies this at `dist ζ c = r` with `R := min R (2 * r)`. -/
theorem exists_diam_image_ball_inter_sphere_le_and_circleImageLength_ne_top
    (hf : DifferentiableOn ℂ f (ball c r))
    (hfin : ∫⁻ z in ball c r, ‖deriv f z‖ₑ ^ 2 ≠ ⊤) {ε : ℝ} (hε : 0 < ε) {R : ℝ} (hR : 0 < R) :
    ∃ ρ ∈ Ioo 0 R, circleImageLength f (ball c r) ζ ρ ≠ ⊤ ∧
      diam (f '' (ball c r ∩ sphere ζ ρ)) ≤ ε ∧
      IsBounded (f '' (ball c r ∩ sphere ζ ρ)) := by
  obtain ⟨ρ, hρmem, hlen⟩ :=
    exists_circleImageLength_lt_of_lintegral_ne_top (s := ball c r) f measurableSet_ball ζ hfin
      (ENNReal.ofReal_pos.mpr hε).ne' hR
  have hfin' : circleImageLength f (ball c r) ζ ρ ≠ ⊤ := (hlen.trans ENNReal.ofReal_lt_top).ne
  exact ⟨ρ, hρmem, hfin', diam_image_ball_inter_sphere_le hf hε.le hlen.le,
    isBounded_image_ball_inter_sphere_of_circleImageLength_ne_top hf hfin'⟩

/-- **A holomorphic map of finite Dirichlet integral has short images of small circle
intersections.** For `f` holomorphic on `ball c r` with `∫⁻ z in ball c r, ‖deriv f z‖ₑ ^ 2 ≠ ⊤`
and an arbitrary `ζ`, every tolerance `ε > 0` and every bound `R > 0` admit a radius `ρ < R` at
which the image of `ball c r ∩ sphere ζ ρ` has diameter at most `ε`. The case the Carathéodory
correspondence uses is `ζ` on the circle `sphere c r` and `ρ < 2 * r`, where the intersection is a
circular crosscut.

This is the limiting form `TauCeti.exists_circleImageLength_lt_of_lintegral_ne_top` of Wolff's
lemma fed to `TauCeti.diam_image_ball_inter_sphere_le`. The annulus in which the good `ρ` is sought
is chosen there rather than here: it is made logarithmically long enough that the length–area
average of `circleImageLength f (ball c r) ζ ρ ^ 2` over it falls below the threshold, and is
shrunk against `R` so that the radius produced lies in `Ioo 0 R`.

The bound is on the intersection `ball c r ∩ sphere ζ ρ`, which is a genuine circular crosscut only
at a boundary point, `dist ζ c = r`, and there only when `ρ < 2 * r`, the intersection being empty
otherwise; since `R` is arbitrary, a caller wanting a crosscut applies the theorem at such a `ζ`
with `R ≤ 2 * r`. Neither restriction is imposed here, and away from the boundary circle neither
holds: a cutting circle centred at `c` itself meets the disc in the whole of `sphere c ρ` for
`ρ < r`, and one centred far outside meets it at radii `ρ` far above `2 * r`.

This is the first of the two geometric inputs of
`TauCeti.exists_continuousOn_closure_eqOn_of_forall_exists_diam_union_le`; nothing here bounds
the boundary piece the crosscut cuts off, which is a matter of the image domain rather than of the
map. -/
theorem exists_diam_image_ball_inter_sphere_le_of_lintegral_ne_top
    (hf : DifferentiableOn ℂ f (ball c r))
    (hfin : ∫⁻ z in ball c r, ‖deriv f z‖ₑ ^ 2 ≠ ⊤) {ε : ℝ} (hε : 0 < ε) {R : ℝ} (hR : 0 < R) :
    ∃ ρ ∈ Ioo 0 R, diam (f '' (ball c r ∩ sphere ζ ρ)) ≤ ε := by
  obtain ⟨ρ, hρmem, -, hdiam, -⟩ :=
    exists_diam_image_ball_inter_sphere_le_and_circleImageLength_ne_top (ζ := ζ) hf hfin hε hR
  exact ⟨ρ, hρmem, hdiam⟩

/-- **A conformal map of a disc has arbitrarily small images of the circle intersections
`ball c r ∩ sphere ζ ρ` at every centre `ζ`.** This is the case of
`TauCeti.exists_diam_image_ball_inter_sphere_le_of_lintegral_ne_top` that a Riemann map falls under:
for `f` injective on `ball c r` with bounded image the Dirichlet integral is the area of that image,
hence finite by `TauCeti.lintegral_enorm_deriv_sq_ne_top_of_isBounded`.

As there, the intersection bounded is a genuine circular crosscut only at a boundary point,
`dist ζ c = r`, and there only when `ρ < 2 * r`, the intersection being empty otherwise — in
particular empty when `r = 0`, which the hypotheses allow; a caller wanting a crosscut applies the
theorem at such a `ζ` with `R ≤ 2 * r`. -/
theorem exists_diam_image_ball_inter_sphere_le
    (hf : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r))
    (hb : IsBounded (f '' ball c r)) {ε : ℝ} (hε : 0 < ε) {R : ℝ} (hR : 0 < R) :
    ∃ ρ ∈ Ioo 0 R, diam (f '' (ball c r ∩ sphere ζ ρ)) ≤ ε :=
  exists_diam_image_ball_inter_sphere_le_of_lintegral_ne_top hf
    (lintegral_enorm_deriv_sq_ne_top_of_isBounded isOpen_ball hf
      measurableSet_ball.nullMeasurableSet subset_rfl hinj hb) hε hR

end TauCeti

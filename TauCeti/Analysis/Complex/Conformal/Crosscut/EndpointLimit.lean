/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Crosscut.Image
public import TauCeti.Analysis.Complex.Conformal.ShortCrosscut
import TauCeti.Analysis.Complex.Conformal.Crosscut.Endpoints
import TauCeti.Topology.Circle.Metric

/-!
# An image crosscut of finite length ends in two points

`Conformal/Crosscut/Image.lean` identifies the boundary piece a circular crosscut clings to as the
union of the *cluster sets* of the map at the crosscut's two endpoints, and shows each of them to be
a continuum. Nothing there says those continua are single points; in its own words, the
identification is "with a union of two cluster sets, not with a connected subset of `∂Ω` running
between them". This file supplies the missing degeneration, from the one hypothesis that the
length–area method already produces: **an image crosscut of finite length has an honest limit at
each of its two ends**, so its closure is the crosscut together with two points.

That this can be had at all, and without circularity, is the point. The end of an image crosscut is
a boundary cluster set, and the boundary cluster sets of the map on the *disc* degenerating to
points is exactly the layer-**L5** milestone of `TauCetiRoadmap/ConformalMapping/README.md` still
open. The ends here degenerate for a different and much cheaper reason: the arc `ball c r ∩ sphere
ζ ρ` is one-dimensional, and the length of its image is a *finite* number, so the images of its
angles satisfy a Cauchy criterion as the angle runs to an end of the arc. No boundary behaviour of
the map on the disc is used, and none is proved.

## The estimate

The engine is the chord bound of `Conformal/LengthArea.lean` in its primitive, set-free form
`TauCeti.ofReal_dist_le_mul_lintegral_Ioc`: the images of the endpoints of an arc of angles are at
distance at most `ρ` times the angular integral of `‖deriv f‖` over *that* arc. Applied to a
sub-arc, it says that the oscillation of `f` along a piece of the circle is controlled by the length
carried by that piece alone. Since the total length is finite, Mathlib's absolute continuity of the
integral (`MeasureTheory.exists_pos_setLIntegral_lt_of_measure_lt`) makes the length carried by a
short sub-arc uniformly small: that is `TauCeti.exists_pos_forall_dist_le_of_lintegral_ne_top`, a
modulus of continuity for `f` along the arc, in the angular parameter.

Turning the angular modulus into a statement about the plane needs the chord formula
`TauCeti.dist_circleMap_eq_two_mul_sin_abs`: on an arc of angular width at most `π` the chord
`2 * |ρ| * sin (|θ - θ'| / 2)` grows with the angular gap, so points of the arc close in the plane
are close in angle. With that, `TauCeti.subsingleton_clusterSetOn_circleMap_image_Ioo` reads the
modulus as the Cauchy criterion `TauCeti.subsingleton_clusterSetOn_of_forall_exists` of
`Topology/ClusterSet.lean` and concludes at *every* point of the closed arc, its two endpoints
included.

The same chord bound, applied with the whole arc rather than a sub-arc, bounds the image
(`TauCeti.isBounded_image_circleMap_image_Ioo_of_lintegral_ne_top`), which is what turns a
subsingleton cluster set into an honest limit.

## The crosscut

The crosscut instances are the arc description of `Conformal/Crosscut/Endpoints.lean`:
`ball c r ∩ sphere ζ ρ` is the open arc of angles within `arccos (ρ / (2 * r))` of `arg (c - ζ)`,
and `closedBall c r ∩ sphere ζ ρ` is the closed one, of angular width `2 * arccos (ρ / (2 * r))`,
which is below `π` exactly because `ρ` is positive. Finiteness of the angular integral over the arc
is finiteness of `TauCeti.circleImageLength f (ball c r) ζ ρ`, the quantity Wolff's lemma makes
small: a crosscut short enough for the length–area estimates is in particular of finite length, so
the hypothesis costs a consumer nothing it has not already paid for.

The conclusion, `TauCeti.exists_closure_image_ball_inter_sphere_eq_insert`, is that the closure of
the image crosscut is the image crosscut together with two points. Which two points, and whether
they are distinct, is not addressed: an image crosscut may well close up. What the L5 argument needs
is only that the two ends are points on `∂Ω`, so that the small arc of a locally connected `∂Ω`
joining them can be named.

## Main results

* `TauCeti.exists_pos_forall_dist_le_of_lintegral_ne_top` — a modulus of continuity along an arc of
  finite image length, in the angular parameter.
* `TauCeti.isBounded_image_circleMap_image_Ioo_of_lintegral_ne_top` — an arc of finite image length
  has bounded image.
* `TauCeti.subsingleton_clusterSetOn_circleMap_image_Ioo` — at every point of an arc of angular
  width at most `π` and of finite image length, the cluster set of the map along the arc has at
  most one element.
* `TauCeti.subsingleton_clusterSetOn_ball_inter_sphere` and
  `TauCeti.exists_tendsto_nhdsWithin_ball_inter_sphere` — the crosscut forms: a circular crosscut of
  finite image length carries a limit at each point of its closure, its two endpoints included.
* `TauCeti.exists_clusterSetOn_ball_inter_sphere_eq_singleton` — that limit as a one-point cluster
  set, the form `Conformal/Crosscut/Image.lean` indexes over.
* `TauCeti.exists_closure_image_ball_inter_sphere_eq_insert` — hence the closure of an image
  crosscut of finite length is the image crosscut together with two points.

## Generality

In accordance with the generality bar of `ConformalMapping/README.md`, which fixes scalar `ℂ` for
every theorem added in layers L0–L6, everything below is stated for maps of `ℂ`. The arc statements
ask nothing of the ambient disc — only that `f` be holomorphic on an open set containing the arc —
so they apply to any circle in any domain, the crosscut being one instance; neither injectivity of
`f` nor any hypothesis on its image is used anywhere in the file.

## Coordination with upstream Mathlib

Layer L5 is absent from
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), the in-progress
human-curated Riemann-mapping-theorem effort, which stops at the mapping theorem itself, and the
pinned Mathlib has no boundary correspondence for conformal maps. So this file is new Lean
formalization rather than a temporary shim, and it consumes no L0–L3 shim: its analytic input is the
chord bound of `Conformal/LengthArea.lean`, which rests on the fundamental theorem of calculus along
an arc.

## References

* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, §2.2 (crosscuts and the length–area
  method).
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. IX.
-/

public section

namespace TauCeti

open Bornology Complex Filter MeasureTheory Metric Set Topology
open scoped ENNReal Real

variable {U : Set ℂ} {f : ℂ → ℂ} {c ζ : ℂ} {r ρ : ℝ}

/-! ## A modulus of continuity along an arc of finite image length -/

/-- The chord bound `TauCeti.ofReal_dist_le_mul_lintegral_Ioc` for two angles of an open arc on
which `f` is holomorphic: the closed interval they span stays inside the open one. -/
private lemma ofReal_dist_le_mul_lintegral_Ioc_of_mem_Ioo (hUo : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (ζ : ℂ) {ρ : ℝ} (hρ : 0 < ρ) {a b θ₁ θ₂ : ℝ}
    (hmemU : ∀ θ ∈ Ioo a b, circleMap ζ ρ θ ∈ U) (h₁ : θ₁ ∈ Ioo a b) (h₂ : θ₂ ∈ Ioo a b)
    (hle : θ₁ ≤ θ₂) :
    ENNReal.ofReal (dist (f (circleMap ζ ρ θ₁)) (f (circleMap ζ ρ θ₂))) ≤
      ENNReal.ofReal ρ * ∫⁻ θ in Ioc θ₁ θ₂, ‖deriv f (circleMap ζ ρ θ)‖ₑ :=
  ofReal_dist_le_mul_lintegral_Ioc hUo hf ζ hρ hle fun _ hθ =>
    hmemU _ ⟨h₁.1.trans_le hθ.1, hθ.2.trans_lt h₂.2⟩

/-- **A modulus of continuity along an arc of finite image length.** If `f` is holomorphic on an
open set containing the piece of the circle of radius `ρ` about `ζ` cut out by the angles `Ioo a b`,
and the angular integral of `‖deriv f‖` over that arc is finite, then for every tolerance `ε > 0`
there is an angular gap `η > 0` within which the images of two angles of the arc stay `ε` apart.

The gap is uniform over the arc, and in particular does not shrink as an end of the arc is
approached: that is the whole content, and it comes from the absolute continuity of the integral,
`MeasureTheory.exists_pos_setLIntegral_lt_of_measure_lt`. A short sub-arc carries little length,
and by the chord bound `TauCeti.ofReal_dist_le_mul_lintegral_Ioc` the length a sub-arc carries
bounds the distance between the images of its two ends.

Uniform continuity in the angle is *not* uniform continuity of `f` on the arc as a subset of the
plane, but on an arc of angular width at most `π` the two agree, which is what
`TauCeti.subsingleton_clusterSetOn_circleMap_image_Ioo` exploits. -/
theorem exists_pos_forall_dist_le_of_lintegral_ne_top (hUo : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (ζ : ℂ) {ρ : ℝ} (hρ : 0 < ρ) {a b : ℝ}
    (hmemU : ∀ θ ∈ Ioo a b, circleMap ζ ρ θ ∈ U)
    (hfin : ∫⁻ θ in Ioo a b, ‖deriv f (circleMap ζ ρ θ)‖ₑ ≠ ⊤) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ θ₁ ∈ Ioo a b, ∀ θ₂ ∈ Ioo a b, |θ₁ - θ₂| ≤ η →
      dist (f (circleMap ζ ρ θ₁)) (f (circleMap ζ ρ θ₂)) ≤ ε := by
  have hρ0 : ENNReal.ofReal ρ ≠ 0 := (ENNReal.ofReal_pos.mpr hρ).ne'
  have hcne : ENNReal.ofReal (ε / ρ) ≠ 0 := (ENNReal.ofReal_pos.mpr (div_pos hε hρ)).ne'
  obtain ⟨δ, hδ, hδlt⟩ :=
    exists_pos_setLIntegral_lt_of_measure_lt (μ := volume.restrict (Ioo a b)) hfin hcne
  obtain ⟨d, hd0, hdδ⟩ := exists_between hδ
  have hdtop : d ≠ ⊤ := (hdδ.trans_le le_top).ne
  -- the estimate for a pair of angles in increasing order
  have key : ∀ θ₁ ∈ Ioo a b, ∀ θ₂ ∈ Ioo a b, θ₁ ≤ θ₂ → θ₂ - θ₁ ≤ d.toReal →
      dist (f (circleMap ζ ρ θ₁)) (f (circleMap ζ ρ θ₂)) ≤ ε := by
    intro θ₁ h₁ θ₂ h₂ hle hgap
    have hsub : Ioc θ₁ θ₂ ⊆ Ioo a b := fun θ hθ => ⟨h₁.1.trans hθ.1, hθ.2.trans_lt h₂.2⟩
    have hmeas : (volume.restrict (Ioo a b)) (Ioc θ₁ θ₂) < δ := by
      refine lt_of_le_of_lt ((Measure.restrict_apply_le _ _).trans ?_) hdδ
      rw [Real.volume_Ioc, ← ENNReal.ofReal_toReal hdtop]
      exact ENNReal.ofReal_le_ofReal hgap
    have hres : (volume.restrict (Ioo a b)).restrict (Ioc θ₁ θ₂) = volume.restrict (Ioc θ₁ θ₂) := by
      rw [Measure.restrict_restrict measurableSet_Ioc, inter_eq_self_of_subset_left hsub]
    have hlt : ∫⁻ θ in Ioc θ₁ θ₂, ‖deriv f (circleMap ζ ρ θ)‖ₑ < ENNReal.ofReal (ε / ρ) := by
      have hbound := hδlt (Ioc θ₁ θ₂) hmeas
      rwa [hres] at hbound
    have hmul : ENNReal.ofReal ρ * ∫⁻ θ in Ioc θ₁ θ₂, ‖deriv f (circleMap ζ ρ θ)‖ₑ
        < ENNReal.ofReal ε := by
      refine (ENNReal.mul_lt_mul_right hρ0 ENNReal.ofReal_ne_top hlt).trans_eq ?_
      rw [← ENNReal.ofReal_mul hρ.le]
      congr 1
      field_simp
    exact ((ENNReal.ofReal_lt_ofReal_iff hε).mp
      ((ofReal_dist_le_mul_lintegral_Ioc_of_mem_Ioo hUo hf ζ hρ hmemU h₁ h₂ hle).trans_lt
        hmul)).le
  refine ⟨d.toReal, ENNReal.toReal_pos hd0.ne' hdtop, fun θ₁ h₁ θ₂ h₂ habs => ?_⟩
  rcases le_total θ₁ θ₂ with hle | hle
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hle)] at habs
    exact key θ₁ h₁ θ₂ h₂ hle habs
  · rw [abs_of_nonneg (sub_nonneg.mpr hle)] at habs
    rw [dist_comm]
    exact key θ₂ h₂ θ₁ h₁ hle habs

/-- **An arc of finite image length has bounded image.** The chord bound applied to the whole arc
rather than to a sub-arc: any two of its points have images at distance at most
`ρ * ∫⁻ θ in Ioo a b, ‖deriv f (circleMap ζ ρ θ)‖ₑ`, a finite number.

This is what makes a subsingleton cluster set along the arc an honest limit, the compactness input
of `TauCeti.exists_tendsto_of_clusterSetOn_subsingleton`. -/
theorem isBounded_image_circleMap_image_Ioo_of_lintegral_ne_top (hUo : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (ζ : ℂ) {ρ : ℝ} (hρ : 0 < ρ) {a b : ℝ}
    (hmemU : ∀ θ ∈ Ioo a b, circleMap ζ ρ θ ∈ U)
    (hfin : ∫⁻ θ in Ioo a b, ‖deriv f (circleMap ζ ρ θ)‖ₑ ≠ ⊤) :
    IsBounded (f '' (circleMap ζ ρ '' Ioo a b)) := by
  set L : ℝ≥0∞ := ENNReal.ofReal ρ * ∫⁻ θ in Ioo a b, ‖deriv f (circleMap ζ ρ θ)‖ₑ with hL
  have hLtop : L ≠ ⊤ := by
    rw [hL]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  have key : ∀ θ₁ ∈ Ioo a b, ∀ θ₂ ∈ Ioo a b, θ₁ ≤ θ₂ →
      dist (f (circleMap ζ ρ θ₁)) (f (circleMap ζ ρ θ₂)) ≤ L.toReal := by
    intro θ₁ h₁ θ₂ h₂ hle
    refine (ENNReal.ofReal_le_iff_le_toReal hLtop).mp ?_
    refine (ofReal_dist_le_mul_lintegral_Ioc_of_mem_Ioo hUo hf ζ hρ hmemU h₁ h₂ hle).trans ?_
    rw [hL]
    gcongr
    exact fun θ hθ => ⟨h₁.1.trans hθ.1, hθ.2.trans_lt h₂.2⟩
  rw [image_image, Metric.isBounded_image_iff]
  refine ⟨L.toReal, fun θ₁ h₁ θ₂ h₂ => ?_⟩
  rcases le_total θ₁ θ₂ with hle | hle
  · exact key θ₁ h₁ θ₂ h₂ hle
  · rw [dist_comm]
    exact key θ₂ h₂ θ₁ h₁ hle

/-! ## The cluster sets of an arc of finite image length -/

/-- **An arc of finite image length has at most one cluster value at each of its points.** For `f`
holomorphic on an open set containing the open arc `circleMap ζ ρ '' Ioo a b`, of angular width at
most `π` and of finite image length, and for any angle `θ₀` of the *closed* arc, `f` has at most one
cluster value along the arc at the point `circleMap ζ ρ θ₀`.

The two endpoints `θ₀ = a` and `θ₀ = b` are the case with content; at an interior angle the
statement is continuity. The angular width restriction is what makes closeness in the plane the same
as closeness in angle: by the chord formula `TauCeti.dist_circleMap_eq_two_mul_sin_abs` the chord
`2 * ρ * sin (|θ - θ₀| / 2)` is then an increasing function of the angular gap, so a point of the
arc within `2 * ρ * sin (m / 2)` of `circleMap ζ ρ θ₀` is within `m` of `θ₀` in angle. Feeding that
to the modulus `TauCeti.exists_pos_forall_dist_le_of_lintegral_ne_top` gives the Cauchy criterion
`TauCeti.subsingleton_clusterSetOn_of_forall_exists`. -/
theorem subsingleton_clusterSetOn_circleMap_image_Ioo (hUo : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (ζ : ℂ) {ρ : ℝ} (hρ : 0 < ρ) {a b θ₀ : ℝ} (hab : a < b)
    (habπ : b - a ≤ π) (hθ₀ : θ₀ ∈ Icc a b)
    (hmemU : ∀ θ ∈ Ioo a b, circleMap ζ ρ θ ∈ U)
    (hfin : ∫⁻ θ in Ioo a b, ‖deriv f (circleMap ζ ρ θ)‖ₑ ≠ ⊤) :
    (clusterSetOn f (circleMap ζ ρ '' Ioo a b) (circleMap ζ ρ θ₀)).Subsingleton := by
  refine subsingleton_clusterSetOn_of_forall_exists fun ε hε => ?_
  obtain ⟨η, hη, hmod⟩ :=
    exists_pos_forall_dist_le_of_lintegral_ne_top hUo hf ζ hρ hmemU hfin hε
  -- the angular gap actually used: below half the modulus, and below the width of the arc
  set m : ℝ := min (η / 2) (b - a) with hm
  have hm0 : 0 < m := lt_min (by linarith) (by linarith)
  have hmπ : m ≤ π := le_trans (min_le_right _ _) habπ
  have hsinm : 0 < Real.sin (m / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  refine ⟨2 * ρ * Real.sin (m / 2), by positivity, ?_⟩
  -- a point of the arc close to `circleMap ζ ρ θ₀` is close to `θ₀` in angle
  have hangle : ∀ x ∈ circleMap ζ ρ '' Ioo a b ∩ ball (circleMap ζ ρ θ₀) (2 * ρ * Real.sin (m / 2)),
      ∃ θ ∈ Ioo a b, circleMap ζ ρ θ = x ∧ |θ - θ₀| < m := by
    rintro _ ⟨⟨θ, hθ, rfl⟩, hx⟩
    refine ⟨θ, hθ, rfl, ?_⟩
    have hπ : |θ - θ₀| ≤ π := by
      rw [abs_le]
      constructor <;> [linarith [hθ.1, hθ₀.2]; linarith [hθ.2, hθ₀.1]]
    rw [mem_ball, dist_circleMap_eq_two_mul_sin_abs ζ ρ hπ, abs_of_pos hρ] at hx
    rcases lt_or_ge |θ - θ₀| m with hlt | hcon
    · exact hlt
    · exfalso
      have hmono : Real.sin (m / 2) ≤ Real.sin (|θ - θ₀| / 2) :=
        Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) (by linarith)
          (by linarith)
      nlinarith [hρ.le]
  rintro x hx y hy
  obtain ⟨θx, hθx, rfl, hdx⟩ := hangle x hx
  obtain ⟨θy, hθy, rfl, hdy⟩ := hangle y hy
  refine hmod θx hθx θy hθy ?_
  have htri : |θx - θy| ≤ |θx - θ₀| + |θ₀ - θy| := abs_sub_le _ _ _
  have hsymm : |θ₀ - θy| = |θy - θ₀| := abs_sub_comm _ _
  have hmη : m ≤ η / 2 := min_le_left _ _
  linarith

/-! ## The two ends of a circular crosscut -/

/-- The angular integral of the length density over the arc of a genuine circular crosscut is
finite as soon as `TauCeti.circleImageLength f (ball c r) ζ ρ` is: the crosscut lies in `ball c r`,
so the indicator in the definition of the latter is inert along it, and the crosscut spans less
than a full period. -/
private lemma lintegral_enorm_deriv_circleMap_ne_top (hζ : dist ζ c = r) (hρ : 0 < ρ)
    (hρr : ρ < 2 * r) (hfin : circleImageLength f (ball c r) ζ ρ ≠ ⊤) :
    ∫⁻ θ in Ioo ((c - ζ).arg - Real.arccos (ρ / (2 * r)))
      ((c - ζ).arg + Real.arccos (ρ / (2 * r))), ‖deriv f (circleMap ζ ρ θ)‖ₑ ≠ ⊤ := by
  have hr : 0 < r := by linarith
  have hφπ2 : Real.arccos (ρ / (2 * r)) < π / 2 :=
    Real.arccos_lt_pi_div_two.mpr (div_pos hρ (by positivity))
  have hmem : ∀ θ ∈ Ioo ((c - ζ).arg - Real.arccos (ρ / (2 * r)))
      ((c - ζ).arg + Real.arccos (ρ / (2 * r))), circleMap ζ ρ θ ∈ ball c r := by
    intro θ hθ
    have : circleMap ζ ρ θ ∈ ball c r ∩ sphere ζ ρ := by
      rw [ball_inter_sphere_eq_circleMap_image_Ioo hζ hρ hρr]
      exact ⟨θ, hθ, rfl⟩
    exact this.1
  have hle : ∫⁻ θ in Ioo ((c - ζ).arg - Real.arccos (ρ / (2 * r)))
        ((c - ζ).arg + Real.arccos (ρ / (2 * r))), ‖deriv f (circleMap ζ ρ θ)‖ₑ ≤
      ∫⁻ θ in Ioc ((c - ζ).arg - Real.arccos (ρ / (2 * r)))
        ((c - ζ).arg - Real.arccos (ρ / (2 * r)) + 2 * π),
          (ball c r).indicator (fun z => ‖deriv f z‖ₑ) (circleMap ζ ρ θ) := by
    calc ∫⁻ θ in Ioo ((c - ζ).arg - Real.arccos (ρ / (2 * r)))
          ((c - ζ).arg + Real.arccos (ρ / (2 * r))), ‖deriv f (circleMap ζ ρ θ)‖ₑ
        = ∫⁻ θ in Ioo ((c - ζ).arg - Real.arccos (ρ / (2 * r)))
            ((c - ζ).arg + Real.arccos (ρ / (2 * r))),
              (ball c r).indicator (fun z => ‖deriv f z‖ₑ) (circleMap ζ ρ θ) := by
          refine setLIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
          rw [Set.indicator_of_mem (hmem θ hθ)]
      _ ≤ _ := by
          refine lintegral_mono_set (fun θ hθ => ?_)
          exact ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  intro htop
  have hbig : ∫⁻ θ in Ioc ((c - ζ).arg - Real.arccos (ρ / (2 * r)))
      ((c - ζ).arg - Real.arccos (ρ / (2 * r)) + 2 * π),
        (ball c r).indicator (fun z => ‖deriv f z‖ₑ) (circleMap ζ ρ θ) = ⊤ :=
    top_unique (by rw [← htop]; exact hle)
  refine hfin ?_
  rw [circleImageLength_eq_lintegral_Ioc f (ball c r) ζ ρ
    ((c - ζ).arg - Real.arccos (ρ / (2 * r))), hbig,
    ENNReal.mul_top (ENNReal.ofReal_pos.mpr hρ).ne']

/-- **A circular crosscut of finite image length has at most one cluster value at each point of its
closure.** This is `TauCeti.subsingleton_clusterSetOn_circleMap_image_Ioo` at the arc description of
`Conformal/Crosscut/Endpoints.lean`: a genuine circular crosscut is the open arc of angles within
`arccos (ρ / (2 * r))` of `arg (c - ζ)`, of angular width below `π`, and its closure adds exactly
the two angles at the ends.

The two endpoints, where `e ∈ sphere c r ∩ sphere ζ ρ`, are the case with content. Neither
injectivity of `f` nor any hypothesis on its image is used. -/
theorem subsingleton_clusterSetOn_ball_inter_sphere (hζ : dist ζ c = r) (hρ : 0 < ρ)
    (hρr : ρ < 2 * r) (hf : DifferentiableOn ℂ f (ball c r))
    (hfin : circleImageLength f (ball c r) ζ ρ ≠ ⊤) {e : ℂ}
    (he : e ∈ closedBall c r ∩ sphere ζ ρ) :
    (clusterSetOn f (ball c r ∩ sphere ζ ρ) e).Subsingleton := by
  have hr : 0 < r := by linarith
  have hφ0 : 0 < Real.arccos (ρ / (2 * r)) :=
    Real.arccos_pos.mpr ((div_lt_one (by positivity)).mpr hρr)
  have hφπ2 : Real.arccos (ρ / (2 * r)) < π / 2 :=
    Real.arccos_lt_pi_div_two.mpr (div_pos hρ (by positivity))
  obtain ⟨θ₀, hθ₀, rfl⟩ : ∃ θ₀ ∈ Icc ((c - ζ).arg - Real.arccos (ρ / (2 * r)))
      ((c - ζ).arg + Real.arccos (ρ / (2 * r))), circleMap ζ ρ θ₀ = e := by
    rw [closedBall_inter_sphere_eq_circleMap_image_Icc hζ hρ hρr] at he
    exact he
  rw [ball_inter_sphere_eq_circleMap_image_Ioo hζ hρ hρr]
  refine subsingleton_clusterSetOn_circleMap_image_Ioo isOpen_ball hf ζ hρ (by linarith)
    (by linarith) hθ₀ (fun θ hθ => ?_)
    (lintegral_enorm_deriv_circleMap_ne_top hζ hρ hρr hfin)
  have : circleMap ζ ρ θ ∈ ball c r ∩ sphere ζ ρ := by
    rw [ball_inter_sphere_eq_circleMap_image_Ioo hζ hρ hρr]
    exact ⟨θ, hθ, rfl⟩
  exact this.1

/-- **A circular crosscut of finite image length has a limit at each point of its closure.** The
cluster set is a subsingleton by `TauCeti.subsingleton_clusterSetOn_ball_inter_sphere`, and it is
nonempty because the image of the crosscut is bounded — the chord bound again — so the map is
confined along the crosscut to a compact set.

At the two endpoints, where `e ∈ sphere c r ∩ sphere ζ ρ`, this is the statement that the image
crosscut is a curve with two honest ends. -/
theorem exists_tendsto_nhdsWithin_ball_inter_sphere (hζ : dist ζ c = r) (hρ : 0 < ρ)
    (hρr : ρ < 2 * r) (hf : DifferentiableOn ℂ f (ball c r))
    (hfin : circleImageLength f (ball c r) ζ ρ ≠ ⊤) {e : ℂ}
    (he : e ∈ closedBall c r ∩ sphere ζ ρ) :
    ∃ v, Tendsto f (𝓝[ball c r ∩ sphere ζ ρ] e) (𝓝 v) := by
  have hb : IsBounded (f '' (ball c r ∩ sphere ζ ρ)) := by
    rw [Metric.isBounded_image_iff]
    refine ⟨(circleImageLength f (ball c r) ζ ρ).toReal, fun z hz w hw => ?_⟩
    exact (ENNReal.ofReal_le_iff_le_toReal hfin).mp
      (ofReal_dist_le_circleImageLength_of_mem_ball_inter_sphere hζ hρ hf hz hw)
  refine exists_tendsto_of_clusterSetOn_subsingleton hb.isCompact_closure
    (fun w hw => subset_closure (mem_image_of_mem f hw)) ?_
    (subsingleton_clusterSetOn_ball_inter_sphere hζ hρ hρr hf hfin he)
  rw [closure_ball_inter_sphere hζ hρ hρr]
  exact he

/-- **The end of a circular crosscut of finite image length is a single point.** The cluster set of
`TauCeti.exists_tendsto_nhdsWithin_ball_inter_sphere` written as a singleton, which is the form
`TauCeti.frontier_inter_closure_image_ball_inter_sphere_eq_biUnion_clusterSetOn` of
`Conformal/Crosscut/Image.lean` indexes the boundary piece over. -/
theorem exists_clusterSetOn_ball_inter_sphere_eq_singleton (hζ : dist ζ c = r) (hρ : 0 < ρ)
    (hρr : ρ < 2 * r) (hf : DifferentiableOn ℂ f (ball c r))
    (hfin : circleImageLength f (ball c r) ζ ρ ≠ ⊤) {e : ℂ}
    (he : e ∈ closedBall c r ∩ sphere ζ ρ) :
    ∃ v, clusterSetOn f (ball c r ∩ sphere ζ ρ) e = {v} := by
  obtain ⟨v, hv⟩ := exists_tendsto_nhdsWithin_ball_inter_sphere hζ hρ hρr hf hfin he
  refine ⟨v, clusterSetOn_eq_singleton_of_tendsto ?_ hv⟩
  rw [closure_ball_inter_sphere hζ hρ hρr]
  exact he

/-- **The closure of an image crosscut of finite length is the image crosscut together with two
points.** `Conformal/Crosscut/Image.lean` writes that closure as the image crosscut together with
the cluster sets at the two endpoints; finiteness of the length collapses each of those to a point.

Nothing is claimed about the two points: they may coincide, an image crosscut being free to close
up. What a boundary-correspondence argument needs of them is that they are points at all, so that
the arc of a locally connected image boundary joining them can be named. -/
theorem exists_closure_image_ball_inter_sphere_eq_insert (hζ : dist ζ c = r) (hρ : 0 < ρ)
    (hρr : ρ < 2 * r) (hf : DifferentiableOn ℂ f (ball c r))
    (hfin : circleImageLength f (ball c r) ζ ρ ≠ ⊤) :
    ∃ u v, closure (f '' (ball c r ∩ sphere ζ ρ)) =
      insert u (insert v (f '' (ball c r ∩ sphere ζ ρ))) := by
  have hpair : sphere c r ∩ sphere ζ ρ =
      {circleMap ζ ρ ((c - ζ).arg - Real.arccos (ρ / (2 * r))),
        circleMap ζ ρ ((c - ζ).arg + Real.arccos (ρ / (2 * r)))} :=
    sphere_inter_sphere_eq_pair_circleMap hζ hρ hρr
  have hsub : ∀ e ∈ sphere c r ∩ sphere ζ ρ, e ∈ closedBall c r ∩ sphere ζ ρ :=
    fun _ he => ⟨sphere_subset_closedBall he.1, he.2⟩
  have hp : circleMap ζ ρ ((c - ζ).arg - Real.arccos (ρ / (2 * r))) ∈ sphere c r ∩ sphere ζ ρ := by
    rw [hpair]; exact mem_insert _ _
  have hq : circleMap ζ ρ ((c - ζ).arg + Real.arccos (ρ / (2 * r))) ∈ sphere c r ∩ sphere ζ ρ := by
    rw [hpair]; exact mem_insert_of_mem _ rfl
  obtain ⟨u, hu⟩ :=
    exists_clusterSetOn_ball_inter_sphere_eq_singleton hζ hρ hρr hf hfin (hsub _ hp)
  obtain ⟨v, hv⟩ :=
    exists_clusterSetOn_ball_inter_sphere_eq_singleton hζ hρ hρr hf hfin (hsub _ hq)
  refine ⟨u, v, ?_⟩
  rw [closure_image_ball_inter_sphere_eq_union_biUnion_clusterSetOn
    (hf.continuousOn.mono inter_subset_left) hζ hρ hρr, hpair, biUnion_pair, hu, hv,
    union_comm, singleton_union, insert_union, singleton_union]

end TauCeti

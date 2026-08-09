/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Connected.OrderInjection
public import TauCeti.Topology.JordanCurve.Separation
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# A curve of the plane has empty interior

A Jordan curve of `ℂ` contains no disc: `TauCeti.IsJordanCurve.interior_eq_empty`. Neither does an
arc, the continuous injective image of a compact set of reals
(`TauCeti.interior_image_eq_empty_of_isCompact`). Both are the same one-dimensionality statement,
and both come from the same source — a set of the plane carrying a continuous real-valued injection
has empty interior — through the criterion `TauCeti.subsingleton_of_continuousOn_injOn` of
`TauCeti/Topology/Connected/OrderInjection.lean`: a preconnected set whose punctures stay
preconnected does not inject into a line.

## The circle inside the disc

The set the criterion is run on is not the disc but a *circle* `Metric.sphere z ρ` inside it. A
circle of `ℂ` is preconnected and stays preconnected when any one point is removed
(`TauCeti.isPathConnected_sphere_sdiff_singleton`, a Jordan curve minus a point being an open arc),
and it has more than one point; so no continuous injection into `ℝ` is defined on it. The disc
itself would serve as well, but the punctured circle is already in the repository whereas the
punctured disc is not.

Everything is therefore reduced to producing, from a disc `Metric.ball z r` inside the set, a
real-valued function that is continuous and injective on `Metric.sphere z (r / 2)`. That is the
private `false_of_ball_subset` below, stated with the function living on the subtype so that a
parametrization of the set can be used directly, with no extension to the plane.

## The two curves

* An **arc** is handled by its parametrization. A continuous injection of a compact set of reals is
  a homeomorphism onto its image, so the inverse parametrization is a continuous injection of the
  arc into `ℝ`, defined on all of it.
* A **Jordan curve** is not: the circle admits no continuous injection into `ℝ` at all, which is
  the whole point. What it does admit is one *after a point is deleted* — `Complex.arg`, composed
  with the rotation carrying the deleted point to `-1`. A point may be deleted for free, because
  the disc inside the curve supplies a point of the curve, its own centre, off the circle
  `Metric.sphere z (r / 2)` on which the criterion is run.

## Why this is a layer-L5 prerequisite

Layer **L5** of the conformal-mapping roadmap (`TauCetiRoadmap/ConformalMapping/README.md`) is
Carathéodory's boundary correspondence for a Jordan domain, and `ConformalMapping/STATUS.md`
records under *Jordan curve input* that "the strong facts about Jordan curves that the forward
direction classically leans on ... are not established here", and that whoever attacks L5 should
settle them first. That a curve is nowhere dense in the plane is the first of those facts and the
standing hypothesis under which the others are read: it is what says the boundary of a Jordan
domain — and hence every boundary cluster set inside it, and the closure of every image crosscut —
is a genuine one-dimensional object rather than a set with interior, and it is an elementary
ingredient of the Jordan curve theorem itself.
`TauCeti/Analysis/Complex/Conformal/Crosscut/Image.lean` already argues from the same fact for a
circular cut, where it is read off the explicit parametrization; for the image boundary, which is
only known to be a Jordan curve, no parametrization is available and the statements below are what
is left.

## Generality

The curves are subsets of `ℂ`, matching the generality bar of `ConformalMapping/README.md`, which
fixes scalar `ℂ` for layers L0–L6, and matching `TauCeti/Topology/JordanCurve/Separation.lean`,
whose punctured-circle theorem is the geometric input. Nothing in the argument is special to `ℂ`
beyond the two-dimensionality that keeps a punctured circle connected, but the punctured circle is
available here and not in a general plane. The purely order-theoretic core is stated for an
arbitrary densely ordered line in `TauCeti/Topology/Connected/OrderInjection.lean`.

## Main results

* `TauCeti.interior_eq_empty_of_continuous_injective` — a subset of `ℂ` carrying a continuous
  injection into `ℝ` has empty interior.
* `TauCeti.interior_image_eq_empty_of_isCompact` — **an arc of the plane has empty interior**: the
  continuous injective image of a compact set of reals contains no disc.
* `TauCeti.IsJordanCurve.interior_eq_empty` — **a Jordan curve of the plane has empty interior**.
* `TauCeti.IsJordanCurve.dense_compl` and `TauCeti.IsJordanCurve.frontier_eq_self` — the two
  readings of that: the complement of a Jordan curve is dense, and a Jordan curve is its own
  frontier.

## References

* K. Kuratowski, *Topology II*, §61.
* C. Carathéodory, *Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung*,
  Math. Ann. **73** (1913).
-/

public section

namespace TauCeti

open Complex Metric Set Topology

variable {C : Set ℂ}

/-! ## From a disc inside the set to a contradiction -/

/-- Preconnectedness of a subset of `C` transfers to the corresponding set of the subtype `↥C`,
the inclusion being an embedding. -/
private theorem isPreconnected_preimage_val {T : Set ℂ} (hTC : T ⊆ C) (hT : IsPreconnected T) :
    IsPreconnected ((Subtype.val : C → ℂ) ⁻¹' T) := by
  rw [← IsInducing.subtypeVal.isPreconnected_image, Subtype.image_preimage_coe,
    inter_eq_right.mpr hTC]
  exact hT

/-- **A set of the plane containing a disc carries no real-valued function that is continuous and
injective on a circle inside that disc.**

This is `TauCeti.subsingleton_of_continuousOn_injOn` run on `Metric.sphere z (r / 2)`, viewed inside
the subtype `↥C`: that circle is preconnected and stays so when any one of its points is removed
(`TauCeti.isPathConnected_sphere_sdiff_singleton`), while the two ends `z ± r / 2` of a diameter
keep it from being a single point.

The function is carried by the subtype rather than by `ℂ` because that is the form a parametrization
of `C` takes; nothing is assumed of it off the circle. -/
private theorem false_of_ball_subset {z : ℂ} {r : ℝ} (hr : 0 < r) (hball : ball z r ⊆ C)
    {ψ : C → ℝ} (hψc : ContinuousOn ψ ((Subtype.val : C → ℂ) ⁻¹' sphere z (r / 2)))
    (hψi : Set.InjOn ψ ((Subtype.val : C → ℂ) ⁻¹' sphere z (r / 2))) : False := by
  have hρ : 0 < r / 2 := by linarith
  have hsub : sphere z (r / 2) ⊆ C := fun w hw =>
    hball (mem_ball.mpr (by rw [mem_sphere] at hw; rw [hw]; linarith))
  -- the circle, read inside `↥C`, is preconnected and has preconnected punctures
  have hS : IsPreconnected ((Subtype.val : C → ℂ) ⁻¹' sphere z (r / 2)) :=
    isPreconnected_preimage_val hsub (isJordanCurve_sphere z hρ).isConnected.isPreconnected
  have hpunct : ∀ x ∈ (Subtype.val : C → ℂ) ⁻¹' sphere z (r / 2),
      IsPreconnected ((Subtype.val : C → ℂ) ⁻¹' sphere z (r / 2) \ {x}) := by
    intro x _
    have hx : (Subtype.val : C → ℂ) ⁻¹' sphere z (r / 2) \ {x} =
        (Subtype.val : C → ℂ) ⁻¹' (sphere z (r / 2) \ {(x : ℂ)}) := by
      ext y
      simp [Subtype.ext_iff]
    rw [hx]
    exact isPreconnected_preimage_val (sdiff_subset.trans hsub)
      (isPathConnected_sphere_sdiff_singleton z hρ (x : ℂ)).isConnected.isPreconnected
  -- the two ends of a diameter keep the circle from being a single point
  have hplus : z + ((r / 2 : ℝ) : ℂ) ∈ sphere z (r / 2) := by
    simpa [mem_sphere_iff_norm] using hr.le
  have hminus : z - ((r / 2 : ℝ) : ℂ) ∈ sphere z (r / 2) := by
    simpa [mem_sphere_iff_norm] using hr.le
  have hne : z + ((r / 2 : ℝ) : ℂ) ≠ z - ((r / 2 : ℝ) : ℂ) := by
    intro hcon
    have h2 : ((r / 2 : ℝ) : ℂ) = 0 := by linear_combination hcon / 2
    rw [Complex.ofReal_eq_zero] at h2
    exact hρ.ne' h2
  have hp : (⟨z + ((r / 2 : ℝ) : ℂ), hsub hplus⟩ : C) ∈
      (Subtype.val : C → ℂ) ⁻¹' sphere z (r / 2) := hplus
  have hm : (⟨z - ((r / 2 : ℝ) : ℂ), hsub hminus⟩ : C) ∈
      (Subtype.val : C → ℂ) ⁻¹' sphere z (r / 2) := hminus
  exact hne (congrArg Subtype.val
    (subsingleton_of_continuousOn_injOn hS hpunct hψc hψi hp hm))

/-! ## Sets that inject into the line -/

/-- **A subset of `ℂ` carrying a continuous injection into `ℝ` has empty interior.**

If it contained a disc it would contain a circle, on which the injection would still be continuous
and injective — and a circle admits none, being preconnected with preconnected punctures. -/
theorem interior_eq_empty_of_continuous_injective {ψ : C → ℝ} (hψc : Continuous ψ)
    (hψi : Function.Injective ψ) : interior C = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro z hz
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hz)
  exact false_of_ball_subset hr hball hψc.continuousOn hψi.injOn

/-- **An arc of the plane has empty interior.** The continuous injective image in `ℂ` of a compact
set of reals contains no disc.

A continuous injection on a compact set is a homeomorphism onto its image
(`Continuous.homeoOfEquivCompactToT2`), so the inverse parametrization is a continuous injection of
the arc into `ℝ`, and `TauCeti.interior_eq_empty_of_continuous_injective` applies. Compactness is
what makes that inverse continuous. -/
theorem interior_image_eq_empty_of_isCompact {K : Set ℝ} (hK : IsCompact K) {γ : ℝ → ℂ}
    (hγ : ContinuousOn γ K) (hinj : Set.InjOn γ K) : interior (γ '' K) = ∅ := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have e : K ≃ₜ γ '' K :=
    Continuous.homeoOfEquivCompactToT2 (f := hinj.bijOn_image.equiv γ)
      (hγ.mapsToRestrict hinj.bijOn_image.mapsTo)
  exact interior_eq_empty_of_continuous_injective (ψ := fun x => ((e.symm x : K) : ℝ))
    (continuous_subtype_val.comp e.symm.continuous)
    fun x y h => e.symm.injective (Subtype.ext h)

/-! ## Jordan curves -/

/-- **A Jordan curve of the plane has empty interior**: no disc of `ℂ` lies on a simple closed
curve.

Unlike an arc, a Jordan curve carries no continuous injection into `ℝ` — the circle does not — so
`TauCeti.interior_eq_empty_of_continuous_injective` does not apply directly. It is the private
criterion behind it that applies, after a point of the curve is deleted, and a disc
`Metric.ball z r` inside the curve supplies that point for free: the criterion is run only on the
circle `Metric.sphere z (r / 2)`, which misses the centre `z`. Deleting the corresponding point
`e z` of the model circle makes `Complex.arg` — composed with the rotation
`u ↦ Circle.exp π * (e z)⁻¹ * u`, which carries `e z` to the point `-1` where `Complex.arg` jumps —
a continuous injection of what is left into `ℝ`. -/
theorem IsJordanCurve.interior_eq_empty (h : IsJordanCurve C) : interior C = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro z hz
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hz)
  obtain ⟨e⟩ := isJordanCurve_iff.mp h
  set z' : C := ⟨z, hball (mem_ball_self hr)⟩ with hz'
  set a : Circle := Circle.exp Real.pi * (e z')⁻¹ with ha
  -- on the circle of radius `r / 2` the rotated parameter avoids the jump of `Complex.arg`
  have hoff : ∀ x ∈ (Subtype.val : C → ℂ) ⁻¹' sphere z (r / 2),
      a * e x ≠ Circle.exp Real.pi := by
    intro x hx hcon
    rw [ha, mul_assoc, mul_eq_left, inv_mul_eq_one] at hcon
    have hxz : x = z' := (e.injective hcon).symm
    rw [hxz] at hx
    have hd : dist ((z' : ℂ)) z = r / 2 := hx
    rw [hz'] at hd
    simp only [dist_self] at hd
    linarith
  have hslit : ∀ x ∈ (Subtype.val : C → ℂ) ⁻¹' sphere z (r / 2),
      ((a * e x : Circle) : ℂ) ∈ slitPlane := by
    intro x hx
    refine mem_slitPlane_iff_arg.mpr ⟨fun hcon => hoff x hx ?_, Circle.coe_ne_zero _⟩
    exact Circle.arg_eq_arg.mp
      (hcon.trans (Circle.arg_exp (by linarith [Real.pi_pos]) le_rfl).symm)
  have hg : Continuous fun x : C => ((a * e x : Circle) : ℂ) :=
    Continuous.subtype_val (Continuous.mul continuous_const e.continuous)
  refine false_of_ball_subset hr hball
    (ψ := fun x => arg ((a * e x : Circle) : ℂ)) (fun x hx => ?_) ?_
  · have hc : ContinuousAt (arg ∘ fun x : C => ((a * e x : Circle) : ℂ)) x :=
      ContinuousAt.comp (f := fun x : C => ((a * e x : Circle) : ℂ))
        (continuousAt_arg (hslit x hx)) hg.continuousAt
    exact hc.continuousWithinAt
  · exact fun x _ y _ hxy => e.injective (mul_left_cancel (Circle.injective_arg hxy))

/-- **The complement of a Jordan curve of the plane is dense**: a curve is nowhere dense, being
closed with empty interior. -/
theorem IsJordanCurve.dense_compl (h : IsJordanCurve C) : Dense Cᶜ :=
  interior_eq_empty_iff_dense_compl.mp h.interior_eq_empty

/-- **A Jordan curve of the plane is its own frontier.** It is closed, so its frontier is what is
left after removing its interior, and that is empty. -/
theorem IsJordanCurve.frontier_eq_self (h : IsJordanCurve C) : frontier C = C := by
  rw [h.isClosed.frontier_eq, h.interior_eq_empty, sdiff_empty]

end TauCeti

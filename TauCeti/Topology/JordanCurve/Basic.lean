/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homeomorph.Lemmas
public import TauCeti.Topology.LocallyConnected
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Jordan curves

A **Jordan curve** — a simple closed curve — is a subset of a topological space homeomorphic to
the circle. This file introduces the predicate `TauCeti.IsJordanCurve` and its basic API.

The circle is Mathlib's `Circle`, the unit circle of `ℂ` as a topological group; the notion itself
is purely topological, so `TauCeti.IsJordanCurve` is stated for a subset of an arbitrary
topological space. `ℂ` is mentioned only by the two concrete curves towards the end of the file:
the model curve, a circle `Metric.sphere c r` of positive radius, and the frontier of a bounded
convex set with nonempty interior. The model is built from the complex affine change of coordinates
`w ↦ (w - c) / r`, so it uses the field structure of `ℂ` and not only its metric, and the convex
frontier is obtained from the model by transport.

Phrasing the predicate as *the set is homeomorphic to the circle*, rather than *the set is the
range of a continuous map on `[0, 1]` that is injective except for matching endpoints*, is what
makes it usable: over a Hausdorff ambient space the two agree, because there a continuous injection
out of a compact space is an embedding, but the parametrized form buries that argument in every
use. Passing from a parametrization to the predicate is `TauCeti.IsJordanCurve.image`, which turns
a continuous injective map defined on a set already known to be a Jordan curve — a circle in `ℂ`,
say — into a proof that its image is one; `TauCeti.IsJordanCurve.of_image` runs the other way,
transporting the property back to a compact set from an image already known to be a Jordan curve.

## Main definitions

* `TauCeti.IsJordanCurve` — a set homeomorphic to the circle.
* `TauCeti.jordanParam` — the parametrization of a Jordan curve by the circle underlying a
  homeomorphism of the curve with `Circle`.

## Main results

* `TauCeti.IsJordanCurve.isCompact`, `TauCeti.IsJordanCurve.isPathConnected`,
  `TauCeti.IsJordanCurve.nonempty` and `TauCeti.IsJordanCurve.not_subsingleton` — a Jordan curve is
  a nonempty compact path-connected set with more than one point.
* `TauCeti.IsJordanCurve.image` and `TauCeti.IsJordanCurve.of_image` — being a Jordan curve
  transfers in both directions along a map that is continuous and injective on the set, provided
  the codomain is Hausdorff (and, in the direction that transports the property back from the
  image, the source set is known to be compact).
* `TauCeti.IsJordanCurve.image_homeomorph` and `TauCeti.isJordanCurve_image_homeomorph_iff` — being
  a Jordan curve is invariant under a homeomorphism of the ambient spaces; no separation axiom is
  needed.
* `TauCeti.continuous_jordanParam`, `TauCeti.jordanParam_injective`,
  `TauCeti.isInducing_jordanParam`, `TauCeti.range_jordanParam`, `TauCeti.jordanParam_apply` and
  `TauCeti.jordanParam_apply_apply` — the parametrization of a Jordan curve by the circle is a
  continuous injection, is inducing, traces out exactly the curve, and undoes `e`; this is what
  carries a statement about the circle to one about an arbitrary Jordan curve.
* `TauCeti.sphereCircleHomeomorph` and `TauCeti.isJordanCurve_sphere` — a circle of positive radius
  in `ℂ` is a Jordan curve, by the affine change of coordinates `w ↦ (w - c) / r`.
* `TauCeti.isJordanCurve_frontier_of_convex` — the frontier of a bounded convex subset of `ℂ` with
  nonempty interior is a Jordan curve. This is `TauCeti.isJordanCurve_sphere` with the disc
  weakened to an arbitrary convex body, the affine change of coordinates being replaced by Mathlib's
  gauge rescaling.
* `TauCeti.locallyConnectedSpace_sphere` and `TauCeti.IsJordanCurve.locallyConnectedSpace` — a
  circle in `ℂ`, and hence every Jordan curve, is locally connected.

## Motivation

This is the vocabulary layer **L5** of the conformal-mapping roadmap
(`TauCetiRoadmap/ConformalMapping/README.md`) is stated in: its milestone, the Carathéodory
boundary correspondence, is about the Riemann map of a *Jordan domain*, and the roadmap records
that the pinned Mathlib has no Jordan-curve vocabulary to state it against. The complex-analytic
half — Jordan domains, the discs among them, and the boundary of a domain that a conformal map
carries onto a disc — is in `TauCeti/Analysis/Complex/Conformal/Jordan/Domain.lean`.

Local connectedness of a Jordan curve is what that milestone needs of the *hypothesis* side: the
route to the extension theorem for a Jordan domain `Ω` runs through Carathéodory's continuity
theorem, whose hypothesis is that `frontier Ω` be locally connected, and
`TauCeti.IsJordanCurve.locallyConnectedSpace` is what discharges it (as
`TauCeti.IsJordanDomain.locallyConnectedSpace_frontier`). Mathlib knows the circle is compact,
connected and path connected, but records no local connectedness for it, and the property is not
preserved by continuous images, so it is proved here from
`TauCeti.locallyConnectedSpace_image_of_isCompact`.

## References

* C. Jordan, *Cours d'analyse de l'École Polytechnique*, vol. 3 (1887).
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Ch. 2.
-/

public section

namespace TauCeti

open Metric Set Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {C : Set X} {p : X} {r : ℝ}

/-- A **Jordan curve**, or simple closed curve, in a topological space: a subset homeomorphic to
the circle.

The predicate is `Nonempty (C ≃ₜ Circle)` rather than a chosen homeomorphism, so that it is a
`Prop`; `TauCeti.isJordanCurve_iff` recovers the homeomorphism from another module, where the
definition itself is not exposed. -/
def IsJordanCurve (C : Set X) : Prop := Nonempty (C ≃ₜ Circle)

/-- A set is a Jordan curve exactly when it is homeomorphic to the circle. This is the interface
to `TauCeti.IsJordanCurve` outside its defining module. -/
theorem isJordanCurve_iff : IsJordanCurve C ↔ Nonempty (C ≃ₜ Circle) := Iff.rfl

/-- A continuous injection defined on a compact set is a homeomorphism onto its image, the image
carrying the subspace topology of a Hausdorff space. This is the set-level form of
`Continuous.homeoOfEquivCompactToT2`, and the engine of both transfer lemmas below. -/
private noncomputable def imageHomeomorphOfIsCompact [T2Space Y] (hC : IsCompact C) {g : X → Y}
    (hg : ContinuousOn g C) (hgi : InjOn g C) : C ≃ₜ g '' C :=
  haveI : CompactSpace C := isCompact_iff_compactSpace.mp hC
  Continuous.homeoOfEquivCompactToT2 (f := hgi.bijOn_image.equiv g)
    (hg.mapsToRestrict hgi.bijOn_image.mapsTo)

/-- A Jordan curve is compact: the circle is. -/
theorem IsJordanCurve.isCompact (h : IsJordanCurve C) : IsCompact C := by
  obtain ⟨e⟩ := h
  exact isCompact_iff_compactSpace.mpr e.symm.compactSpace

/-- A Jordan curve in a Hausdorff space is closed. -/
theorem IsJordanCurve.isClosed [T2Space X] (h : IsJordanCurve C) : IsClosed C :=
  h.isCompact.isClosed

/-- A Jordan curve is path connected: the circle is. -/
theorem IsJordanCurve.isPathConnected (h : IsJordanCurve C) : IsPathConnected C := by
  obtain ⟨e⟩ := h
  exact isPathConnected_iff_pathConnectedSpace.mpr
    (e.symm.surjective.pathConnectedSpace e.symm.continuous)

/-- A Jordan curve is connected. -/
theorem IsJordanCurve.isConnected (h : IsJordanCurve C) : IsConnected C :=
  h.isPathConnected.isConnected

/-- A Jordan curve is nonempty. -/
theorem IsJordanCurve.nonempty (h : IsJordanCurve C) : C.Nonempty := h.isConnected.nonempty

/-- A Jordan curve has more than one point: the circle contains both `1` and `-1`. Together with
`TauCeti.IsJordanCurve.isConnected` this rules out the degenerate curves, so a Jordan curve is a
nondegenerate continuum. -/
theorem IsJordanCurve.not_subsingleton (h : IsJordanCurve C) : ¬ C.Subsingleton := by
  obtain ⟨e⟩ := h
  intro hsub
  exact Circle.neg_ne_self 1
    (e.symm.injective (Subtype.ext (hsub (e.symm (-1)).2 (e.symm 1).2)))

/-- **A Jordan curve is carried to a Jordan curve by a continuous injection.** Only continuity and
injectivity *on the curve* are needed, the curve supplying the compactness that upgrades them to a
homeomorphism onto the image. -/
theorem IsJordanCurve.image [T2Space Y] (h : IsJordanCurve C) {g : X → Y} (hg : ContinuousOn g C)
    (hgi : InjOn g C) : IsJordanCurve (g '' C) := by
  have hC := h.isCompact
  obtain ⟨e⟩ := h
  exact ⟨(imageHomeomorphOfIsCompact hC hg hgi).symm.trans e⟩

/-- **A compact set carried onto a Jordan curve by a continuous injection is a Jordan curve.**
This is the converse of `TauCeti.IsJordanCurve.image`; compactness of the source has to be assumed
here, since it is no longer inherited from the curve. It is the form in which the predicate is
verified when the curve is the *unknown* rather than the parameter: one exhibits a continuous
injective map of the set onto a set already known to be a Jordan curve, as the boundary
correspondence does with the boundary of a disc. -/
theorem IsJordanCurve.of_image [T2Space Y] (hC : IsCompact C) {g : X → Y} (hg : ContinuousOn g C)
    (hgi : InjOn g C) (h : IsJordanCurve (g '' C)) : IsJordanCurve C := by
  obtain ⟨e⟩ := h
  exact ⟨(imageHomeomorphOfIsCompact hC hg hgi).trans e⟩

/-- The image of a Jordan curve under a homeomorphism of the ambient spaces is a Jordan curve.
Unlike `TauCeti.IsJordanCurve.image` this needs no separation axiom on the codomain, because
`Homeomorph.image` supplies the homeomorphism onto the image outright. -/
theorem IsJordanCurve.image_homeomorph (h : IsJordanCurve C) (e : X ≃ₜ Y) :
    IsJordanCurve (e '' C) := by
  obtain ⟨f⟩ := h
  exact ⟨(e.image C).symm.trans f⟩

/-- Being a Jordan curve is invariant under a homeomorphism of the ambient spaces. This is the
characteristic form of `TauCeti.IsJordanCurve.image_homeomorph`: the backward direction is that
lemma applied to `e.symm`, which no consumer then has to spell out. -/
@[simp]
theorem isJordanCurve_image_homeomorph_iff (e : X ≃ₜ Y) :
    IsJordanCurve (e '' C) ↔ IsJordanCurve C :=
  ⟨fun h => e.symm_image_image C ▸ h.image_homeomorph e.symm, fun h => h.image_homeomorph e⟩

/-! ## The parametrization by the circle

Every transport of a statement about `Circle` to a Jordan curve goes through the parametrization
`jordanParam e` attached to a homeomorphism `e`, so its properties — continuity, injectivity,
range, and that it is inducing — are collected here rather than rebuilt at each use, both by the
cutting of a curve at one or two of its points
(`TauCeti/Topology/JordanCurve/Separation.lean`) and by the quantitative form of that cutting
(`TauCeti/Topology/JordanCurve/SmallArc.lean`). -/

/-- The parametrization of a Jordan curve by the circle underlying a homeomorphism `e`: the
composite of `e.symm` with the inclusion of the curve into the ambient space. -/
noncomputable def jordanParam (e : C ≃ₜ Circle) : Circle → X :=
  fun u => ((e.symm u : C) : X)

/-- The parametrization `TauCeti.jordanParam` of a Jordan curve by the circle is continuous. -/
lemma continuous_jordanParam (e : C ≃ₜ Circle) : Continuous (jordanParam e) :=
  continuous_subtype_val.comp e.symm.continuous

/-- The parametrization `TauCeti.jordanParam` of a Jordan curve by the circle is injective: this is
the simplicity of the curve. -/
lemma jordanParam_injective (e : C ≃ₜ Circle) : Function.Injective (jordanParam e) :=
  Subtype.val_injective.comp e.symm.injective

/-- The parametrization `TauCeti.jordanParam` of a Jordan curve by the circle is inducing, so
preconnectedness of a subset of the curve may be tested on its preimage of parameters. -/
lemma isInducing_jordanParam (e : C ≃ₜ Circle) : Topology.IsInducing (jordanParam e) :=
  Topology.IsInducing.subtypeVal.comp e.symm.isInducing

/-- The parametrization `TauCeti.jordanParam` of a Jordan curve by the circle traces out exactly the
curve. -/
@[simp]
lemma range_jordanParam (e : C ≃ₜ Circle) : range (jordanParam e) = C := by
  refine subset_antisymm ?_ fun x hx => ⟨e ⟨x, hx⟩, by simp [jordanParam]⟩
  rintro _ ⟨u, rfl⟩
  exact (e.symm u).2

/-- The defining equation of `TauCeti.jordanParam`: the parameter `u` names the point `e.symm u` of
the curve, read in the ambient space. This is the general application lemma, so a consumer never has
to unfold the definition. -/
@[simp]
lemma jordanParam_apply (e : C ≃ₜ Circle) (u : Circle) :
    jordanParam e u = ((e.symm u : C) : X) := by
  simp [jordanParam]

/-- The parametrization `TauCeti.jordanParam` of a Jordan curve by the circle undoes `e`: it sends
the parameter `e ⟨p, hp⟩` of a point `p` of the curve back to `p`. Simp proves this from
`TauCeti.jordanParam_apply`; it is stated for the `rw` steps that produce the point `p` itself
rather than a coerced parameter. -/
lemma jordanParam_apply_apply (e : C ≃ₜ Circle) (hp : p ∈ C) :
    jordanParam e (e ⟨p, hp⟩) = p := by
  simp

/-! ## The model curve: a circle in `ℂ` -/

/-- `Circle` is *by definition* the unit sphere of `ℂ`, but it is a `def` rather than an
abbreviation, so its topology is only definitionally the subtype topology. This identification is
the one place where that unfolding happens; the lemmas below then compute with the unit sphere
alone. -/
private noncomputable def unitSphereCircleHomeomorph : sphere (0 : ℂ) 1 ≃ₜ Circle :=
  Homeomorph.refl _

private lemma coe_unitSphereCircleHomeomorph (z : sphere (0 : ℂ) 1) :
    (unitSphereCircleHomeomorph z : ℂ) = (z : ℂ) := rfl

private lemma coe_unitSphereCircleHomeomorph_symm (z : Circle) :
    ((unitSphereCircleHomeomorph.symm z : sphere (0 : ℂ) 1) : ℂ) = (z : ℂ) := rfl

/-- The affine parametrization `w ↦ (w - c) / r` of a circle of centre `c` and positive radius `r`
in `ℂ` by the unit circle. It is the restriction to the spheres of the inverse of Mathlib's ambient
`affineHomeomorph r c`, so only the membership equivalence is proved here. -/
noncomputable def sphereCircleHomeomorph (c : ℂ) (hr : 0 < r) : sphere c r ≃ₜ Circle :=
  haveI hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  (((affineHomeomorph (r : ℂ) c hr0).symm).subtype fun w => by
      rw [affineHomeomorph_symm_apply]
      simp [mem_sphere_iff_norm, abs_of_pos hr, div_eq_one_iff_eq, hr.ne']).trans
    unitSphereCircleHomeomorph

/-- The parametrization of `sphere c r` by the unit circle divides out the affine change of
coordinates. -/
@[simp]
lemma coe_sphereCircleHomeomorph_apply (c : ℂ) (hr : 0 < r) (w : sphere c r) :
    (sphereCircleHomeomorph c hr w : ℂ) = ((w : ℂ) - c) / r := by
  simp [sphereCircleHomeomorph, coe_unitSphereCircleHomeomorph]

/-- The inverse parametrization of `sphere c r` by the unit circle is the affine change of
coordinates. -/
@[simp]
lemma coe_sphereCircleHomeomorph_symm_apply (c : ℂ) (hr : 0 < r) (z : Circle) :
    (((sphereCircleHomeomorph c hr).symm z : sphere c r) : ℂ) = c + r * (z : ℂ) := by
  simp [sphereCircleHomeomorph, coe_unitSphereCircleHomeomorph_symm, add_comm]

/-- A circle of positive radius in `ℂ` is a Jordan curve. -/
theorem isJordanCurve_sphere (c : ℂ) (hr : 0 < r) : IsJordanCurve (sphere c r) :=
  isJordanCurve_iff.mpr ⟨sphereCircleHomeomorph c hr⟩

/-- **The frontier of a bounded convex subset of `ℂ` with nonempty interior is a Jordan curve.**

This is `TauCeti.isJordanCurve_sphere` with the disc weakened to an arbitrary convex body, which it
recovers at `s = Metric.ball c r`. The model curve transports because Mathlib's gauge rescaling
supplies an *ambient* homeomorphism `e : ℂ ≃ₜ ℂ` carrying `frontier s` onto the unit circle
(`exists_homeomorph_image_interior_closure_frontier_eq_unitBall`), so the affine change of
coordinates above is simply replaced by a nonlinear one and no further topology is needed.

The set is asked neither to be open nor to be nonempty: what a convex set needs in order to have a
one-dimensional frontier is that it be *solid*, and that is `(interior s).Nonempty`. Without it the
statement fails — a segment is convex and bounded, and is its own frontier. -/
theorem isJordanCurve_frontier_of_convex {s : Set ℂ} (hs : Convex ℝ s)
    (hne : (interior s).Nonempty) (hb : Bornology.IsBounded s) : IsJordanCurve (frontier s) := by
  obtain ⟨e, -, -, hfr⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall hs hne hb
  refine (isJordanCurve_image_homeomorph_iff e).mp ?_
  rw [hfr]
  exact isJordanCurve_sphere 0 one_pos

/-! ## Local connectedness -/

open Complex in
/-- **A circle in `ℂ` is locally connected.** It is the image of the compact interval `[-π, π]`,
which is convex and hence locally connected, under the continuous `θ ↦ c + r * exp (θ * I)`, so
`TauCeti.locallyConnectedSpace_image_of_isCompact` applies. A sphere of negative radius is empty,
and vacuously locally connected. -/
instance locallyConnectedSpace_sphere (c : ℂ) (r : ℝ) : LocallyConnectedSpace (sphere c r) := by
  rcases lt_or_ge r 0 with hr | hr
  · have hempty : sphere c r = (∅ : Set ℂ) := by
      ext z
      simp only [mem_sphere_iff_norm, mem_empty_iff_false, iff_false]
      intro h
      have : (0 : ℝ) ≤ r := h ▸ norm_nonneg (z - c)
      linarith
    rw [hempty]
    exact ⟨fun x => absurd x.2 (notMem_empty _)⟩
  · have hparam :
        sphere c r = (fun θ : ℝ => c + r * exp (θ * I)) '' Icc (-Real.pi) Real.pi := by
      ext z
      simp only [mem_sphere_iff_norm, mem_image, mem_Icc]
      constructor
      · intro hz
        refine ⟨arg (z - c), ⟨(neg_pi_lt_arg (z - c)).le, arg_le_pi (z - c)⟩, ?_⟩
        rw [← hz, norm_mul_exp_arg_mul_I (z - c)]
        ring
      · rintro ⟨θ, -, rfl⟩
        simp [abs_of_nonneg hr]
    have := (convex_Icc (-Real.pi) Real.pi).locallyPathConnectedSpace
    rw [hparam]
    exact locallyConnectedSpace_image_of_isCompact isCompact_Icc
      (Continuous.continuousOn (by fun_prop))

/-- **The circle is locally connected.** `Circle` is the unit circle of `ℂ`, so this is the unit
case of `TauCeti.locallyConnectedSpace_sphere` transported along `TauCeti.sphereCircleHomeomorph`.
Mathlib records the circle as compact, connected and path connected, but not as locally
connected. -/
instance locallyConnectedSpace_circle : LocallyConnectedSpace Circle :=
  (sphereCircleHomeomorph (0 : ℂ) one_pos).symm.locallyConnectedSpace

/-- **A Jordan curve is locally connected**, being homeomorphic to the circle.

This is the form in which the hypothesis of Carathéodory's continuity theorem — that the boundary
of the domain be locally connected — is met by a Jordan domain, which is what layer **L5** of the
conformal-mapping roadmap is about; see `TauCeti.IsJordanDomain.locallyConnectedSpace_frontier`. -/
theorem IsJordanCurve.locallyConnectedSpace (h : IsJordanCurve C) : LocallyConnectedSpace C :=
  (isJordanCurve_iff.mp h).elim fun e => e.locallyConnectedSpace

end TauCeti

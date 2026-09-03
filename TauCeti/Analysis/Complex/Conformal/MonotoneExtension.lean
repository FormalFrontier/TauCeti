/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.ArcConstancy
public import TauCeti.Analysis.Complex.Conformal.ClusterSet
public import TauCeti.Topology.JordanCurve.Monotone

/-!
# Injectivity of a monotone conformal extension

This file isolates the remaining topological input in the injectivity half of Carathéodory's
boundary correspondence. Let `F` be continuous on a closed disc, holomorphic and injective on its
interior. If every point fibre of the boundary restriction is connected, then `F` is injective on
the boundary and hence on the whole closed disc.

The proof joins two existing parts of the conformal-mapping development. Boundary uniqueness in
`TauCeti/Analysis/Complex/Conformal/ArcConstancy.lean` says that a conformal map is constant on no
relative open arc of the bounding circle, so each boundary fibre has empty interior. The monotone
Jordan-curve theorem in `TauCeti/Topology/JordanCurve/Monotone.lean` then turns connectedness of the
fibres into injectivity. Finally,
`TauCeti.injOn_closure_of_injOn_frontier` propagates boundary injectivity across the closed disc,
since a boundary value of a conformal map cannot also be an interior value.

For the layer **L5** Carathéodory milestone, the continuous extension is supplied by the
length–area and plane-separation argument. The result here shows that upgrading it to the requested
homeomorphism of closures needs exactly the monotonicity of its boundary restriction; it does not
assume or assert that monotonicity for an arbitrary continuous extension.

## Main results

* `TauCeti.injOn_sphere_of_isPreconnected_boundary_fiber` — a monotone boundary restriction of a
  conformal disc map is injective.
* `TauCeti.injOn_sphere_iff_isPreconnected_boundary_fiber` — monotonicity of the boundary
  restriction is exactly its injectivity.
* `TauCeti.injOn_closedBall_of_isPreconnected_boundary_fiber` — the extension is injective on the
  closed disc.
* `TauCeti.bijOn_closedBall_closure_image_of_isPreconnected_boundary_fiber` — consequently it is a
  bijection from the closed disc onto the closure of the conformal image; the existing
  `TauCeti.closureHomeomorph` packages this bijection as a homeomorphism.

## References

* C. Carathéodory, *Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung*,
  Math. Ann. **73** (1913).
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Ch. 2.
-/

public section

namespace TauCeti

open Metric Set Topology

variable {c : ℂ} {r : ℝ} {F : ℂ → ℂ}

/-- **A conformal disc map with a monotone boundary restriction is injective on the circle.**
Suppose `F` is continuous on `closedBall c r`, holomorphic and injective on `ball c r`, and every
point fibre of its restriction to `sphere c r` is preconnected. Then the restriction is injective.

The fibre-interior hypothesis of
`TauCeti.IsJordanCurve.injective_of_isPreconnected_fiber_of_interior_fiber_eq_empty` is exactly
`TauCeti.interior_setOf_eq_eq_empty_of_injOn`, the boundary uniqueness theorem for a conformal map.
-/
theorem injOn_sphere_of_isPreconnected_boundary_fiber (hr : 0 < r)
    (hcont : ContinuousOn F (closedBall c r)) (hdiff : DifferentiableOn ℂ F (ball c r))
    (hinj : InjOn F (ball c r))
    (hpre : ∀ a, IsPreconnected {z : sphere c r | F z = a}) : InjOn F (sphere c r) := by
  have hcontinuous : Continuous (fun z : sphere c r ↦ F z) :=
    hcont.mono sphere_subset_closedBall |>.domRestrict
  have hrestricted : Function.Injective (fun z : sphere c r ↦ F z) :=
    (isJordanCurve_sphere c hr).injective_of_isPreconnected_fiber_of_interior_fiber_eq_empty
      hcontinuous hpre fun a ↦ interior_setOf_eq_eq_empty_of_injOn hr hcont hdiff hinj a
  intro x hx y hy hxy
  have hxy' : (fun z : sphere c r ↦ F z) ⟨x, hx⟩ = (fun z : sphere c r ↦ F z) ⟨y, hy⟩ :=
    hxy
  exact congrArg Subtype.val (hrestricted hxy')

/-- **For a conformal extension, boundary monotonicity is equivalent to boundary injectivity.**
Boundary uniqueness makes every point fibre interiorless, so
`TauCeti.IsJordanCurve.injective_iff_isPreconnected_fiber_of_interior_fiber_eq_empty` applies to
the restriction of `F` to `sphere c r`.

This equivalence makes the outstanding geometric input in the Carathéodory injectivity argument
precise: proving that the boundary fibres are preconnected is neither weaker nor stronger than the
required boundary injectivity once the conformal and continuity hypotheses are available. -/
theorem injOn_sphere_iff_isPreconnected_boundary_fiber (hr : 0 < r)
    (hcont : ContinuousOn F (closedBall c r)) (hdiff : DifferentiableOn ℂ F (ball c r))
    (hinj : InjOn F (ball c r)) :
    InjOn F (sphere c r) ↔ ∀ a, IsPreconnected {z : sphere c r | F z = a} := by
  have hcontinuous : Continuous (fun z : sphere c r ↦ F z) :=
    hcont.mono sphere_subset_closedBall |>.domRestrict
  have hiff :=
    (isJordanCurve_sphere c hr).injective_iff_isPreconnected_fiber_of_interior_fiber_eq_empty
      hcontinuous fun a ↦ interior_setOf_eq_eq_empty_of_injOn hr hcont hdiff hinj a
  constructor
  · intro hboundary
    apply hiff.mp
    intro x y hxy
    exact Subtype.ext (hboundary x.2 y.2 hxy)
  · exact injOn_sphere_of_isPreconnected_boundary_fiber hr hcont hdiff hinj

/-- **A conformal disc map with a monotone boundary restriction is injective on the closed
disc.** Boundary injectivity comes from
`TauCeti.injOn_sphere_of_isPreconnected_boundary_fiber`; the interior and boundary images are
disjoint by conformal properness, so `TauCeti.injOn_closure_of_injOn_frontier` gives injectivity on
the closure. -/
theorem injOn_closedBall_of_isPreconnected_boundary_fiber (hr : 0 < r)
    (hcont : ContinuousOn F (closedBall c r)) (hdiff : DifferentiableOn ℂ F (ball c r))
    (hinj : InjOn F (ball c r))
    (hpre : ∀ a, IsPreconnected {z : sphere c r | F z = a}) : InjOn F (closedBall c r) := by
  have hclosure : closure (ball c r) = closedBall c r := closure_ball c hr.ne'
  have hfrontier : frontier (ball c r) = sphere c r := frontier_ball c hr.ne'
  rw [← hclosure]
  refine injOn_closure_of_injOn_frontier isOpen_ball hdiff hinj ?_ (fun _ _ ↦ rfl) ?_
  · simpa only [hclosure] using hcont
  · simpa only [hfrontier] using
      injOn_sphere_of_isPreconnected_boundary_fiber hr hcont hdiff hinj hpre

/-- **A monotone conformal extension is a bijection of the closed disc with the closure of its
image.** This is the set-level conclusion needed to instantiate `TauCeti.closureHomeomorph`.
Surjectivity is continuity on the compact closed disc; injectivity is
`TauCeti.injOn_closedBall_of_isPreconnected_boundary_fiber`. -/
theorem bijOn_closedBall_closure_image_of_isPreconnected_boundary_fiber (hr : 0 < r)
    (hcont : ContinuousOn F (closedBall c r)) (hdiff : DifferentiableOn ℂ F (ball c r))
    (hinj : InjOn F (ball c r))
    (hpre : ∀ a, IsPreconnected {z : sphere c r | F z = a}) :
    BijOn F (closedBall c r) (closure (F '' ball c r)) := by
  have hclosure : closure (ball c r) = closedBall c r := closure_ball c hr.ne'
  rw [← hclosure]
  exact bijOn_closure_closure_image (isBounded_ball : Bornology.IsBounded (ball c r))
    (by simpa only [hclosure] using hcont) (fun _ _ ↦ rfl)
    (by simpa only [hclosure] using
      injOn_closedBall_of_isPreconnected_boundary_fiber hr hcont hdiff hinj hpre)

end TauCeti

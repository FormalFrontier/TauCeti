/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.BoundaryCorrespondence
public import TauCeti.Topology.JordanCurve
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Jordan domains, and the domains a conformal map takes onto a disc

A **Jordan domain** is a bounded domain of `ℂ` whose boundary is a Jordan curve. This file
introduces `TauCeti.IsJordanDomain`, exhibits the discs as the basic example, and proves the
*converse* half of the Carathéodory boundary correspondence: a bounded domain that a conformal map
carries onto a disc, the map extending continuously and injectively to the closure, is a Jordan
domain.

## Why the converse is the accessible half

Layer **L5** of the conformal-mapping roadmap (`TauCetiRoadmap/ConformalMapping/README.md`) is
Carathéodory's theorem: *the Riemann map of a Jordan domain extends to a homeomorphism of the
closures*. Both directions of that correspondence pass through the same object, the boundary
homeomorphism `TauCeti.closureHomeomorph`, but they are not of the same difficulty. Producing the
extension is the hard direction — it needs the boundary geometry to control the cluster sets of the
map, which is where `Conformal/ClusterSet.lean` and the local connectivity of the boundary enter,
and it is *not* proved here. Reading the boundary geometry *off* an extension that is already given
is the direction this file supplies, and it is short, because the boundary correspondence has
already been established: `TauCeti.image_frontier_eq_frontier_image` says that an injective
continuous extension carries `frontier U` onto `frontier (f '' U)`, and `frontier U` is compact
whenever `U` is bounded, so `TauCeti.IsJordanCurve.of_image` transports the circle backwards along
the extension.

The result is exactly the statement that Carathéodory's hypothesis is not merely sufficient but
necessary: among bounded domains, "conformally a disc, with the map extending to a homeomorphism of
the closures" implies "Jordan". It is what makes the L5 milestone a *correspondence* rather than a
one-way sufficient condition, and it is the form in which the boundary hypothesis is checked in
practice, since a Riemann map is rarely available in closed form while its boundary values often
are.

## Main definitions

* `TauCeti.IsJordanDomain` — a bounded domain of `ℂ` whose frontier is a Jordan curve.

## Main results

* `TauCeti.sphereCircleHomeomorph` and `TauCeti.isJordanCurve_sphere` — a circle of positive radius
  in `ℂ` is a Jordan curve, by the explicit affine parametrization `w ↦ (w - c) / r`.
* `TauCeti.isJordanDomain_ball` — a disc of positive radius is a Jordan domain, the basic example
  and the one Carathéodory's theorem compares every other Jordan domain to.
* `TauCeti.isJordanCurve_frontier_of_isJordanCurve_frontier_image` and
  `TauCeti.isJordanDomain_of_image_eq_ball` — **the converse half of the Carathéodory
  correspondence**: if a conformal map on a bounded open `U` extends continuously and injectively
  to `closure U` and carries `U` onto a disc, then `U` is a Jordan domain.

## Generality

In accordance with the generality bar of `ConformalMapping/README.md`, which fixes scalar `ℂ` for
every theorem added in layers L0–L6, the results below are stated for maps of `ℂ`, as in
`Conformal/BoundaryCorrespondence.lean`; the purely topological content is in
`TauCeti/Topology/JordanCurve.lean`, where it is stated for an arbitrary topological space.

## Coordination with upstream Mathlib

Layer L5 is absent from
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), the in-progress
human-curated Riemann-mapping-theorem effort, which stops at the mapping theorem itself, and the
pinned Mathlib has no Jordan-curve vocabulary at all. So this file is new Lean formalization rather
than a temporary shim. It consumes, through `Conformal/BoundaryCorrespondence.lean`, the L0–L3 shim
`TauCeti.isOpen_image_of_differentiableOn_of_injOn`, to be refactored onto Mathlib once the
upstream work lands.

## References

* C. Carathéodory, *Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung*,
  Math. Ann. **73** (1913).
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. IX.
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Ch. 2.
-/

public section

namespace TauCeti

open Metric Set Topology

variable {U : Set ℂ} {f F : ℂ → ℂ} {c : ℂ} {r : ℝ}

/-! ## Circles and discs -/

/-- The affine parametrization `w ↦ (w - c) / r` of a circle of centre `c` and positive radius `r`
in `ℂ` by the unit circle. -/
noncomputable def sphereCircleHomeomorph (c : ℂ) (hr : 0 < r) : sphere c r ≃ₜ Circle where
  toFun w := ⟨((w : ℂ) - c) / r, mem_sphere_zero_iff_norm.2 (by
    have hw : ‖(w : ℂ) - c‖ = r := mem_sphere_iff_norm.1 w.2
    rw [norm_div, hw, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, div_self hr.ne'])⟩
  invFun z := ⟨c + r * (z : ℂ), by
    simp [mem_sphere_iff_norm, Circle.norm_coe, abs_of_pos hr]⟩
  left_inv w := by
    have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    apply Subtype.ext
    field_simp
    ring
  right_inv z := by
    have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    apply Circle.coe_injective
    field_simp
    ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The parametrization of `sphere c r` by the unit circle divides out the affine change of
coordinates. -/
@[simp]
lemma coe_sphereCircleHomeomorph_apply (c : ℂ) (hr : 0 < r) (w : sphere c r) :
    (sphereCircleHomeomorph c hr w : ℂ) = ((w : ℂ) - c) / r := by
  rw [sphereCircleHomeomorph]
  rfl

/-- The inverse parametrization of `sphere c r` by the unit circle is the affine change of
coordinates. -/
@[simp]
lemma coe_sphereCircleHomeomorph_symm_apply (c : ℂ) (hr : 0 < r) (z : Circle) :
    (((sphereCircleHomeomorph c hr).symm z : sphere c r) : ℂ) = c + r * (z : ℂ) := by
  rw [sphereCircleHomeomorph]
  rfl

/-- A circle of positive radius in `ℂ` is a Jordan curve. -/
theorem isJordanCurve_sphere (c : ℂ) (hr : 0 < r) : IsJordanCurve (sphere c r) :=
  isJordanCurve_iff.mpr ⟨sphereCircleHomeomorph c hr⟩

/-- A **Jordan domain**: a bounded domain of `ℂ` bounded by a Jordan curve.

Boundedness is part of the definition: the two complementary domains of a Jordan curve in the
sphere have the same boundary, and it is the bounded one — the *interior* of the curve — that the
Carathéodory correspondence compares to the unit disc. -/
structure IsJordanDomain (U : Set ℂ) : Prop where
  /-- A Jordan domain is open. -/
  isOpen : IsOpen U
  /-- A Jordan domain is connected, in particular nonempty. -/
  isConnected : IsConnected U
  /-- A Jordan domain is bounded. -/
  isBounded : Bornology.IsBounded U
  /-- The frontier of a Jordan domain is a Jordan curve. -/
  isJordanCurve_frontier : IsJordanCurve (frontier U)

/-- A disc of positive radius is a Jordan domain: its frontier is the circle of the same centre and
radius. This is the model Jordan domain, and the target of every Riemann map. -/
theorem isJordanDomain_ball (c : ℂ) (hr : 0 < r) : IsJordanDomain (ball c r) where
  isOpen := isOpen_ball
  isConnected := (convex_ball c r).isConnected (nonempty_ball.2 hr)
  isBounded := isBounded_ball
  isJordanCurve_frontier := by
    rw [frontier_ball c hr.ne']
    exact isJordanCurve_sphere c hr

/-! ## Elementary consequences of being a Jordan domain -/

/-- A Jordan domain is nonempty. -/
theorem IsJordanDomain.nonempty (h : IsJordanDomain U) : U.Nonempty := h.isConnected.nonempty

/-- The closure of a Jordan domain is compact. -/
theorem IsJordanDomain.isCompact_closure (h : IsJordanDomain U) : IsCompact (closure U) :=
  h.isBounded.isCompact_closure

/-- The frontier of a Jordan domain is nonempty; in particular a Jordan domain is a *proper* open
subset of `ℂ`, so that — once it is also simply connected — it satisfies the hypotheses of the
Riemann mapping theorem. -/
theorem IsJordanDomain.frontier_nonempty (h : IsJordanDomain U) : (frontier U).Nonempty :=
  h.isJordanCurve_frontier.nonempty

/-- A Jordan domain is not all of `ℂ`. -/
theorem IsJordanDomain.ne_univ (h : IsJordanDomain U) : U ≠ univ := by
  intro hU
  obtain ⟨w, hw⟩ := h.frontier_nonempty
  rw [hU, frontier_univ] at hw
  exact hw

/-! ## The converse half of the Carathéodory correspondence -/

/-- **A conformal map with an injective continuous extension transports the Jordan property back
across the boundary.** If a holomorphic `f` on a bounded open `U` has a continuous extension `F` to
`closure U` that is injective there, and the frontier of the image `f '' U` is a Jordan curve, then
so is the frontier of `U`.

The extension carries `frontier U` onto `frontier (f '' U)`
(`TauCeti.image_frontier_eq_frontier_image`) and is continuous and injective there, and `frontier U`
is compact because `U` is bounded; `TauCeti.IsJordanCurve.of_image` does the rest. Injectivity of
`f` on `U` is not assumed: it follows from that of `F` on `closure U`. -/
theorem isJordanCurve_frontier_of_isJordanCurve_frontier_image (hUo : IsOpen U)
    (hUb : Bornology.IsBounded U) (hfd : DifferentiableOn ℂ f U)
    (hFc : ContinuousOn F (closure U)) (hFf : EqOn F f U) (hFi : InjOn F (closure U))
    (h : IsJordanCurve (frontier (f '' U))) : IsJordanCurve (frontier U) := by
  have hcpt : IsCompact (frontier U) :=
    hUb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  exact IsJordanCurve.of_image hcpt (hFc.mono frontier_subset_closure)
    (hFi.mono frontier_subset_closure)
    (image_frontier_eq_frontier_image hUo hUb hfd hFc hFf hFi ▸ h)

/-- **The converse half of the Carathéodory boundary correspondence.** A bounded domain of `ℂ` that
a holomorphic map carries onto a disc, extending continuously and injectively to the closure, is a
Jordan domain.

Carathéodory's theorem — layer **L5** of the conformal-mapping roadmap — is the converse: for a
Jordan domain such an extension *exists*. Together the two say that, among bounded domains, being a
Jordan domain is exactly the condition under which the Riemann map extends to a homeomorphism of
the closures. -/
theorem isJordanDomain_of_image_eq_ball (hUo : IsOpen U) (hUc : IsConnected U)
    (hUb : Bornology.IsBounded U) (hfd : DifferentiableOn ℂ f U)
    (hFc : ContinuousOn F (closure U)) (hFf : EqOn F f U) (hFi : InjOn F (closure U))
    (hr : 0 < r) (himg : f '' U = ball c r) : IsJordanDomain U where
  isOpen := hUo
  isConnected := hUc
  isBounded := hUb
  isJordanCurve_frontier := by
    refine isJordanCurve_frontier_of_isJordanCurve_frontier_image hUo hUb hfd hFc hFf hFi ?_
    rw [himg, frontier_ball c hr.ne']
    exact isJordanCurve_sphere c hr

end TauCeti

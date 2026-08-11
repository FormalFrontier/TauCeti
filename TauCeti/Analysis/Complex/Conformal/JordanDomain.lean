/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.BoundaryCorrespondence
public import TauCeti.Topology.JordanCurve.Basic
public import TauCeti.Topology.UniformlyLocallyConnected
import Mathlib.Analysis.Normed.Module.Connected
import TauCeti.Analysis.Complex.Conformal.Biholomorph

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

* `TauCeti.isJordanDomain_of_convex` — a bounded convex domain of `ℂ` is a Jordan domain, on the
  frontier statement `TauCeti.isJordanCurve_frontier_of_convex` that generalises the circle.
* `TauCeti.isJordanDomain_ball` — its special case at a disc of positive radius, the basic example
  and the one Carathéodory's theorem compares every other Jordan domain to.
* `TauCeti.IsJordanDomain.locallyConnectedSpace_frontier` — the boundary of a Jordan domain is
  locally connected, which is the hypothesis the *hard* direction of the L5 milestone runs on:
  Carathéodory's continuity theorem produces a continuous extension of the Riemann map exactly for
  a locally connected boundary.
* `TauCeti.IsJordanDomain.isUniformlyLocallyConnected_frontier` — the same hypothesis in the
  uniform `ε`–`δ` form that proof actually consumes, available because the boundary is compact.
* `TauCeti.isJordanCurve_frontier_of_isJordanCurve_frontier_image`,
  `TauCeti.isJordanDomain_of_isJordanCurve_frontier_image` and
  `TauCeti.isJordanDomain_of_image_eq_ball` — **the converse half of the Carathéodory
  correspondence**: if a conformal map on a bounded open `U` extends continuously and injectively
  to `closure U` and carries `U` onto a connected set with Jordan frontier — a disc, in the last of
  the three — then `U` is itself a Jordan domain.

## Generality

In accordance with the generality bar of `ConformalMapping/README.md`, which fixes scalar `ℂ` for
every theorem added in layers L0–L6, the results below are stated for maps of `ℂ`, as in
`Conformal/BoundaryCorrespondence.lean`; the Jordan-curve vocabulary they are phrased in, together
with the circle that models it, is in `TauCeti/Topology/JordanCurve/Basic.lean`, where the
predicate and its transfer lemmas are stated for an arbitrary topological space.

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

/-! ## Jordan domains, and the convex domains among them -/

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

/-- **A bounded convex domain of `ℂ` is a Jordan domain.**

This is `TauCeti.isJordanDomain_ball` with the disc weakened to an arbitrary convex domain, which it
recovers at `U = Metric.ball c r`. An elliptical disc, the interior of a convex polygon, and any
nonempty bounded intersection of *finitely many* open half-planes are Jordan domains — finitely
many, since an infinite intersection of open half-planes is convex but need not be open.

Of the four defining conditions, openness and boundedness are the hypotheses `ho` and `hb`, taken
over unchanged. Connectedness is `hU` with `hne`: a nonempty convex set is connected. The Jordan
frontier is `hU`, `hne` and `hb` together, by `TauCeti.isJordanCurve_frontier_of_convex`, whose
solidity hypothesis `(interior U).Nonempty` is `hne` read through `ho`, the interior of an open set
being the set itself. -/
theorem isJordanDomain_of_convex (hU : Convex ℝ U) (ho : IsOpen U) (hne : U.Nonempty)
    (hb : Bornology.IsBounded U) : IsJordanDomain U where
  isOpen := ho
  isConnected := hU.isConnected hne
  isBounded := hb
  isJordanCurve_frontier :=
    isJordanCurve_frontier_of_convex hU (by rwa [ho.interior_eq]) hb

/-- A disc of positive radius is a Jordan domain: it is a bounded convex domain, and its frontier is
the circle of the same centre and radius. This is the model Jordan domain, and the target of every
Riemann map. -/
theorem isJordanDomain_ball (c : ℂ) (hr : 0 < r) : IsJordanDomain (ball c r) :=
  isJordanDomain_of_convex (convex_ball c r) isOpen_ball (nonempty_ball.mpr hr) isBounded_ball

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

/-- **The boundary of a Jordan domain is locally connected**, being a Jordan curve
(`TauCeti.IsJordanCurve.locallyConnectedSpace`).

This is the hypothesis under which Carathéodory's continuity theorem produces the continuous
extension, so it is what the hard direction of the L5 milestone asks of a Jordan domain; the
converse reading — that any continuous extension *carries* local connectedness to the image
boundary — is `TauCeti.locallyConnectedSpace_frontier_image` in
`Conformal/LocallyConnectedBoundary.lean`. -/
theorem IsJordanDomain.locallyConnectedSpace_frontier (h : IsJordanDomain U) :
    LocallyConnectedSpace (frontier U) :=
  h.isJordanCurve_frontier.locallyConnectedSpace

/-- **The boundary of a Jordan domain is uniformly locally connected**: nearby boundary points are
joined by connected subsets of the boundary that are small at a rate independent of where they sit.

This is `TauCeti.IsJordanDomain.locallyConnectedSpace_frontier` upgraded by
`TauCeti.IsCompact.isUniformlyLocallyConnected`, the upgrade costing nothing because the boundary
of a bounded set is compact. The uniform form is what the hard direction of the L5 milestone
consumes: Carathéodory's continuity theorem controls the image of a crosscut by joining its two
boundary endpoints inside a small connected piece of `frontier U`, and the estimate has to be
uniform over all crosscuts at once. -/
theorem IsJordanDomain.isUniformlyLocallyConnected_frontier (h : IsJordanDomain U) :
    IsUniformlyLocallyConnected (frontier U) :=
  haveI := h.locallyConnectedSpace_frontier
  IsCompact.isUniformlyLocallyConnected
    (h.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure)

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
  have hfi : InjOn f U := fun x hx y hy hxy =>
    hFi (subset_closure hx) (subset_closure hy) (by rw [hFf hx, hFf hy]; exact hxy)
  exact IsJordanCurve.of_image hcpt (hFc.mono frontier_subset_closure)
    (hFi.mono frontier_subset_closure)
    (image_frontier_eq_frontier_image hUo hUb hfd hfi hFc hFf ▸ h)

/-- **The converse half of the Carathéodory boundary correspondence.** A bounded open set of `ℂ`
that a holomorphic map carries onto a connected set with Jordan frontier, extending continuously
and injectively to the closure, is itself a Jordan domain.

Carathéodory's theorem — layer **L5** of the conformal-mapping roadmap — is the converse for the
disc: for a Jordan domain such an extension *exists*. Together the two say that, among bounded
domains, being a Jordan domain is exactly the condition under which the Riemann map extends to a
homeomorphism of the closures.

Only two of the four properties of a Jordan domain are asked of the image, since the other two are
already carried across by `f`: the image of an open set under an injective holomorphic map is open,
and the image is bounded because `F` is continuous on the compact `closure U`. A caller holding
`h : TauCeti.IsJordanDomain (f '' U)` supplies `h.isConnected` and `h.isJordanCurve_frontier`.
Connectedness of `U` itself is likewise not assumed: `f` is an open partial homeomorphism of `U`
onto `f '' U` (`TauCeti.DifferentiableOn.toOpenPartialHomeomorph`), so `U` is the image of the
connected `f '' U` under the continuous inverse. -/
theorem isJordanDomain_of_isJordanCurve_frontier_image (hUo : IsOpen U)
    (hUb : Bornology.IsBounded U) (hfd : DifferentiableOn ℂ f U)
    (hFc : ContinuousOn F (closure U)) (hFf : EqOn F f U) (hFi : InjOn F (closure U))
    (himgc : IsConnected (f '' U)) (himg : IsJordanCurve (frontier (f '' U))) :
    IsJordanDomain U where
  isOpen := hUo
  isConnected := by
    have hfi : InjOn f U := fun x hx y hy hxy =>
      hFi (subset_closure hx) (subset_closure hy) (by rw [hFf hx, hFf hy]; exact hxy)
    set e := DifferentiableOn.toOpenPartialHomeomorph hfd hUo hfi with he
    have htgt : e.target = f '' U := DifferentiableOn.toOpenPartialHomeomorph_target hfd hUo hfi
    have hsymm : e.symm '' (f '' U) = U := by
      rw [← htgt, e.symm_image_target_eq_source, he,
        DifferentiableOn.toOpenPartialHomeomorph_source]
    exact hsymm ▸ himgc.image _ (e.continuousOn_symm.mono htgt.ge)
  isBounded := hUb
  isJordanCurve_frontier :=
    isJordanCurve_frontier_of_isJordanCurve_frontier_image hUo hUb hfd hFc hFf hFi himg

/-- **The converse half of the Carathéodory boundary correspondence, for the disc.** A bounded open
set of `ℂ` that a holomorphic map carries onto a disc, extending continuously and injectively to
the closure, is a Jordan domain.

This is the case of `TauCeti.isJordanDomain_of_isJordanCurve_frontier_image` in which the image is
the model Jordan domain, and it is the form the Carathéodory correspondence is stated in, the disc
being the target of every Riemann map. -/
theorem isJordanDomain_of_image_eq_ball (hUo : IsOpen U)
    (hUb : Bornology.IsBounded U) (hfd : DifferentiableOn ℂ f U)
    (hFc : ContinuousOn F (closure U)) (hFf : EqOn F f U) (hFi : InjOn F (closure U))
    (hr : 0 < r) (himg : f '' U = ball c r) : IsJordanDomain U :=
  isJordanDomain_of_isJordanCurve_frontier_image hUo hUb hfd hFc hFf hFi
    (himg ▸ (isJordanDomain_ball c hr).isConnected)
    (himg ▸ (isJordanDomain_ball c hr).isJordanCurve_frontier)

end TauCeti

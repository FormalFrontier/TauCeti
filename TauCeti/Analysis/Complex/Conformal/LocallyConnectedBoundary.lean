/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import TauCeti.Analysis.Complex.Conformal.BoundaryCorrespondence
public import TauCeti.Analysis.Complex.Conformal.JordanDomain
public import TauCeti.Topology.LocallyConnected

/-!
# Local connectedness of the boundary of a conformally mapped domain

Carathéodory's *continuity theorem* — the analytic half of layer **L5** of the conformal-mapping
roadmap — says that a Riemann map `f : 𝔻 → Ω` extends continuously to the closed disc **if and only
if** `∂Ω` is locally connected. This file proves the "only if" half, the half that holds with no
hypothesis on the boundary at all: local connectedness is *carried along* by any continuous
extension, so a domain whose boundary is not locally connected admits no such extension.

The mechanism is purely topological and is isolated in `TauCeti/Topology/LocallyConnected.lean`:
local connectedness is not preserved by continuous images in general, but it is preserved by
quotient maps, and a continuous map of a compact space into a Hausdorff one is a quotient map onto
its image. `Conformal/BoundaryCorrespondence.lean` has already identified the two images in
question — a continuous extension `F` of a conformal map carries `closure U` onto
`closure (f '' U)` and `frontier U` onto `frontier (f '' U)` — so all that remains is to feed those
identifications the compactness that boundedness of `U` provides.

For the Riemann map itself the source side of the hypothesis is automatic, and the file records
that: the closed unit disc is convex and hence locally connected, and the unit circle is locally
connected by `TauCeti.locallyConnectedSpace_sphere`, an application of the same image theorem in
`TauCeti/Topology/JordanCurve.lean`. So the disc corollaries below carry no local-connectedness
hypothesis at all, and neither does the Jordan-domain corollary at the end of the file, whose
boundary is locally connected because it is a Jordan curve.

Together with `TauCeti.exists_continuousOn_closure_eqOn`, the extension criterion of
`TauCeti/Topology/ClusterSet.lean`, this delimits the L5 milestone from both sides: the criterion
says which boundary behaviour *produces* a continuous extension, and the results here say what any
continuous extension *forces* on the image boundary. The sufficiency half of the continuity
theorem, and with it the Jordan-domain milestone itself, is not proved here; what this file and
`TauCeti.IsJordanDomain.locallyConnectedSpace_frontier` supply for it is the hypothesis it runs
on — local connectedness of the boundary of a Jordan domain — together with the machinery that
transports it.

In accordance with the generality bar of `ConformalMapping/README.md`, which fixes scalar `ℂ` for
every theorem added in layers L0–L6, the results below are stated for maps of `ℂ`, as in
`Conformal/BoundaryCorrespondence.lean`; the topological engine they run on is stated for arbitrary
topological spaces.

## Main results

* `TauCeti.locallyConnectedSpace_closure_image` and
  `TauCeti.locallyConnectedSpace_frontier_image` — a continuous extension of a conformal map to the
  closure of a bounded domain carries local connectedness of the closure, respectively of the
  boundary, to the image.
* `TauCeti.locallyConnectedSpace_closure_image_ball` and
  `TauCeti.locallyConnectedSpace_frontier_image_ball` — the Riemann-map case: if a conformal map on
  the unit disc extends continuously to the closed disc, the closure and the boundary of its image
  are locally connected.
* `TauCeti.IsJordanDomain.locallyConnectedSpace_frontier_image` — the same for a conformal map on
  any Jordan domain, whose boundary is locally connected for free.

## Coordination with upstream Mathlib

Layer L5 is absent from
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), the in-progress
human-curated Riemann-mapping-theorem effort, which stops at the mapping theorem itself, and
Mathlib has no boundary correspondence for conformal maps. So this file is new Lean formalization
rather than a temporary shim. It consumes the L0–L3 shim
`TauCeti.isOpen_image_of_differentiableOn_of_injOn` through
`Conformal/BoundaryCorrespondence.lean`, to be refactored onto Mathlib once the upstream work
lands.

## References

* C. Carathéodory, *Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung*,
  Math. Ann. **73** (1913).
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Theorem 2.1.
* P. L. Duren, *Univalent Functions*, Ch. 3.
-/

public section

namespace TauCeti

open Complex Metric Set Topology

variable {U : Set ℂ} {f F : ℂ → ℂ}

/-! ## Local connectedness under a continuous extension -/

/-- **A continuous extension carries a locally connected closure to a locally connected closure.**
For a bounded `U`, an extension `F` of `f` continuous on `closure U` maps `closure U` onto
`closure (f '' U)`, and `closure U` is compact, so local connectedness passes along.

As with `TauCeti.image_closure_eq_closure_image`, which is what identifies the two sets, neither
holomorphy of `f` nor openness of `U` is used; a conformal `f` is the intended application. -/
theorem locallyConnectedSpace_closure_image [LocallyConnectedSpace (closure U)]
    (hUb : Bornology.IsBounded U) (hFc : ContinuousOn F (closure U)) (hFf : EqOn F f U) :
    LocallyConnectedSpace (closure (f '' U)) := by
  rw [← image_closure_eq_closure_image hUb hFc hFf]
  exact locallyConnectedSpace_image_of_isCompact hUb.isCompact_closure hFc

/-- **A continuous extension carries a locally connected boundary to a locally connected
boundary.** This is the "only if" half of Carathéodory's continuity theorem: a conformal map on a
bounded domain with locally connected boundary can extend continuously to the closure only if the
boundary of its image is locally connected too. No injectivity of the extension is assumed — only
the injectivity of `f` on `U` that makes it conformal.

The equality `TauCeti.image_frontier_eq_frontier_image` is what reaches *all* of the image boundary;
holomorphy enters only through it, to know that `f '' U` is open. -/
theorem locallyConnectedSpace_frontier_image [LocallyConnectedSpace (frontier U)] (hUo : IsOpen U)
    (hUb : Bornology.IsBounded U) (hfd : DifferentiableOn ℂ f U) (hfi : InjOn f U)
    (hFc : ContinuousOn F (closure U)) (hFf : EqOn F f U) :
    LocallyConnectedSpace (frontier (f '' U)) := by
  rw [← image_frontier_eq_frontier_image hUo hUb hfd hfi hFc hFf]
  exact locallyConnectedSpace_image_of_isCompact
    (isCompact_of_isClosed_isBounded isClosed_frontier
      (hUb.closure.subset frontier_subset_closure))
    (hFc.mono frontier_subset_closure)

/-! ## The Riemann-map case -/

/-- **The closure of the image of a Riemann map with a continuous extension is locally connected.**
The unit disc case of `TauCeti.locallyConnectedSpace_closure_image`: the closed disc is convex,
hence locally connected, so no hypothesis on the source boundary is left. As there, holomorphy of
`f` is not used — a conformal `f` is the intended application. -/
theorem locallyConnectedSpace_closure_image_ball (hFc : ContinuousOn F (closedBall 0 1))
    (hFf : EqOn F f (ball 0 1)) :
    LocallyConnectedSpace (closure (f '' ball (0 : ℂ) 1)) := by
  haveI : LocallyConnectedSpace (closure (ball (0 : ℂ) 1)) := by
    rw [closure_ball (0 : ℂ) one_ne_zero]
    haveI := (convex_closedBall (0 : ℂ) 1).locallyPathConnectedSpace
    infer_instance
  refine locallyConnectedSpace_closure_image (isBounded_ball) ?_ hFf
  rwa [closure_ball (0 : ℂ) one_ne_zero]

/-- **The boundary of the image of a Riemann map with a continuous extension is locally
connected.** The unit disc case of `TauCeti.locallyConnectedSpace_frontier_image`: the unit circle
is locally connected by `TauCeti.locallyConnectedSpace_sphere`, so no hypothesis on the source
boundary is left.

Contrapositively, a simply connected domain whose boundary is not locally connected — the comb
domain and the slit disc with a spiralling slit are the standard examples — admits no conformal
map from the disc extending continuously to the closed disc. -/
theorem locallyConnectedSpace_frontier_image_ball (hfd : DifferentiableOn ℂ f (ball 0 1))
    (hfi : InjOn f (ball 0 1)) (hFc : ContinuousOn F (closedBall 0 1))
    (hFf : EqOn F f (ball 0 1)) :
    LocallyConnectedSpace (frontier (f '' ball (0 : ℂ) 1)) := by
  haveI : LocallyConnectedSpace (frontier (ball (0 : ℂ) 1)) := by
    rw [frontier_ball (0 : ℂ) one_ne_zero]
    infer_instance
  have hcl : closure (ball (0 : ℂ) 1) = closedBall 0 1 := closure_ball (0 : ℂ) one_ne_zero
  exact locallyConnectedSpace_frontier_image isOpen_ball isBounded_ball hfd hfi (hcl ▸ hFc) hFf

/-! ## The Jordan-domain case -/

/-- **A conformal map of a Jordan domain that extends continuously has locally connected image
boundary.** The source-side hypothesis of `TauCeti.locallyConnectedSpace_frontier_image` is
automatic for a Jordan domain, since its boundary is a Jordan curve
(`TauCeti.IsJordanDomain.locallyConnectedSpace_frontier`).

Contrapositively: a domain whose boundary is not locally connected is not the image of a Jordan
domain under a conformal map extending continuously to the closure — in particular, taking the
disc for the Jordan domain, it is not one the Riemann map reaches with a continuous extension. -/
theorem IsJordanDomain.locallyConnectedSpace_frontier_image (hU : IsJordanDomain U)
    (hfd : DifferentiableOn ℂ f U) (hfi : InjOn f U) (hFc : ContinuousOn F (closure U))
    (hFf : EqOn F f U) : LocallyConnectedSpace (frontier (f '' U)) :=
  haveI := hU.locallyConnectedSpace_frontier
  _root_.TauCeti.locallyConnectedSpace_frontier_image hU.isOpen hU.isBounded hfd hfi hFc hFf

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import
  TauCeti.Analysis.Complex.Conformal.InverseBoundaryCluster
public import
  TauCeti.Analysis.Complex.Conformal.JordanDomain
import TauCeti.Topology.JordanCurve.SmallArc

/-!
# Jordan domains have preconnected approach regions

This file proves that every Jordan domain in `ℂ` has
preconnected approach regions at every boundary point,
i.e. `IsPreconnectedApproachAt U a` holds for every
`a ∈ frontier U` when `U` is a Jordan domain.

Combined with
`TauCeti.injOn_closedBall_of_isPreconnected_image_approach`
from `InverseBoundaryCluster.lean`, this gives an
end-to-end chain from a Jordan-domain hypothesis on the
conformal image to injectivity on the closed disc:

    IsJordanDomain (f '' ball c r)
    → IsPreconnectedApproachAt at every boundary point
    → preconnected boundary fibres
    → injective on closedBall c r

## The gap

The proof reduces to a single sorry in
`isPreconnected_inter_ball_of_locallyConnected_frontier`,
a planar topology result: a bounded open connected set
in `ℂ` whose frontier is locally connected has
preconnected intersection with every ball centered at a
boundary point.  This is the **Torhorst theorem** (1921).
TauCeti has the prerequisite
(`IsJordanCurve.locallyConnectedSpace`); the Torhorst
theorem itself is not formalized in Lean.

## The reduction chain (4 lemmas)

1. `isPreconnected_inter_ball_of_locallyConnected_frontier`
   — the Torhorst theorem, `sorry`. Pure planar topology.
2. `isPreconnected_jordanDomain_inter_ball` — wraps (1)
   using `IsJordanCurve.locallyConnectedSpace`.
3. `IsJordanDomain.isPreconnectedApproachAt` — wraps (2)
   into the predicate.
4. `IsJordanDomain.injOn_closedBall_of_conformal` —
   feeds (3) through `InverseBoundaryCluster`.

## Main results

* `TauCeti.IsJordanDomain.isPreconnectedApproachAt` —
  a Jordan domain has preconnected approach regions at
  every frontier point.
* `TauCeti.IsJordanDomain.injOn_closedBall_of_conformal`
  — if the conformal image of a disc is a Jordan domain,
  the continuous extension is injective on the closed disc.

## References

* C. Carathéodory, *Über die gegenseitige Beziehung der
  Ränder bei der konformen Abbildung*, Math. Ann. **73**
  (1913).
* M. Torhorst, *Über den Rand der einfach
  zusammenhängenden ebenen Gebiete*, Math. Z. **9**
  (1921).
* G. T. Whyburn, *Topological Analysis*, Ch. VI.
* D. Cureton, `sphere-six-complex`,
  github.com/deancureton/sphere-six-complex.
-/

@[expose] public section

open Set Metric Topology Function Filter

noncomputable section

namespace TauCeti

/-! ### The Torhorst theorem (sorry) -/

/-- **The Torhorst theorem (planar).**  A bounded open
connected subset of `ℂ` whose frontier is locally
connected (as a subspace) has preconnected intersection
with every ball centered at a frontier point.

Equivalently: such a set is locally connected at every
boundary point.  The statement is phrased with balls
because `IsPreconnectedApproachAt` needs preconnected
traces on neighborhoods, and metric balls generate the
neighborhood filter.

The classical proof (Whyburn, *Topological Analysis*
Ch. VI) uses three ingredients:
1. Boundary bumping: every component of `U ∩ V` (V open)
   has closure meeting `frontier U ∩ closure V`.
2. Local connectivity of the frontier provides connected
   neighborhoods in `frontier U` near `a`.
3. Unicoherence of the sphere (equivalently, Janiszewski's
   theorem — available as `TauCeti.janiszewski`): two
   compact connected sets in the sphere whose intersection
   is connected have a connected union.

None of (1)–(3) directly compose into a proof without
additional continuum-theoretic infrastructure. -/
theorem isPreconnected_inter_ball_of_lc_frontier
    {U : Set ℂ} {a : ℂ}
    (hUo : IsOpen U) (hUc : IsConnected U)
    (hUb : Bornology.IsBounded U)
    (ha : a ∈ frontier U)
    (_hlc : LocallyConnectedSpace (frontier U))
    {ε : ℝ} (hε : 0 < ε) :
    IsPreconnected (U ∩ ball a ε) := by
  sorry

/-! ### Jordan domain specialization -/

variable {U : Set ℂ} {a : ℂ}

/-- A Jordan domain has preconnected intersection with
every ball at a boundary point: the Torhorst theorem
specialized to Jordan-curve boundaries, which are locally
connected by
`IsJordanCurve.locallyConnectedSpace`. -/
theorem isPreconnected_jordanDomain_inter_ball
    (hU : IsJordanDomain U) (ha : a ∈ frontier U)
    {ε : ℝ} (hε : 0 < ε) :
    IsPreconnected (U ∩ ball a ε) :=
  isPreconnected_inter_ball_of_lc_frontier
    hU.isOpen hU.isConnected hU.isBounded ha
    hU.isJordanCurve_frontier.locallyConnectedSpace hε

/-! ### Assembly -/

/-- **A Jordan domain has preconnected approach regions at
every boundary point.**  Immediate from
`isPreconnected_jordanDomain_inter_ball`. -/
theorem IsJordanDomain.isPreconnectedApproachAt
    (hU : IsJordanDomain U) (ha : a ∈ frontier U) :
    IsPreconnectedApproachAt U a := by
  intro s hs
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.mp hs
  exact ⟨ball a ε, ball_mem_nhds a hε, hεs,
    isPreconnected_jordanDomain_inter_ball hU ha hε⟩

variable {f F : ℂ → ℂ} {c : ℂ} {r : ℝ}

/-- **Conformal injectivity on the closed disc when the
image is a Jordan domain.**  If `f` is holomorphic and
injective on `ball c r`, `F` is its continuous extension
to `closedBall c r`, and `f '' ball c r` is a Jordan
domain, then `F` is injective on `closedBall c r`.

Feeds `IsJordanDomain.isPreconnectedApproachAt` into
`injOn_closedBall_of_isPreconnected_image_approach`. -/
theorem IsJordanDomain.injOn_closedBall_of_conformal
    (hr : 0 < r)
    (hfd : DifferentiableOn ℂ f (ball c r))
    (hfi : InjOn f (ball c r))
    (hFc : ContinuousOn F (closedBall c r))
    (hFf : EqOn F f (ball c r))
    (hJ : IsJordanDomain (f '' ball c r)) :
    InjOn F (closedBall c r) :=
  injOn_closedBall_of_isPreconnected_image_approach
    hr hfd hfi hFc hFf
    fun _ ha => hJ.isPreconnectedApproachAt ha

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.ClusterSet
public import TauCeti.Topology.ClusterSet.Inverse

/-!
# Boundary cluster reciprocity for conformal maps

For a conformal injection `f : U → ℂ`, the set-level inverse
`Function.invFunOn f U : f '' U → U` exchanges boundary cluster membership with `f`: a boundary
value `v` belongs to the cluster set of `f` at `w` exactly when `w` belongs to the cluster set of
the inverse at `v`. The topological reciprocity theorem lives in
`TauCeti/Topology/ClusterSet/Inverse.lean`; this file applies it to the injectivity problem in the
Carathéodory boundary correspondence.

Suppose `F` extends `f` continuously to `closure U`. At every `w ∈ frontier U`, continuity makes
`F w` a cluster value of `f` at `w`, while conformality puts `F w` on
`frontier (f '' U)`. Reciprocity therefore puts `w` in the inverse cluster set at `F w`. If all
such inverse cluster sets are subsingletons, equal boundary values force equal boundary points.
The existing theorem `TauCeti.injOn_closure_of_injOn_frontier` then promotes this to injectivity on
the whole closure, exactly the hypothesis `TauCeti.closureHomeomorph` needs.

This is a clean prerequisite for layer **L5** of `TauCetiRoadmap/ConformalMapping/README.md`, whose
concrete milestone is that a Riemann map of a Jordan domain extends to a homeomorphism of closures.
It does not assert the still-missing singleton property: it isolates the inverse-cluster condition
that turns a continuous extension into the injective extension required by that milestone.

Layer L5 is absent from the in-progress human-curated Mathlib Riemann-mapping proof
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), which stops at L3.
Nothing here is vendored from that work. The conformal input is Tau Ceti's existing boundary-image
theorem `TauCeti.image_frontier_subset_frontier_image`; the reciprocal cluster-set argument is the
general topological result proved in the new sibling module.

## Main results

* `TauCeti.injOn_frontier_of_clusterSetOn_invFunOn_subsingleton` — singleton inverse boundary
  cluster sets make a continuous extension injective on the frontier.
* `TauCeti.injOn_closure_of_clusterSetOn_invFunOn_subsingleton` — the resulting injectivity on the
  entire closure.

## References

* C. Carathéodory, *Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung*,
  Math. Ann. **73** (1913).
* E. F. Collingwood and A. J. Lohwater, *The Theory of Cluster Sets*, Ch. 1.
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Theorem 2.1.
-/

public section

namespace TauCeti

open Complex Set Topology

variable {U : Set ℂ} {f F : ℂ → ℂ}

/-- **Singleton inverse boundary cluster sets make a continuous extension injective on the
frontier.** Let `f` be holomorphic and injective on an open set `U`, and let `F` be a continuous
extension to `closure U`. If, at every point of `frontier (f '' U)`, the cluster set of
`Function.invFunOn f U` along `f '' U` is a subsingleton, then `F` is injective on `frontier U`.

No boundedness or connectedness hypothesis is needed. Conformality is used only to send the source
frontier into the image frontier; cluster reciprocity and continuity do the injectivity argument. -/
theorem injOn_frontier_of_clusterSetOn_invFunOn_subsingleton (hUo : IsOpen U)
    (hfd : DifferentiableOn ℂ f U) (hfi : InjOn f U)
    (hFc : ContinuousOn F (closure U)) (hFf : EqOn F f U)
    (hsub : ∀ v ∈ frontier (f '' U),
      (clusterSetOn (Function.invFunOn f U) (f '' U) v).Subsingleton) :
    InjOn F (frontier U) := by
  have hbij : BijOn f U (f '' U) := hfi.bijOn_image
  exact injOn_of_clusterSetOn_invOn_subsingleton_of_continuousOn_extension
    frontier_subset_closure
    (image_subset_iff.mp (image_frontier_subset_frontier_image hUo hfd hfi hFc hFf))
    hFc hFf hbij.invOn_invFunOn hbij.mapsTo hbij.surjOn.mapsTo_invFunOn hsub

/-- **Singleton inverse boundary cluster sets make a continuous extension injective on the whole
closure.** This is the closure form of
`TauCeti.injOn_frontier_of_clusterSetOn_invFunOn_subsingleton`, and directly supplies the final
injectivity hypothesis of `TauCeti.closureHomeomorph`.

The interior is already handled by injectivity of `f`; a boundary value cannot collide with an
interior value because a continuous extension of a conformal map sends the frontier outside the
open image. -/
theorem injOn_closure_of_clusterSetOn_invFunOn_subsingleton (hUo : IsOpen U)
    (hfd : DifferentiableOn ℂ f U) (hfi : InjOn f U)
    (hFc : ContinuousOn F (closure U)) (hFf : EqOn F f U)
    (hsub : ∀ v ∈ frontier (f '' U),
      (clusterSetOn (Function.invFunOn f U) (f '' U) v).Subsingleton) :
    InjOn F (closure U) :=
  injOn_closure_of_injOn_frontier hUo hfd hfi hFc hFf
    (injOn_frontier_of_clusterSetOn_invFunOn_subsingleton hUo hfd hfi hFc hFf hsub)

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Classification.SubgroupQuotient
public import TauCeti.Topology.Covering.Quotient

/-!
# The covering associated to a subgroup

For a subgroup `H ≤ π₁(X, x₀)`, `UniversalCover.SubgroupQuotient x₀ H` is already defined as
the orbit quotient of the universal cover by `H`, and `UniversalCover.subgroupQuotientProj`
is its descended endpoint projection. This file proves that the descended projection is a
covering map.

The two inputs are that `UniversalCover.proj` and `UniversalCover.subgroupQuotientMap` are
quotient covering maps, for `π₁(X, x₀)` and for `H` respectively, and that the first factors
through the second. `TauCeti.IsQuotientCoveringMap.isCoveringMap_of_comp` turns exactly that
data into a covering map: the sheets of the descended projection over the image of a locally
disjoint set `U` are the images of the translates of `U`. Nothing about good neighbourhoods of
the base, their path-connectedness, or the transport of a sheet of `proj` along the
fundamental-group action enters here, because the general statement uses only the disjointness
built into `IsQuotientCoveringMap`.

The conclusion is not inherited formally from the two quotient maps being covering maps: the
deck group of `UniversalCover x₀ / H` over `X` is the normalizer quotient `N(H) / H`, which is
transitive on the fibres only for normal `H`, so the descended projection is generally not
itself a quotient covering map for any group.

## Main declaration

* `TauCeti.UniversalCover.isCoveringMap_subgroupQuotientProj`: the cover associated to
  `H ≤ π₁(X, x₀)` is a covering space of `X`.

## References

This completes the existence half in `TauCetiRoadmap/UniversalCovers/README.md`, Stage 2,
item 7: construct the pointed connected cover `UniversalCover x₀ / H`. It uses the universal
cover adapted from Kim Morrison's
[mathlib4#38292](https://github.com/leanprover-community/mathlib4/pull/38292) and Mathlib's
quotient-covering-map interface due to Junyan Xu.
-/

public section

variable {X : Type*} [TopologicalSpace X]

namespace TauCeti.UniversalCover

/-- The endpoint projection on the quotient of the universal cover by `H` is a covering map. -/
theorem isCoveringMap_subgroupQuotientProj [LocallyPathConnectedSpace X]
    [PathConnectedSpace X] [SemilocallySimplyConnectedSpace X]
    (x₀ : X) (H : Subgroup (FundamentalGroup X x₀)) :
    IsCoveringMap (subgroupQuotientProj x₀ H) :=
  IsQuotientCoveringMap.isCoveringMap_of_comp (isQuotientCoveringMap (x₀ := x₀))
    (isQuotientCoveringMap_subgroupQuotientMap x₀ H)
    (subgroupQuotientProj_comp_subgroupQuotientMap x₀ H)

end TauCeti.UniversalCover

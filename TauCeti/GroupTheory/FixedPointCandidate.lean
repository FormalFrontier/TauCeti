/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.DerivedCentralQuotient
public import TauCeti.GroupTheory.FixedSubgroup

/-!
# The candidate simple group attached to an endomorphism

For an endomorphism `F` of a group `G` this file composes the two constructions of
`TauCeti.GroupTheory.FixedSubgroup` and `TauCeti.GroupTheory.DerivedCentralQuotient` into

```text
FixedPointCandidate F = [H, H] / Z([H, H]),  where  H = fixedSubgroup F,
```

the group the classification's Lie-type lane attaches to a Steinberg endomorphism of a pinned
algebraic group. Nothing here asserts that the result is finite or simple, and no ambient group is
involved: the composite is a carrier-independent prerequisite for the later family-by-family
construction.

## Main definitions

* `TauCeti.FixedPointCandidate`: the derived central quotient of a fixed subgroup.

## References

This is the composite prescribed by milestone L3 of `TauCetiRoadmap/CFSGStatement/README.md`, which
fixes `H_d = fixedSubgroup d.steinberg` and `d.Group = [H_d, H_d] / Z([H_d, H_d])`, with the centre
read as the centre of the derived subgroup rather than of `H_d`. The construction is standard; see
R. W. Carter, *Simple Groups of Lie Type*, and D. Gorenstein, R. Lyons and R. Solomon, *The
Classification of the Finite Simple Groups*.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G]

/-- The candidate simple group attached to an endomorphism `F` of a group: the derived subgroup of
the fixed points of `F`, modulo the centre of that derived subgroup.

For the Steinberg endomorphisms constructed by the roadmap, this is the corresponding finite group
of Lie type outside the small parameters excluded by `LieTypeIndex.InStandardRange`; at those
parameters it can be trivial, nonsimple, a duplicate, or the separately indexed Tits group. None of
these properties is asserted here. -/
abbrev FixedPointCandidate (F : G →* G) : Type _ :=
  DerivedCentralQuotient ↥(fixedSubgroup F)

end TauCeti

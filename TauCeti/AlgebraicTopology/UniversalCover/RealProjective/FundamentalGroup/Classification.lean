/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.RealProjective.FundamentalGroup.Basic
public import TauCeti.AlgebraicTopology.UniversalCover.RealProjective.FundamentalGroup.Line
public import TauCeti.AlgebraicTopology.UniversalCover.RealProjective.FundamentalGroup.Zero

/-!
# Fundamental groups of real projective spaces in every dimension

The fundamental group of real projective space has three dimension ranges:

* `RP⁰` is a point, so its fundamental group has one element;
* `RP¹` is a circle, so its fundamental group is infinite cyclic;
* `RPⁿ` has a two-element fundamental group for `2 ≤ n`.

The three group isomorphisms are constructed in the imported dimension-specific modules. This file
records their common cardinality consequence. Recall that `Nat.card` is zero on an infinite type,
so the value zero in dimension one expresses infinitude, not an empty fundamental group.

## Main result

* `TauCeti.RealProjectiveSpace.card_fundamentalGroup`: the cardinality trichotomy
  `1, 0, 2` in dimensions `0, 1, ≥ 2`, respectively.

## Roadmap

This assembles the `π₁(RPⁿ)` application in Stage 4, item 13 of
`TauCetiRoadmap/UniversalCovers/README.md`. The dimension-zero input is
`TauCeti.RealProjectiveSpace.Zero.fundamentalGroupMulEquiv`; the circle case is
`TauCeti.RealProjectiveSpace.Line.fundamentalGroupMulEquiv`; and the higher-dimensional input is
`TauCeti.RealProjectiveSpace.fundamentalGroupMulEquiv`.

## References

* A. Hatcher, *Algebraic Topology*, Section 1.1 and Corollary 1.15.
-/

public section

namespace TauCeti.RealProjectiveSpace

noncomputable section

/-- **The cardinality trichotomy for fundamental groups of real projective spaces.**

The values are `1` in dimension zero, `0` in dimension one because that fundamental group is
infinite, and `2` in every dimension at least two. -/
-- This is not a simp lemma: for symbolic `n`, its right-hand side is a stuck match on `n`.
theorem card_fundamentalGroup (n : ℕ) (x : RealProjectiveSpace n) :
    Nat.card (FundamentalGroup (RealProjectiveSpace n) x) =
      match n with
      | 0 => 1
      | 1 => 0
      | _ + 2 => 2 := by
  rcases n with _ | n
  · exact Zero.card_fundamentalGroup x
  · rcases n with _ | n
    · exact Line.card_fundamentalGroup x
    · exact card_fundamentalGroup_of_two_le (n + 2) (by omega) x

end

end TauCeti.RealProjectiveSpace

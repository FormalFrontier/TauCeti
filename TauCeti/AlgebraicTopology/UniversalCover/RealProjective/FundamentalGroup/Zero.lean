/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import TauCeti.AlgebraicTopology.UniversalCover.RealProjective.Basic

/-!
# The fundamental group of zero-dimensional real projective space

Real projective zero-space is a single point: the unit sphere in `ℝ¹` consists of two antipodal
points, and the antipodal quotient identifies them. The sibling modules compute the fundamental
group of `RP¹` and of `RPⁿ` for `2 ≤ n`; this file supplies the remaining boundary case.

The existing theorem `TauCeti.RealProjectiveSpace.subsingleton_zero` gives uniqueness directly.
Together with the quotient's nonemptiness, Mathlib's generic contractibility instance for a
nonempty subsingleton space makes `RP⁰` contractible and hence simply connected. It follows that
the fundamental group at its unique point is the trivial group.

## Main declarations

* `TauCeti.RealProjectiveSpace.Zero.instUnique`: `RP⁰` has exactly one point.
* `TauCeti.RealProjectiveSpace.Zero.fundamentalGroupMulEquiv`: the fundamental group of `RP⁰`
  is the trivial group `PUnit`.
* `TauCeti.RealProjectiveSpace.Zero.card_fundamentalGroup`: the fundamental group has one
  element.

## Roadmap

This closes the `n = 0` boundary case of `π₁(RPⁿ)` in Stage 4, item 13 of
`TauCetiRoadmap/UniversalCovers/README.md`. The `n = 1` case is
`TauCeti.RealProjectiveSpace.Line.fundamentalGroupMulEquiv`, while
`TauCeti.RealProjectiveSpace.fundamentalGroupMulEquiv` covers `2 ≤ n`.

## References

* A. Hatcher, *Algebraic Topology*, Section 1.1.
-/

public section

namespace TauCeti.RealProjectiveSpace.Zero

noncomputable section

/-- Zero-dimensional real projective space has exactly one point. -/
instance instUnique : Unique (RealProjectiveSpace 0) :=
  letI : Subsingleton (RealProjectiveSpace 0) := subsingleton_zero
  uniqueOfSubsingleton (Nonempty.some inferInstance)

/-- **The fundamental group of `RP⁰` is trivial.** At its unique basepoint it is isomorphic to
the one-element group `PUnit`. -/
def fundamentalGroupMulEquiv (x : RealProjectiveSpace 0) :
    FundamentalGroup (RealProjectiveSpace 0) x ≃* PUnit :=
  letI : Unique (FundamentalGroup (RealProjectiveSpace 0) x) := uniqueOfSubsingleton 1
  MulEquiv.ofUnique

/-- The equivalence from the fundamental group of `RP⁰` takes every loop class to the unique
element of `PUnit`. -/
@[simp]
theorem fundamentalGroupMulEquiv_apply (x : RealProjectiveSpace 0)
    (γ : FundamentalGroup (RealProjectiveSpace 0) x) :
    fundamentalGroupMulEquiv x γ = PUnit.unit :=
  Subsingleton.elim _ _

/-- The fundamental group of `RP⁰` has exactly one element. -/
theorem card_fundamentalGroup (x : RealProjectiveSpace 0) :
    Nat.card (FundamentalGroup (RealProjectiveSpace 0) x) = 1 :=
  Nat.card_unique

end

end TauCeti.RealProjectiveSpace.Zero

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.Homeomorph
public import TauCeti.AlgebraicTopology.NotSimplyConnected
public import TauCeti.AlgebraicTopology.UniversalCover.ComplexCircleFundamentalGroup
public import TauCeti.AlgebraicTopology.UniversalCover.RealProjective.Circle

/-!
# The fundamental group of the real projective line is `ℤ`

For `n = 1`, real projective space `RP¹` is homeomorphic to the circle `Circle` via
`TauCeti.RealProjectiveSpace.Line.homeomorphCircle`.

Transporting the circle computation `π₁(Circle, z) ≃* Multiplicative ℤ`
(`TauCeti.Circle.fundamentalGroupMulEquiv`) across `RP¹ ≃ₜ Circle` gives

  `π₁(RP¹, x) ≃* Multiplicative ℤ`

at any basepoint `x : RealProjectiveSpace 1`.

For `2 ≤ n`, the fundamental group computation is developed in the sibling module
`TauCeti.AlgebraicTopology.UniversalCover.RealProjective.FundamentalGroup.Basic`, yielding
`π₁(RPⁿ) ≅ ℤˣ` conditional on the simple-connectivity instance for `Sⁿ`.

## Main declarations

* `TauCeti.RealProjectiveSpace.Line.fundamentalGroupMulEquiv`: `π₁(RP¹, x) ≃* Multiplicative ℤ` at
  any basepoint.
* `TauCeti.RealProjectiveSpace.Line.nontrivial_fundamentalGroup`: `π₁(RP¹, x)` is nontrivial.
* `TauCeti.RealProjectiveSpace.Line.infinite_fundamentalGroup`: `π₁(RP¹, x)` is infinite.
* `TauCeti.RealProjectiveSpace.Line.not_simplyConnectedSpace`: `RP¹` is not simply connected.
* `TauCeti.RealProjectiveSpace.Line.not_contractibleSpace`: `RP¹` is not contractible.

## References

This advances `TauCetiRoadmap/UniversalCovers/README.md`, Stage 4, item 13, `π₁(RPⁿ)`, by
closing its `n = 1` case.
-/

public section

namespace TauCeti

namespace RealProjectiveSpace

namespace Line

noncomputable section

/-- **The fundamental group of the real projective line is infinite cyclic.** The isomorphism is
obtained by transporting the complex-circle computation across `homeomorphCircle`. -/
def fundamentalGroupMulEquiv (x : RealProjectiveSpace 1) :
    FundamentalGroup (RealProjectiveSpace 1) x ≃* Multiplicative ℤ :=
  (FundamentalGroup.homeomorphMulEquiv homeomorphCircle x).trans
    (Circle.fundamentalGroupMulEquiv (homeomorphCircle x))

/-- `fundamentalGroupMulEquiv` factors through the homeomorphism from the real projective line
to the circle and the circle fundamental-group computation. -/
theorem fundamentalGroupMulEquiv_def (x : RealProjectiveSpace 1) :
    fundamentalGroupMulEquiv x =
      (FundamentalGroup.homeomorphMulEquiv homeomorphCircle x).trans
        (Circle.fundamentalGroupMulEquiv (homeomorphCircle x)) :=
  by
    unfold fundamentalGroupMulEquiv
    rfl

/-- The fundamental group of `RP¹` at any basepoint is nontrivial. -/
theorem nontrivial_fundamentalGroup (x : RealProjectiveSpace 1) :
    Nontrivial (FundamentalGroup (RealProjectiveSpace 1) x) :=
  (fundamentalGroupMulEquiv x).toEquiv.nontrivial

/-- The fundamental group of `RP¹` at any basepoint is infinite. -/
theorem infinite_fundamentalGroup (x : RealProjectiveSpace 1) :
    Infinite (FundamentalGroup (RealProjectiveSpace 1) x) :=
  Infinite.of_injective _ (fundamentalGroupMulEquiv x).symm.injective

/-- The real projective line is not simply connected. -/
theorem not_simplyConnectedSpace : ¬ SimplyConnectedSpace (RealProjectiveSpace 1) :=
  haveI := nontrivial_fundamentalGroup basepoint
  not_simplyConnectedSpace_of_nontrivial_fundamentalGroup basepoint

/-- The real projective line is not contractible. -/
theorem not_contractibleSpace : ¬ ContractibleSpace (RealProjectiveSpace 1) :=
  not_contractibleSpace_of_not_simplyConnectedSpace not_simplyConnectedSpace

end
end Line
end RealProjectiveSpace
end TauCeti

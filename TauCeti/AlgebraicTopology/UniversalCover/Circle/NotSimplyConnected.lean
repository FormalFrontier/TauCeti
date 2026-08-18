/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.NotSimplyConnected
public import TauCeti.AlgebraicTopology.UniversalCover.Circle.FundamentalGroup

/-!
# The circle is not simply connected

The circle computation `π₁(AddCircle p) ≃* Multiplicative ℤ`
(`AddCircle.fundamentalGroupMulEquiv`) has an immediate qualitative payoff: since
`Multiplicative ℤ` is nontrivial and infinite, so is the fundamental group of the circle, and
therefore the circle is **not simply connected**. Being non-simply-connected, it is not
contractible, and it is not homeomorphic to any simply connected space; in particular the
circle is not homeomorphic to the real line nor to any real normed space.

These are the standard topological consequences of `π₁(S¹) ≅ ℤ`, and they realise the
universal-covers roadmap Stage 4 "applications" (`TauCetiRoadmap/UniversalCovers/README.md`),
extending the circle computation (item 12, `π₁(S¹) ≅ ℤ`) to the classical fact that the
circle and the line are topologically distinct.

The nontriviality and infinitude of the fundamental group are transported from
`Multiplicative ℤ` along the circle equivalence. Non-simple-connectivity then follows because
a simply connected space has a subsingleton fundamental group. The homeomorphism statements
consume Mathlib's transfer of `SimplyConnectedSpace` along a homotopy equivalence
(`ContinuousMap.HomotopyEquiv.simplyConnectedSpace`, via `Homeomorph.toHomotopyEquiv`) and the
contractibility of a real topological vector space
(`RealTopologicalVectorSpace.contractibleSpace`). No Mathlib code is vendored.

## Main declarations

* `AddCircle.nontrivial_fundamentalGroup`, `AddCircle.infinite_fundamentalGroup`: the fundamental
  group of `AddCircle p` (`p ≠ 0`), at any basepoint, is nontrivial and infinite.
* `AddCircle.not_simplyConnectedSpace`: `AddCircle p` is not simply connected.
* `AddCircle.not_contractibleSpace`: `AddCircle p` is not contractible.
* `AddCircle.isEmpty_homeomorph_of_simplyConnectedSpace`,
  `AddCircle.isEmpty_homeomorph_realTopologicalVectorSpace`,
  `AddCircle.isEmpty_homeomorph_real`: `AddCircle p` is not homeomorphic to a simply
  connected space, to a real topological vector space, or to `ℝ`.
* `UnitAddCircle.*`: the specialisations to the unit circle `S¹ = ℝ ⧸ ℤ`.
-/

public section

namespace AddCircle

variable (p : ℝ)

/-- The fundamental group of the circle `AddCircle p` (`p ≠ 0`), based at any point `x`, is
nontrivial. See `fundamentalGroupMulEquiv` for the full winding-number classification. -/
theorem nontrivial_fundamentalGroup (hp : p ≠ 0) (x : AddCircle p) :
    Nontrivial (FundamentalGroup (AddCircle p) x) := by
  obtain ⟨e, rfl⟩ := QuotientAddGroup.mk_surjective x
  exact (fundamentalGroupMulEquiv p hp ⟨e, rfl⟩).toEquiv.nontrivial

/-- The fundamental group of the circle `AddCircle p` (`p ≠ 0`), based at any point `x`, is
infinite. See `fundamentalGroupMulEquiv` for the full winding-number classification. -/
theorem infinite_fundamentalGroup (hp : p ≠ 0) (x : AddCircle p) :
    Infinite (FundamentalGroup (AddCircle p) x) := by
  obtain ⟨e, rfl⟩ := QuotientAddGroup.mk_surjective x
  exact Infinite.of_injective _ (fundamentalGroupMulEquiv p hp ⟨e, rfl⟩).symm.injective

/-- The fundamental group of the circle `AddCircle p` (`p ≠ 0`), based at `0`, is nontrivial. -/
theorem nontrivial_fundamentalGroup_zero (hp : p ≠ 0) :
    Nontrivial (FundamentalGroup (AddCircle p) 0) :=
  nontrivial_fundamentalGroup p hp 0

/-- The fundamental group of the circle `AddCircle p` (`p ≠ 0`), based at `0`, is infinite. -/
theorem infinite_fundamentalGroup_zero (hp : p ≠ 0) :
    Infinite (FundamentalGroup (AddCircle p) 0) :=
  infinite_fundamentalGroup p hp 0

/-- The circle `AddCircle p` (`p ≠ 0`) is **not simply connected**: its fundamental group is
nontrivial, whereas a simply connected space has a subsingleton fundamental group. -/
theorem not_simplyConnectedSpace (hp : p ≠ 0) : ¬ SimplyConnectedSpace (AddCircle p) :=
  haveI := nontrivial_fundamentalGroup_zero p hp
  TauCeti.not_simplyConnectedSpace_of_nontrivial_fundamentalGroup (0 : AddCircle p)

/-- The circle `AddCircle p` (`p ≠ 0`) is **not contractible**: a contractible space is simply
connected, and the circle is not. -/
theorem not_contractibleSpace (hp : p ≠ 0) : ¬ ContractibleSpace (AddCircle p) :=
  TauCeti.not_contractibleSpace_of_not_simplyConnectedSpace (not_simplyConnectedSpace p hp)

/-- The circle `AddCircle p` (`p ≠ 0`) is not homeomorphic to any simply connected space: a
homeomorphism is in particular a homotopy equivalence, and simple connectivity transfers along
homotopy equivalences, which the circle does not enjoy. -/
theorem isEmpty_homeomorph_of_simplyConnectedSpace (hp : p ≠ 0)
    (Y : Type*) [TopologicalSpace Y] [SimplyConnectedSpace Y] :
    IsEmpty (AddCircle p ≃ₜ Y) :=
  TauCeti.isEmpty_homeomorph_of_not_simplyConnectedSpace (not_simplyConnectedSpace p hp) Y

/-- The circle `AddCircle p` (`p ≠ 0`) is not homeomorphic to any real topological vector space
(in particular, to any real normed space), since such a space is contractible, hence simply
connected. -/
theorem isEmpty_homeomorph_realTopologicalVectorSpace (hp : p ≠ 0) (E : Type*)
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E] :
    IsEmpty (AddCircle p ≃ₜ E) :=
  TauCeti.isEmpty_homeomorph_realTopologicalVectorSpace_of_not_simplyConnectedSpace
    (not_simplyConnectedSpace p hp) E

/-- The circle `AddCircle p` (`p ≠ 0`) is not homeomorphic to the real line: the circle is not
simply connected but `ℝ` is contractible. -/
theorem isEmpty_homeomorph_real (hp : p ≠ 0) : IsEmpty (AddCircle p ≃ₜ ℝ) :=
  TauCeti.isEmpty_homeomorph_real_of_not_simplyConnectedSpace (not_simplyConnectedSpace p hp)

end AddCircle

namespace UnitAddCircle

/-- The fundamental group of the unit circle `S¹ = ℝ ⧸ ℤ`, based at `0`, is nontrivial. -/
theorem nontrivial_fundamentalGroup_zero : Nontrivial (FundamentalGroup UnitAddCircle 0) :=
  AddCircle.nontrivial_fundamentalGroup_zero 1 one_ne_zero

/-- The fundamental group of the unit circle `S¹ = ℝ ⧸ ℤ`, based at `0`, is infinite. -/
theorem infinite_fundamentalGroup_zero : Infinite (FundamentalGroup UnitAddCircle 0) :=
  AddCircle.infinite_fundamentalGroup_zero 1 one_ne_zero

/-- The unit circle `S¹ = ℝ ⧸ ℤ` is not simply connected. -/
theorem not_simplyConnectedSpace : ¬ SimplyConnectedSpace UnitAddCircle :=
  AddCircle.not_simplyConnectedSpace 1 one_ne_zero

/-- The unit circle `S¹ = ℝ ⧸ ℤ` is not contractible. -/
theorem not_contractibleSpace : ¬ ContractibleSpace UnitAddCircle :=
  AddCircle.not_contractibleSpace 1 one_ne_zero

/-- The unit circle `S¹ = ℝ ⧸ ℤ` is not homeomorphic to the real line. -/
theorem isEmpty_homeomorph_real : IsEmpty (UnitAddCircle ≃ₜ ℝ) :=
  AddCircle.isEmpty_homeomorph_real 1 one_ne_zero

end UnitAddCircle

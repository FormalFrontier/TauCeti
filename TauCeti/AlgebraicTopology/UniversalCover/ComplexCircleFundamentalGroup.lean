/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import TauCeti.AlgebraicTopology.FundamentalGroup.Homeomorph
public import TauCeti.AlgebraicTopology.NotSimplyConnected
public import TauCeti.AlgebraicTopology.UniversalCover.Circle.FundamentalGroup

/-!
# The fundamental group of the complex unit circle is `ℤ`

The additive-circle computation `π₁(AddCircle p) ≃* Multiplicative ℤ`
(`TauCeti.AddCircle.fundamentalGroupMulEquiv`) lives on the quotient `ℝ ⧸ (p • ℤ)`. Mathlib's
canonical circle is instead `Circle`, the unit sphere `{z : ℂ | ‖z‖ = 1}` with its complex
multiplicative group structure, and the two are identified by the homeomorphism
`AddCircle.homeomorphCircle : AddCircle (2 * π) ≃ₜ Circle` (which sends `0` to `1`).

Transporting the additive-circle computation across that homeomorphism gives the fundamental
group at the canonical basepoint `1 : Circle`. Mathlib's basepoint-change isomorphism
`FundamentalGroup.fundamentalGroupMulEquivOfPathConnected` then gives the result at any
`x : Circle`:

  `π₁(Circle, x) ≃* Multiplicative ℤ`.

The canonical-basepoint computation uses the concrete lift `0 : ℝ` through
`TauCeti.AddCircle.fundamentalGroupMulEquivZero`.

This is the `Circle ⊆ ℂ` instance of the universal-covers roadmap Stage 4 target `π₁(S¹) ≅ ℤ`
(`TauCetiRoadmap/UniversalCovers/README.md`, item 12), realised on the standard Mathlib circle
that the homeomorphism-invariance API was built to reach
(`TauCeti/AlgebraicTopology/FundamentalGroup/Homeomorph.lean` names it as the intended
application). The qualitative corollaries — the fundamental group is nontrivial and infinite,
so `Circle` is neither simply connected nor contractible, and in particular is not
homeomorphic to the real line — follow exactly as for `AddCircle`. No Mathlib code is vendored.

## Main declarations

* `TauCeti.Circle.homeomorphCircle_symm_one`: `AddCircle.homeomorphCircle.symm 1 = 0`.
* `TauCeti.Circle.fundamentalGroupMulEquiv`: `π₁(Circle, x) ≃* Multiplicative ℤ`.
* `TauCeti.Circle.fundamentalGroupMulEquiv_def`: factorization through basepoint change and the
  canonical-basepoint circle computation.
* `TauCeti.Circle.nontrivial_fundamentalGroup`, `TauCeti.Circle.infinite_fundamentalGroup`:
  the fundamental group of `Circle`, based at `x`, is nontrivial and infinite.
* `TauCeti.Circle.not_simplyConnectedSpace`, `TauCeti.Circle.not_contractibleSpace`:
  `Circle` is not simply connected and not contractible.
* `TauCeti.Circle.isEmpty_homeomorph_real`: `Circle` is not homeomorphic to `ℝ`.
-/

public section

namespace TauCeti

namespace Circle

open scoped Real

noncomputable section

/-- The inverse homeomorphism `AddCircle.homeomorphCircle.symm` carries `1 : Circle` to `0`. -/
@[simp]
theorem homeomorphCircle_symm_one :
    (AddCircle.homeomorphCircle (T := 2 * Real.pi) Real.two_pi_pos.ne').symm 1 = 0 := by
  rw [Homeomorph.symm_apply_eq, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_zero]

/-- The fundamental group of the complex unit circle `Circle = {z : ℂ | ‖z‖ = 1}`, based at
`x`, is `Multiplicative ℤ`: `π₁(S¹, x) ≅ ℤ`. It is obtained by changing the basepoint to
`1 : Circle`, then transporting the additive-circle computation at `0` across
`AddCircle.homeomorphCircle : AddCircle (2 * π) ≃ₜ Circle`. -/
def fundamentalGroupMulEquiv (x : Circle) : FundamentalGroup Circle x ≃* Multiplicative ℤ :=
  (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected x 1).trans
    ((FundamentalGroup.homeomorphMulEquivOfEq
          (AddCircle.homeomorphCircle (T := 2 * Real.pi) Real.two_pi_pos.ne').symm
          homeomorphCircle_symm_one).trans
      (AddCircle.fundamentalGroupMulEquivZero (2 * Real.pi) Real.two_pi_pos.ne'))

/-- `fundamentalGroupMulEquiv` factors through Mathlib's basepoint-change isomorphism, followed
by the canonical-basepoint circle computation transported from `AddCircle`. -/
theorem fundamentalGroupMulEquiv_def (x : Circle) :
    fundamentalGroupMulEquiv x =
      (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected x 1).trans
        ((FundamentalGroup.homeomorphMulEquivOfEq
          (AddCircle.homeomorphCircle (T := 2 * Real.pi) Real.two_pi_pos.ne').symm
            homeomorphCircle_symm_one).trans
          (AddCircle.fundamentalGroupMulEquivZero (2 * Real.pi) Real.two_pi_pos.ne')) :=
  by
    unfold fundamentalGroupMulEquiv
    rfl

/-- The fundamental group of the complex unit circle `Circle`, based at `x`, is nontrivial. See
`fundamentalGroupMulEquiv` for the full identification with `Multiplicative ℤ`. -/
theorem nontrivial_fundamentalGroup (x : Circle) : Nontrivial (FundamentalGroup Circle x) :=
  (fundamentalGroupMulEquiv x).toEquiv.nontrivial

/-- The fundamental group of the complex unit circle `Circle`, based at `x`, is infinite. See
`fundamentalGroupMulEquiv` for the full identification with `Multiplicative ℤ`. -/
theorem infinite_fundamentalGroup (x : Circle) : Infinite (FundamentalGroup Circle x) :=
  Infinite.of_injective _ (fundamentalGroupMulEquiv x).symm.injective

/-- The complex unit circle `Circle` is **not simply connected**: its fundamental group is
nontrivial, whereas a simply connected space has a subsingleton fundamental group. -/
theorem not_simplyConnectedSpace : ¬ SimplyConnectedSpace Circle :=
  haveI := nontrivial_fundamentalGroup 1
  not_simplyConnectedSpace_of_nontrivial_fundamentalGroup (1 : Circle)

/-- The complex unit circle `Circle` is **not contractible**: a contractible space is simply
connected, and the circle is not. -/
theorem not_contractibleSpace : ¬ ContractibleSpace Circle :=
  not_contractibleSpace_of_not_simplyConnectedSpace not_simplyConnectedSpace

/-- The complex unit circle `Circle` is not homeomorphic to any simply connected space: a
homeomorphism is a homotopy equivalence, and simple connectivity transfers along homotopy
equivalences, which the circle does not enjoy. -/
theorem isEmpty_homeomorph_of_simplyConnectedSpace (Y : Type*) [TopologicalSpace Y]
    [SimplyConnectedSpace Y] : IsEmpty (Circle ≃ₜ Y) :=
  isEmpty_homeomorph_of_not_simplyConnectedSpace not_simplyConnectedSpace Y

/-- The complex unit circle `Circle` is not homeomorphic to any real topological vector space
(in particular, to any real normed space), since such a space is contractible, hence simply
connected. -/
theorem isEmpty_homeomorph_realTopologicalVectorSpace (E : Type*) [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E] : IsEmpty (Circle ≃ₜ E) :=
  isEmpty_homeomorph_realTopologicalVectorSpace_of_not_simplyConnectedSpace
    not_simplyConnectedSpace E

/-- The complex unit circle `Circle` is not homeomorphic to the real line: the circle is not
simply connected but `ℝ` is contractible. -/
theorem isEmpty_homeomorph_real : IsEmpty (Circle ≃ₜ ℝ) :=
  isEmpty_homeomorph_real_of_not_simplyConnectedSpace not_simplyConnectedSpace

end

end Circle

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Instances.Complex
public import TauCeti.AlgebraicTopology.FundamentalGroup.Homeomorph
public import TauCeti.AlgebraicTopology.NotSimplyConnected
public import TauCeti.AlgebraicTopology.UniversalCover.ComplexCircleFundamentalGroup
public import TauCeti.AlgebraicTopology.UniversalCover.RealProjective.Basic
public import TauCeti.Geometry.Sphere.Circle
public import TauCeti.Geometry.Sphere.LinearIsometry

/-!
# The fundamental group of the real projective line is `ℤ`

For `n = 1`, real projective space `RP¹` is homeomorphic to the circle `Circle` via the map
sending the antipodal class of a unit vector `(x₀, x₁) ∈ S¹ ⊆ ℝ²`, identified with `z = x₀ + i x₁`,
to `z² ∈ Circle`. The map is well-defined because `(-z)² = z²`, and is a continuous bijection
from a compact space to a Hausdorff space, hence a homeomorphism.

Transporting the circle computation `π₁(Circle, z) ≃* Multiplicative ℤ`
(`TauCeti.Circle.fundamentalGroupMulEquiv`) across `RP¹ ≃ₜ Circle` gives

  `π₁(RP¹, x) ≃* Multiplicative ℤ`

at any basepoint `x : RealProjectiveSpace 1`.

For `2 ≤ n`, the fundamental group computation is developed in the sibling module
`TauCeti.AlgebraicTopology.UniversalCover.RealProjective.FundamentalGroup.Basic`, yielding
`π₁(RPⁿ) ≅ ℤˣ` conditional on the simple-connectivity instance for `Sⁿ`.

## Main declarations

* `TauCeti.RealProjectiveSpace.toCircleOne`: the squared complex coordinate on `RP¹`.
* `TauCeti.RealProjectiveSpace.homeomorphCircleOne`: the homeomorphism `RP¹ ≃ₜ Circle`.
* `TauCeti.RealProjectiveSpace.basepointOne`: the natural basepoint of `RP¹` corresponding
  to `1 : Circle`.
* `TauCeti.RealProjectiveSpace.fundamentalGroupMulEquivOne`: `π₁(RP¹, x) ≃* Multiplicative ℤ` at
  any basepoint.
* `TauCeti.RealProjectiveSpace.fundamentalGroupMulEquivOne_def`: the factorization of that
  isomorphism into the homeomorphism-invariance isomorphism and the circle computation.
* `TauCeti.RealProjectiveSpace.nontrivial_fundamentalGroup_one`: `π₁(RP¹, x)` is nontrivial.
* `TauCeti.RealProjectiveSpace.infinite_fundamentalGroup_one`: `π₁(RP¹, x)` is infinite.
* `TauCeti.RealProjectiveSpace.not_simplyConnectedSpace_one`: `RP¹` is not simply connected.
* `TauCeti.RealProjectiveSpace.not_contractibleSpace_one`: `RP¹` is not contractible.

## References

This advances `TauCetiRoadmap/UniversalCovers/README.md`, Stage 4, item 13, `π₁(RPⁿ)`, by
closing its `n = 1` case. It consumes Mathlib's `Complex.orthonormalBasisOneI`, restricted to unit
spheres by `TauCeti.LinearIsometryEquiv.unitSphereEquiv` /
`TauCeti.LinearIsometryEquiv.unitSphereIsometryEquiv`
(`TauCeti/Geometry/Sphere/LinearIsometry.lean`), Mathlib's `Circle.isQuotientCoveringMap_npow`, and
Tau Ceti's circle fundamental-group calculation; no external formalization is vendored.
-/

public section

namespace TauCeti

open Metric
open scoped _root_.EuclideanSpace Real

namespace RealProjectiveSpace

noncomputable section

/-- The map from `RP¹` to the complex circle induced by squaring a unit-vector representative.
Squaring makes the value independent of the choice between the two antipodal representatives. -/
def toCircleOne : RealProjectiveSpace 1 → Circle :=
  RealProjectiveSpace.lift 1 (fun x => EuclideanSpace.sphereHomeomorphCircle x ^ 2) fun x => by
    ext
    push_cast
    simp [EuclideanSpace.coe_sphereHomeomorphCircle_apply, map_neg]
    ring

/-- On a unit-vector representative, `toCircleOne` is the square of its complex coordinate. -/
@[simp]
lemma toCircleOne_mk (x : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    toCircleOne (mk 1 x) = EuclideanSpace.sphereHomeomorphCircle x ^ 2 :=
  RealProjectiveSpace.lift_mk 1 _ _ x

/-- The squared-coordinate map from `RP¹` to the complex circle is continuous. -/
private lemma continuous_toCircleOne : Continuous toCircleOne :=
  (isQuotientMap_mk 1).continuous_iff.mpr
    ((EuclideanSpace.sphereHomeomorphCircle.continuous.pow 2).congr
      fun x => (toCircleOne_mk x).symm)

/-- The squared-coordinate map from `RP¹` to the complex circle is injective. -/
private lemma injective_toCircleOne : Function.Injective toCircleOne := by
  intro x y hxy
  obtain ⟨x, rfl⟩ := mk_surjective 1 x
  obtain ⟨y, rfl⟩ := mk_surjective 1 y
  rw [toCircleOne_mk, toCircleOne_mk] at hxy
  have hxy' : (EuclideanSpace.sphereHomeomorphCircle x : ℂ) ^ 2 =
      (EuclideanSpace.sphereHomeomorphCircle y : ℂ) ^ 2 := by
    rw [← Circle.coe_pow, ← Circle.coe_pow, hxy]
  obtain h | h := sq_eq_sq_iff_eq_or_eq_neg.mp hxy'
  · exact congrArg (mk 1) (EuclideanSpace.sphereHomeomorphCircle.injective <| Circle.ext h)
  · rw [mk_eq_mk_iff]
    refine Or.inr <| EuclideanSpace.sphereHomeomorphCircle.injective ?_
    ext
    simp [EuclideanSpace.coe_sphereHomeomorphCircle_apply, map_neg, h]

/-- The squared-coordinate map from `RP¹` to the complex circle is surjective. -/
private lemma surjective_toCircleOne : Function.Surjective toCircleOne := by
  intro z
  obtain ⟨w, hw⟩ := (Circle.isQuotientCoveringMap_npow 2).surjective z
  refine ⟨mk 1 (EuclideanSpace.sphereHomeomorphCircle.symm w), ?_⟩
  rw [toCircleOne_mk, EuclideanSpace.sphereHomeomorphCircle.apply_symm_apply]
  exact hw

/-- The squared-coordinate map from `RP¹` to the complex circle is bijective. -/
private lemma bijective_toCircleOne : Function.Bijective toCircleOne :=
  ⟨injective_toCircleOne, surjective_toCircleOne⟩

/-- **The real projective line is homeomorphic to the circle.** The map sends the antipodal class
of a unit vector, viewed as a complex number `z`, to `z²`. -/
def homeomorphCircleOne : RealProjectiveSpace 1 ≃ₜ Circle :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective toCircleOne bijective_toCircleOne)
    continuous_toCircleOne

/-- The homeomorphism `RP¹ ≃ₜ Circle` evaluates as the squared-coordinate map. -/
@[simp]
lemma homeomorphCircleOne_apply (x : RealProjectiveSpace 1) :
    homeomorphCircleOne x = toCircleOne x := by
  have h : homeomorphCircleOne.toEquiv =
      Equiv.ofBijective toCircleOne bijective_toCircleOne :=
    Continuous.toEquiv_homeoOfEquivCompactToT2
      (f := Equiv.ofBijective toCircleOne bijective_toCircleOne) continuous_toCircleOne
  exact congrFun (congrArg (fun e : RealProjectiveSpace 1 ≃ Circle =>
    (e : RealProjectiveSpace 1 → Circle)) h) x

/-- A natural basepoint of `RP¹`: the antipodal class of the Euclidean unit vector corresponding
to `1 : ℂ` under `sphereHomeomorphCircle`. -/
def basepointOne : RealProjectiveSpace 1 :=
  mk 1 (EuclideanSpace.sphereHomeomorphCircle.symm 1)

/-- The squared-coordinate map on `RP¹` sends the natural basepoint to `1 : Circle`. -/
@[simp]
lemma toCircleOne_basepointOne : toCircleOne basepointOne = 1 := by
  simp [basepointOne]

/-- **The fundamental group of the real projective line is infinite cyclic.** The isomorphism is
obtained by transporting the complex-circle computation across `homeomorphCircleOne`. -/
def fundamentalGroupMulEquivOne (x : RealProjectiveSpace 1) :
    FundamentalGroup (RealProjectiveSpace 1) x ≃* Multiplicative ℤ :=
  (FundamentalGroup.homeomorphMulEquiv homeomorphCircleOne x).trans
    (Circle.fundamentalGroupMulEquiv (homeomorphCircleOne x))

/-- `fundamentalGroupMulEquivOne` factors as the homeomorphism-invariance isomorphism of
`homeomorphCircleOne` composed with the circle equivalence. This exposes the definition so
consumers can reason about the isomorphism. -/
theorem fundamentalGroupMulEquivOne_def (x : RealProjectiveSpace 1) :
    fundamentalGroupMulEquivOne x =
      (FundamentalGroup.homeomorphMulEquiv homeomorphCircleOne x).trans
        (Circle.fundamentalGroupMulEquiv (homeomorphCircleOne x)) := by
  unfold fundamentalGroupMulEquivOne
  rfl

/-- The fundamental group of `RP¹` at any basepoint is nontrivial. -/
theorem nontrivial_fundamentalGroup_one (x : RealProjectiveSpace 1) :
    Nontrivial (FundamentalGroup (RealProjectiveSpace 1) x) :=
  (fundamentalGroupMulEquivOne x).toEquiv.nontrivial

/-- The fundamental group of `RP¹` at any basepoint is infinite. -/
theorem infinite_fundamentalGroup_one (x : RealProjectiveSpace 1) :
    Infinite (FundamentalGroup (RealProjectiveSpace 1) x) :=
  Infinite.of_injective _ (fundamentalGroupMulEquivOne x).symm.injective

/-- The real projective line is not simply connected. -/
theorem not_simplyConnectedSpace_one : ¬ SimplyConnectedSpace (RealProjectiveSpace 1) :=
  haveI := nontrivial_fundamentalGroup_one basepointOne
  not_simplyConnectedSpace_of_nontrivial_fundamentalGroup basepointOne

/-- The real projective line is not contractible. -/
theorem not_contractibleSpace_one : ¬ ContractibleSpace (RealProjectiveSpace 1) :=
  not_contractibleSpace_of_not_simplyConnectedSpace not_simplyConnectedSpace_one

end

end RealProjectiveSpace

end TauCeti

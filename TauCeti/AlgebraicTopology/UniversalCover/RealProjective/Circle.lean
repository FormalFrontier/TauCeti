/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homeomorph.Lemmas
public import TauCeti.AlgebraicTopology.UniversalCover.RealProjective.Basic
public import TauCeti.Geometry.Sphere.Circle

/-!
# The real projective line is homeomorphic to the circle

For `n = 1`, real projective space `RP¹` is homeomorphic to the complex unit circle `Circle` via
the map sending the antipodal class of a unit vector `(x₀, x₁) ∈ S¹ ⊆ ℝ²`, identified with
`z = x₀ + i x₁`, to `z² ∈ Circle`. The map is well-defined because `(-z)² = z²`, and is a
continuous bijection from a compact space to a Hausdorff space, hence a homeomorphism.

## Main declarations

* `TauCeti.RealProjectiveSpace.Line.toCircle`: the squared complex coordinate on `RP¹`.
* `TauCeti.RealProjectiveSpace.Line.toCircle_mk`: evaluation of `toCircle` on a unit vector.
* `TauCeti.RealProjectiveSpace.Line.homeomorphCircle`: the homeomorphism `RP¹ ≃ₜ Circle`.
* `TauCeti.RealProjectiveSpace.Line.homeomorphCircle_apply`: forward evaluation of
  `homeomorphCircle`.
* `TauCeti.RealProjectiveSpace.Line.homeomorphCircle_symm_apply`: backward evaluation of
  `homeomorphCircle`.
* `TauCeti.RealProjectiveSpace.Line.basepoint`: the natural basepoint of `RP¹` corresponding
  to `1 : Circle`.
* `TauCeti.RealProjectiveSpace.Line.toCircle_basepoint`: `toCircle` sends `basepoint` to `1`.

## References

This supports the `n = 1` case of `π₁(RPⁿ)` in `TauCetiRoadmap/UniversalCovers/README.md`, Stage 4,
item 13.
-/

public section

namespace TauCeti

open Metric
open scoped _root_.EuclideanSpace Real

namespace RealProjectiveSpace

namespace Line

noncomputable section

/-- The map from `RP¹` to the complex circle induced by squaring a unit-vector representative.
Squaring makes the value independent of the choice between the two antipodal representatives. -/
def toCircle : RealProjectiveSpace 1 → Circle :=
  RealProjectiveSpace.lift 1 (fun x => EuclideanSpace.sphereHomeomorphCircle x ^ 2) fun x => by
    rw [EuclideanSpace.sphereHomeomorphCircle_neg]
    exact neg_sq _

/-- On a unit-vector representative, `toCircle` is the square of its complex coordinate. -/
@[simp]
lemma toCircle_mk (x : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    toCircle (mk 1 x) = EuclideanSpace.sphereHomeomorphCircle x ^ 2 :=
  RealProjectiveSpace.lift_mk 1 _ _ x

/-- The squared-coordinate map from `RP¹` to the complex circle is continuous. -/
private lemma continuous_toCircle : Continuous toCircle :=
  (isQuotientMap_mk 1).continuous_iff.mpr
    ((EuclideanSpace.sphereHomeomorphCircle.continuous.pow 2).congr
      fun x => (toCircle_mk x).symm)

/-- The squared-coordinate map from `RP¹` to the complex circle is injective. -/
private lemma injective_toCircle : Function.Injective toCircle := by
  intro x y hxy
  obtain ⟨x, rfl⟩ := mk_surjective 1 x
  obtain ⟨y, rfl⟩ := mk_surjective 1 y
  rw [toCircle_mk, toCircle_mk] at hxy
  have hxy' : (EuclideanSpace.sphereHomeomorphCircle x : ℂ) ^ 2 =
      (EuclideanSpace.sphereHomeomorphCircle y : ℂ) ^ 2 := by
    rw [← Circle.coe_pow, ← Circle.coe_pow, hxy]
  obtain h | h := sq_eq_sq_iff_eq_or_eq_neg.mp hxy'
  · exact congrArg (mk 1) (EuclideanSpace.sphereHomeomorphCircle.injective <| Circle.ext h)
  · rw [mk_eq_mk_iff]
    refine Or.inr <| EuclideanSpace.sphereHomeomorphCircle.injective ?_
    rw [EuclideanSpace.sphereHomeomorphCircle_neg]
    exact Circle.ext h

/-- The squared-coordinate map from `RP¹` to the complex circle is surjective. -/
private lemma surjective_toCircle : Function.Surjective toCircle := by
  intro z
  obtain ⟨w, hw⟩ := (Circle.isQuotientCoveringMap_npow 2).surjective z
  refine ⟨mk 1 (EuclideanSpace.sphereHomeomorphCircle.symm w), ?_⟩
  rw [toCircle_mk, EuclideanSpace.sphereHomeomorphCircle.apply_symm_apply]
  exact hw

/-- The squared-coordinate map from `RP¹` to the complex circle is bijective. -/
private lemma bijective_toCircle : Function.Bijective toCircle :=
  ⟨injective_toCircle, surjective_toCircle⟩

/-- **The real projective line is homeomorphic to the circle.** The map sends the antipodal class
of a unit vector, viewed as a complex number `z`, to `z²`. -/
def homeomorphCircle : RealProjectiveSpace 1 ≃ₜ Circle :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective toCircle bijective_toCircle)
    continuous_toCircle

/-- The homeomorphism `RP¹ ≃ₜ Circle` evaluates as the squared-coordinate map. -/
@[simp]
lemma homeomorphCircle_apply (x : RealProjectiveSpace 1) :
    homeomorphCircle x = toCircle x :=
  congrArg (fun e : RealProjectiveSpace 1 ≃ Circle => e x)
    (Continuous.toEquiv_homeoOfEquivCompactToT2 continuous_toCircle)

/-- The inverse homeomorphism `Circle ≃ₜ RP¹` evaluates on squares of unit vectors. -/
@[simp]
lemma homeomorphCircle_symm_apply (w : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    homeomorphCircle.symm (EuclideanSpace.sphereHomeomorphCircle w ^ 2) = mk 1 w := by
  rw [Homeomorph.symm_apply_eq, homeomorphCircle_apply, toCircle_mk]

/-- A natural basepoint of `RP¹`: the antipodal class of the Euclidean unit vector corresponding
to `1 : ℂ` under `sphereHomeomorphCircle`. -/
def basepoint : RealProjectiveSpace 1 :=
  mk 1 (EuclideanSpace.sphereHomeomorphCircle.symm 1)

/-- The squared-coordinate map on `RP¹` sends the natural basepoint to `1 : Circle`. -/
@[simp]
lemma toCircle_basepoint : toCircle basepoint = 1 := by
  simp [basepoint]

end
end Line
end RealProjectiveSpace
end TauCeti

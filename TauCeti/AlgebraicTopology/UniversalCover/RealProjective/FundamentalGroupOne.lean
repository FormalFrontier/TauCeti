/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas
public import TauCeti.AlgebraicTopology.UniversalCover.ComplexCircleFundamentalGroup
public import TauCeti.AlgebraicTopology.UniversalCover.RealProjective.Basic
public import TauCeti.Geometry.Sphere.LinearIsometry

/-!
# The fundamental group of the real projective line

Real projective one-space is the quotient of the unit circle in `EuclideanSpace ℝ (Fin 2)` by
the antipodal action. Squaring a point of the complex unit circle identifies exactly the two
antipodal points, so it descends to a homeomorphism

  `RealProjectiveSpace 1 ≃ₜ Circle`.

The proof first identifies the Euclidean unit circle with Mathlib's complex `Circle` through
`Complex.orthonormalBasisOneI`. The squared complex coordinate is continuous and constant on
antipodal orbits. It is injective on the orbit quotient because two complex numbers with equal
squares are equal or negatives, and it is surjective because Mathlib's power map on `Circle` is a
quotient covering map. A continuous bijection from the compact quotient to the Hausdorff circle is
then a homeomorphism.

Transporting the circle fundamental group computation across this homeomorphism computes the
exceptional one-dimensional case of the real-projective-space fundamental group:

  `FundamentalGroup (RealProjectiveSpace 1) x ≃* Multiplicative ℤ`.

For dimensions at least two the antipodal cover has deck group `ℤˣ`, as proved in
`TauCeti.AlgebraicTopology.UniversalCover.RealProjective.Deck`, but completing that computation
also needs the separate theorem that the higher-dimensional sphere is simply connected. Thus the
line is genuinely exceptional: its fundamental group is infinite cyclic, not the order-two deck
group of its non-universal antipodal cover.

## Main declarations

* `TauCeti.RealProjectiveSpace.sphereOneHomeomorphCircle`: the Euclidean unit circle is
  homeomorphic to the complex unit circle.
* `TauCeti.RealProjectiveSpace.toCircle`: the squared complex coordinate on `RP¹`.
* `TauCeti.RealProjectiveSpace.oneHomeomorphCircle`: the homeomorphism `RP¹ ≃ₜ Circle`.
* `TauCeti.RealProjectiveSpace.fundamentalGroupOneMulEquiv`: `π₁(RP¹, x) ≃* Multiplicative ℤ` at
  any basepoint.
* `TauCeti.RealProjectiveSpace.fundamentalGroupOneMulEquiv_def`: the factorization of that
  isomorphism into homeomorphisms and the additive-circle computation.

This advances `TauCetiRoadmap/UniversalCovers/README.md`, Stage 4, item 13, `π₁(RPⁿ)`, by
closing its `n = 1` case. It consumes Mathlib's orthonormal-basis isometry and the quotient
covering map for powers of `Circle`, together with Tau Ceti's existing circle fundamental-group
calculation; no external formalization is vendored.
-/

public section

namespace TauCeti

open Metric
open scoped EuclideanSpace Real

namespace RealProjectiveSpace

noncomputable section

/-- The unit sphere in the two-dimensional real Euclidean space is homeomorphic to Mathlib's
complex unit circle. -/
def sphereOneHomeomorphCircle :
    sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ Circle :=
  (IsometryEquiv.mk
    (LinearIsometryEquiv.unitSphereEquiv Complex.orthonormalBasisOneI.repr.symm)
    (LinearIsometryEquiv.isometry_unitSphereEquiv
      Complex.orthonormalBasisOneI.repr.symm)).toHomeomorph

/-- The Euclidean-circle homeomorphism is the standard orthonormal-coordinate isometry on
underlying points. -/
@[simp]
lemma sphereOneHomeomorphCircle_coe
    (x : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    (sphereOneHomeomorphCircle x : ℂ) = Complex.orthonormalBasisOneI.repr.symm x :=
  LinearIsometryEquiv.coe_unitSphereEquiv_apply Complex.orthonormalBasisOneI.repr.symm x

/-- The Euclidean-circle homeomorphism intertwines the antipodal maps. -/
@[simp]
lemma sphereOneHomeomorphCircle_neg
    (x : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    sphereOneHomeomorphCircle (-x) = -sphereOneHomeomorphCircle x := by
  ext
  rw [sphereOneHomeomorphCircle_coe, Circle.coe_neg, sphereOneHomeomorphCircle_coe]
  exact map_neg Complex.orthonormalBasisOneI.repr.symm (x : EuclideanSpace ℝ (Fin 2))

/-- The map from `RP¹` to the complex circle induced by squaring a unit-vector representative.
Squaring makes the value independent of the choice between the two antipodal representatives. -/
def toCircle : RealProjectiveSpace 1 → Circle :=
  RealProjectiveSpace.lift 1 (fun x => sphereOneHomeomorphCircle x ^ 2) fun x => by
    rw [sphereOneHomeomorphCircle_neg, neg_sq]

/-- On a unit-vector representative, `toCircle` is the square of its complex coordinate. -/
@[simp]
lemma toCircle_mk (x : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    toCircle (mk 1 x) = sphereOneHomeomorphCircle x ^ 2 :=
  RealProjectiveSpace.lift_mk 1 _ _ x

/-- The squared-coordinate map from `RP¹` to the complex circle is continuous. -/
private lemma continuous_toCircle : Continuous toCircle :=
  (isQuotientMap_mk 1).continuous_iff.mpr
    ((sphereOneHomeomorphCircle.continuous.pow 2).congr fun x => (toCircle_mk x).symm)

/-- The squared-coordinate map from `RP¹` to the complex circle is injective. -/
private lemma injective_toCircle : Function.Injective toCircle := by
  intro x y hxy
  obtain ⟨x, rfl⟩ := mk_surjective 1 x
  obtain ⟨y, rfl⟩ := mk_surjective 1 y
  rw [toCircle_mk, toCircle_mk] at hxy
  have hxy' : (sphereOneHomeomorphCircle x : ℂ) ^ 2 =
      (sphereOneHomeomorphCircle y : ℂ) ^ 2 := congrArg Subtype.val hxy
  obtain h | h := sq_eq_sq_iff_eq_or_eq_neg.mp hxy'
  · exact congrArg (mk 1) (sphereOneHomeomorphCircle.injective <| Circle.ext h)
  · rw [mk_eq_mk_iff]
    refine Or.inr <| sphereOneHomeomorphCircle.injective ?_
    rw [sphereOneHomeomorphCircle_neg]
    exact Circle.ext h

/-- The squared-coordinate map from `RP¹` to the complex circle is surjective. -/
private lemma surjective_toCircle : Function.Surjective toCircle := by
  intro z
  obtain ⟨w, hw⟩ := (Circle.isQuotientCoveringMap_npow 2).surjective z
  refine ⟨mk 1 (sphereOneHomeomorphCircle.symm w), ?_⟩
  rw [toCircle_mk, sphereOneHomeomorphCircle.apply_symm_apply]
  exact hw

/-- **The real projective line is homeomorphic to the circle.** The map sends the antipodal class
of a unit vector, viewed as a complex number `z`, to `z²`. -/
def oneHomeomorphCircle : RealProjectiveSpace 1 ≃ₜ Circle :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective toCircle ⟨injective_toCircle, surjective_toCircle⟩)
    continuous_toCircle

/-- The homeomorphism `RP¹ ≃ₜ Circle` evaluates as the squared-coordinate map. -/
@[simp]
lemma oneHomeomorphCircle_apply (x : RealProjectiveSpace 1) :
    oneHomeomorphCircle x = toCircle x := by
  have h : oneHomeomorphCircle.toEquiv =
      Equiv.ofBijective toCircle ⟨injective_toCircle, surjective_toCircle⟩ :=
    Continuous.toEquiv_homeoOfEquivCompactToT2 continuous_toCircle
  exact congrFun (congrArg Equiv.toFun h) x

/-- A natural basepoint of `RP¹`: the antipodal class of the Euclidean unit vector corresponding
to `1 : ℂ`. -/
def oneBasepoint : RealProjectiveSpace 1 :=
  mk 1 (sphereOneHomeomorphCircle.symm 1)

/-- The squared-coordinate map on `RP¹` sends the natural basepoint to `1 : Circle`. -/
@[simp]
lemma toCircle_oneBasepoint : toCircle oneBasepoint = 1 := by
  simp [oneBasepoint]

/-- The homeomorphism from the real projective line to the circle sends the natural basepoint to
`1 : Circle`. -/
@[simp]
lemma oneHomeomorphCircle_oneBasepoint : oneHomeomorphCircle oneBasepoint = 1 := by
  rw [oneHomeomorphCircle_apply, toCircle_oneBasepoint]

/-- **The fundamental group of the real projective line is infinite cyclic.** The isomorphism is
obtained by transporting the additive-circle computation across `oneHomeomorphCircle` and
`AddCircle.homeomorphCircle`. -/
def fundamentalGroupOneMulEquiv (x : RealProjectiveSpace 1) :
    FundamentalGroup (RealProjectiveSpace 1) x ≃* Multiplicative ℤ :=
  (FundamentalGroup.homeomorphMulEquiv oneHomeomorphCircle x).trans
    ((FundamentalGroup.homeomorphMulEquiv
        (AddCircle.homeomorphCircle (T := 2 * Real.pi) Real.two_pi_pos.ne').symm
        (oneHomeomorphCircle x)).trans
      (AddCircle.fundamentalGroupMulEquiv (2 * Real.pi) Real.two_pi_pos.ne'
        ⟨Classical.choose (QuotientAddGroup.mk_surjective
          ((AddCircle.homeomorphCircle (T := 2 * Real.pi) Real.two_pi_pos.ne').symm
            (oneHomeomorphCircle x))),
         Classical.choose_spec (QuotientAddGroup.mk_surjective _)⟩))

/-- `fundamentalGroupOneMulEquiv` factors as the homeomorphism-invariance isomorphism of
`oneHomeomorphCircle` composed with the circle homeomorphism and the additive-circle
equivalence. This exposes the definition so consumers can reason about the isomorphism. -/
theorem fundamentalGroupOneMulEquiv_def (x : RealProjectiveSpace 1) :
    fundamentalGroupOneMulEquiv x =
      (FundamentalGroup.homeomorphMulEquiv oneHomeomorphCircle x).trans
        ((FundamentalGroup.homeomorphMulEquiv
            (AddCircle.homeomorphCircle (T := 2 * Real.pi) Real.two_pi_pos.ne').symm
            (oneHomeomorphCircle x)).trans
          (AddCircle.fundamentalGroupMulEquiv (2 * Real.pi) Real.two_pi_pos.ne'
            ⟨Classical.choose (QuotientAddGroup.mk_surjective
              ((AddCircle.homeomorphCircle (T := 2 * Real.pi) Real.two_pi_pos.ne').symm
                (oneHomeomorphCircle x))),
             Classical.choose_spec (QuotientAddGroup.mk_surjective _)⟩)) := by
  unfold fundamentalGroupOneMulEquiv
  rfl

/-- The fundamental group of `RP¹` at any basepoint is nontrivial. -/
theorem nontrivial_fundamentalGroup_one (x : RealProjectiveSpace 1) :
    Nontrivial (FundamentalGroup (RealProjectiveSpace 1) x) :=
  (fundamentalGroupOneMulEquiv x).toEquiv.nontrivial

/-- The fundamental group of `RP¹` at any basepoint is infinite. -/
theorem infinite_fundamentalGroup_one (x : RealProjectiveSpace 1) :
    Infinite (FundamentalGroup (RealProjectiveSpace 1) x) :=
  Infinite.of_injective _ (fundamentalGroupOneMulEquiv x).symm.injective

/-- The real projective line is not simply connected. -/
theorem not_simplyConnectedSpace_one : ¬ SimplyConnectedSpace (RealProjectiveSpace 1) :=
  haveI := nontrivial_fundamentalGroup_one oneBasepoint
  not_simplyConnectedSpace_of_nontrivial_fundamentalGroup oneBasepoint

/-- The real projective line is not contractible. -/
theorem not_contractibleSpace_one : ¬ ContractibleSpace (RealProjectiveSpace 1) :=
  not_contractibleSpace_of_not_simplyConnectedSpace not_simplyConnectedSpace_one

end

end RealProjectiveSpace

end TauCeti


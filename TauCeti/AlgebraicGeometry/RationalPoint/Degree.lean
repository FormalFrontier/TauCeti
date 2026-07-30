/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.RationalPoint.Basic
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Degree

/-!
# Divisor degrees at a rational point

`TauCeti.AlgebraicGeometry.RationalPoint.Basic` shows that a section `s` of a morphism of schemes
`f : X ⟶ S` has residue degree one at every point of the base — for `S = Spec k` the statement
`[κ(x₀) : k] = 1` at a `k`-rational point `x₀`. This file draws the consequences for the relative
degree of a Weil divisor, whose weight at a codimension-one point `x` is exactly that residue
degree.

## Main results

* `relativeDegree_ofPoint_of_section`: the prime divisor at a codimension-one point in the image
  of a section has relative degree `1`.
* `relativeDegree_zsmul_ofPoint_of_section`: hence `deg (d · x₀) = d`.
* `relativeDegree_sub_zsmul_ofPoint_of_section`: hence `deg (D - (deg D) · x₀) = 0`, so
  subtracting a multiple of `x₀` normalizes an arbitrary Weil divisor to relative degree zero.

This is the geometric source of the weight-one base point hypothesis that the Layer A degree
theory runs on: the weight of a point of a curve over `k` is its residue degree `[κ(x) : k]`
(`SchemeWeilDivisor.relativeDegree`), and both the class-group splitting
`OrderSystem.classGroupAddEquivPicZeroProdInt` and the Abel-Jacobi class
`OrderSystem.weightedAbelJacobiClass` require a base point of weight one. So this file records
precisely why a `k`-rational point supplies that hypothesis, instead of it having to be assumed.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, "Standing hypotheses" ("A chosen
`k`-rational point `x₀`. ... the `k`-point *rigidifies/normalizes* the Picard functor and supplies
the Abel-Jacobi morphism") and Layer A ("Degree", `Σ_x [κ(x):k]·ord_x`).

No external mathematics is vendored; the proofs reuse `SchemeWeilDivisor.relativeDegree_ofPoint`,
the `AddMonoidHom` structure of `SchemeWeilDivisor.relativeDegree`, and
`residueDegree_eq_one_of_section` from `RationalPoint.Basic`.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

variable {X S : Scheme.{u}} {f : X ⟶ S} {s : S ⟶ X}

/-- A prime divisor whose generic point is a rational point has relative degree one.

This is the geometric origin of the weight-one base point hypothesis of the Layer A degree
theory: the weight of a codimension-one point `x` of a curve over `k` is its residue degree
`[κ(x) : k]`, and at a `k`-rational point that weight is one. -/
theorem relativeDegree_ofPoint_of_section (hs : s ≫ f = 𝟙 S) {y : S}
    {x₀ : CodimensionOnePoint X} (hx₀ : (x₀ : X) = s y) :
    SchemeWeilDivisor.relativeDegree f (WeilDivisor.ofPoint x₀) = 1 := by
  rw [SchemeWeilDivisor.relativeDegree_ofPoint, hx₀, residueDegree_eq_one_of_section hs,
    Nat.cast_one]

/-- A multiple of the prime divisor at a rational point has that multiple as relative degree:
`deg (d · x₀) = d`. -/
theorem relativeDegree_zsmul_ofPoint_of_section (hs : s ≫ f = 𝟙 S) {y : S}
    {x₀ : CodimensionOnePoint X} (hx₀ : (x₀ : X) = s y) (d : ℤ) :
    SchemeWeilDivisor.relativeDegree f (d • WeilDivisor.ofPoint x₀) = d := by
  rw [map_zsmul, relativeDegree_ofPoint_of_section hs hx₀, smul_eq_mul, mul_one]

/-- Correcting a divisor by a multiple of a rational point kills its relative degree:
`deg (D - (deg D) · x₀) = 0`.

Over a base point of relative degree one, every Weil divisor becomes relative degree zero after
subtracting its own degree times that point. Only this equality of relative degrees is proved
here: no map on divisor classes is constructed. -/
theorem relativeDegree_sub_zsmul_ofPoint_of_section (hs : s ≫ f = 𝟙 S) {y : S}
    {x₀ : CodimensionOnePoint X} (hx₀ : (x₀ : X) = s y) (D : SchemeWeilDivisor X) :
    SchemeWeilDivisor.relativeDegree f
        (D - SchemeWeilDivisor.relativeDegree f D • WeilDivisor.ofPoint x₀) = 0 := by
  rw [map_sub, relativeDegree_zsmul_ofPoint_of_section hs hx₀, sub_self]

end AlgebraicGeometry

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.BaseChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Eval

/-!
# Points of a Weierstrass curve from formal-group parameters

Over a complete ring `O` carrying the `I`-adic topology, a parameter `t ∈ I` gives a point of
`W` over any field `K` whose structure map `O → K` is injective: the `w`-expansion converges at
`t`, and the pair
`(t / w(t), -1 / w(t))` satisfies the Weierstrass equation because the `w`-equation *is* that
equation read in the coordinates `x = t / w`, `y = -1 / w`. The parameter `t = 0` gives the point
at infinity.

The two coordinates are recorded in closed form as well. Since `w(t) = t ^ 3 * u(t)` with `u(t)`
a unit, the `x`-coordinate is inverse to `t ^ 2 * u(t)` and the `y`-coordinate to
`-(t ^ 3 * u(t))`. Both are stated as products in `K`, so no inverse of either factor has to be
named; the powers `2` and `3` of `t` they exhibit are what a valuation on `K` would later turn
into pole orders, but no order or valuation hypothesis is assumed here.

## Main definitions

* `WeierstrassCurve.formalPoint`: the point of `W⁄K` attached to a parameter of an adic ideal.

## Main results

* `WeierstrassCurve.formalPoint_equation`: the parametrized pair lies on the curve.
* `WeierstrassCurve.formalPoint_of_param_eq_zero` and
  `WeierstrassCurve.formalPoint_of_param_ne_zero`: the two branches of the definition.
* `WeierstrassCurve.xCoord_formalPoint` and `WeierstrassCurve.yCoord_formalPoint`: the point's
  coordinates, through which the closed forms
  `WeierstrassCurve.xCoord_formalPoint_mul_eq_one` and
  `WeierstrassCurve.yCoord_formalPoint_mul_eq_neg_one` are stated.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, VII.2.

## Provenance

The same parametrization is formalised in Michael Stoll's elliptic-curve development
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0) at `66889eada51a`, file
`EllipticCurves/WeierstrassFormalGroup/Filtration.lean`, declarations `formalPoint_nonsingular`,
`formalPoint`, `formalPoint_of_param_eq_zero` and `formalPoint_of_param_ne_zero`, whose names
this module keeps. That
development states them over `v.adicCompletion K` for a height-one prime of a Dedekind domain
and builds nonsingularity from its own chord lemma; the declarations below are stated over an
arbitrary complete adic ring mapping injectively to a field, and get the point straight from
Mathlib's `Affine.Point.mk`, which carries the equation-to-nonsingularity step itself, so no
nonsingularity lemma is restated here.
-/

public section

open PowerSeries

variable {O : Type*} [CommRing O] [UniformSpace O] [IsUniformAddGroup O] [CompleteSpace O]
  [T2Space O] [IsTopologicalRing O] [IsLinearTopology O O]
  {K : Type*} [Field K] [Algebra O K]

namespace WeierstrassCurve

variable (W : WeierstrassCurve O)

/-- **A formal-group parameter gives a point of the curve**: the pair `(t / w(t), -1 / w(t))`
satisfies the Weierstrass equation over `K`. The hypothesis is `w(t) ≠ 0` rather than `t ≠ 0`,
because that is what the two denominators need; `algebraMap_formalWEval_ne_zero` supplies it
from `t ≠ 0` in the adic setting. -/
theorem formalPoint_equation {t : O} (ht : PowerSeries.HasEval t)
    (hw : algebraMap O K (W.formalWEval t) ≠ 0) : (W.baseChange K).toAffine.Equation
      (algebraMap O K t / algebraMap O K (W.formalWEval t))
      (-(algebraMap O K (W.formalWEval t))⁻¹) := by
  have hkey := congrArg (algebraMap O K) (W.formalWEval_wEquation ht)
  rw [wEquationRHS_def] at hkey
  simp only [map_add, map_mul, map_pow, ← IsScalarTower.algebraMap_apply] at hkey
  rw [WeierstrassCurve.Affine.equation_iff']
  simp only [baseChange, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆]
  field_simp
  linear_combination hkey

variable [W.IsElliptic]

variable [FaithfulSMul O K]

omit [W.IsElliptic] in
/-- `w(t)` is nonzero in `K` at a nonzero parameter of an adic ideal: it factors as
`t ^ 3 * u(t)`, and in `K` both factors are nonzero — `t` because the structure map is
injective, and `u(t)` because a unit maps to a unit. -/
theorem algebraMap_formalWEval_ne_zero {I : Ideal O} (hI : IsAdic I) {t : O} (ht : t ∈ I)
    (ht0 : t ≠ 0) : algebraMap O K (W.formalWEval t) ≠ 0 := by
  have hinj := FaithfulSMul.algebraMap_injective O K
  rw [W.formalWEval_eq_pow_mul_formalUEval (hI.isTopologicallyNilpotent_of_mem ht), map_mul,
    map_pow]
  exact mul_ne_zero (pow_ne_zero _ ((map_ne_zero_iff _ hinj).mpr ht0))
    ((W.isUnit_formalUEval hI ht).map (algebraMap O K)).ne_zero

open scoped Classical in
/-- **The point attached to a formal-group parameter**: a nonzero `t` in an adic ideal gives the
affine point `(t / w(t), -1 / w(t))`, and `t = 0` gives the point at infinity. -/
noncomputable def formalPoint {I : Ideal O} (hI : IsAdic I) {t : O} (ht : t ∈ I) :
    (W.baseChange K).toAffine.Point :=
  if h0 : t = 0 then 0
  else .mk (W.formalPoint_equation (K := K) (hI.isTopologicallyNilpotent_of_mem ht)
    (W.algebraMap_formalWEval_ne_zero hI ht h0))

open scoped Classical in
/-- The parameter `0` gives the point at infinity. -/
@[simp]
theorem formalPoint_of_param_eq_zero {I : Ideal O} (hI : IsAdic I) {t : O} (ht : t ∈ I)
    (h0 : t = 0) :
    W.formalPoint (K := K) hI ht = 0 := by
  simp [formalPoint, h0]

open scoped Classical in
/-- A nonzero parameter gives the affine point, with its coordinates in the form
`formalPoint_equation` states them. -/
@[simp]
theorem formalPoint_of_param_ne_zero {I : Ideal O} (hI : IsAdic I) {t : O} (ht : t ∈ I)
    (h0 : t ≠ 0) :
    W.formalPoint (K := K) hI ht =
      .mk (W.formalPoint_equation (K := K) (hI.isTopologicallyNilpotent_of_mem ht)
        (W.algebraMap_formalWEval_ne_zero hI ht h0)) := by
  simp [formalPoint, h0]

open scoped Classical in
/-- **The `x`-coordinate of the parametrized point** is `t / w(t)`. -/
@[simp]
theorem xCoord_formalPoint {I : Ideal O} (hI : IsAdic I) {t : O} (ht : t ∈ I) (h0 : t ≠ 0) :
    (W.formalPoint (K := K) hI ht).xCoord =
      algebraMap O K t / algebraMap O K (W.formalWEval t) := by
  rw [W.formalPoint_of_param_ne_zero hI ht h0]
  simp [_root_.WeierstrassCurve.Affine.Point.mk]

open scoped Classical in
/-- **The `y`-coordinate of the parametrized point** is `-1 / w(t)`. -/
@[simp]
theorem yCoord_formalPoint {I : Ideal O} (hI : IsAdic I) {t : O} (ht : t ∈ I) (h0 : t ≠ 0) :
    (W.formalPoint (K := K) hI ht).yCoord = -(algebraMap O K (W.formalWEval t))⁻¹ := by
  rw [W.formalPoint_of_param_ne_zero hI ht h0]
  simp [_root_.WeierstrassCurve.Affine.Point.mk]

/-- **The `x`-coordinate in closed form**: since `w(t) = t ^ 3 * u(t)` with `u(t)` a unit, the
`x`-coordinate `t / w(t)` is the inverse of `t ^ 2 * u(t)`. Stated as a product so that it needs
no inverse; the exponent `2` is what a valuation would read as the pole order. -/
theorem xCoord_formalPoint_mul_eq_one {I : Ideal O} (hI : IsAdic I) {t : O} (ht : t ∈ I)
    (ht0 : t ≠ 0) :
    (W.formalPoint (K := K) hI ht).xCoord * algebraMap O K (t ^ 2 * W.formalUEval t) = 1 := by
  rw [W.xCoord_formalPoint hI ht ht0]
  have hinj := FaithfulSMul.algebraMap_injective O K
  have hT : algebraMap O K t ≠ 0 := (map_ne_zero_iff _ hinj).mpr ht0
  have hU : algebraMap O K (W.formalUEval t) ≠ 0 :=
    ((W.isUnit_formalUEval hI ht).map (algebraMap O K)).ne_zero
  rw [W.formalWEval_eq_pow_mul_formalUEval (hI.isTopologicallyNilpotent_of_mem ht)]
  push_cast [map_mul, map_pow]
  field_simp

/-- **The `y`-coordinate in closed form**: `-1 / w(t)` is minus the inverse of `t ^ 3 * u(t)`,
with exponent `3` where the `x`-coordinate has `2`. -/
theorem yCoord_formalPoint_mul_eq_neg_one {I : Ideal O} (hI : IsAdic I) {t : O} (ht : t ∈ I)
    (ht0 : t ≠ 0) :
    (W.formalPoint (K := K) hI ht).yCoord * algebraMap O K (t ^ 3 * W.formalUEval t) = -1 := by
  rw [W.yCoord_formalPoint hI ht ht0]
  have hinj := FaithfulSMul.algebraMap_injective O K
  have hT : algebraMap O K t ≠ 0 := (map_ne_zero_iff _ hinj).mpr ht0
  have hU : algebraMap O K (W.formalUEval t) ≠ 0 :=
    ((W.isUnit_formalUEval hI ht).map (algebraMap O K)).ne_zero
  rw [W.formalWEval_eq_pow_mul_formalUEval (hI.isTopologicallyNilpotent_of_mem ht)]
  push_cast [map_mul, map_pow]
  field_simp

end WeierstrassCurve

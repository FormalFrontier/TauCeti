/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.RatFunc.Degree
public import Mathlib.RingTheory.Localization.NormTrace
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Finrank

/-!
# The norm of a function on a Weierstrass curve

The function field `F(W)` of an affine Weierstrass curve is a quadratic extension of the rational
function field `F(x)` — that is `WeierstrassCurve.Affine.finrank_functionField` — so every
function has an algebra norm `N : F(W) → F(x)`. Mathlib's `Algebra.norm` supplies it, over
`RatFunc F` itself once `RatFunc.liftAlgebra` is in scope. This file computes the degree of that
norm of a function regular away from infinity: it is the degree of the polynomial norm. The
coordinate values that follow from it — `ord_∞ x = -2`, `ord_∞ y = -3` — are proved where the
valuation lives, in `FunctionField/InfinityPlace.lean`.

## Main results

* `WeierstrassCurve.Affine.intDegree_norm_of_mul_eq`: the degree of the norm of `u / d` is the
  degree of the polynomial norm of `u`, less twice that of `d`. Stated for an arbitrary numerator in
  the coordinate ring, so it needs no hypothesis on the basis coefficients.
* `WeierstrassCurve.Affine.intDegree_norm_algebraMap_coordinateRing`: over `RatFunc F`, the
  `intDegree` of the norm of a function regular away from infinity is the degree of its polynomial
  norm.

No new norm is defined, and no lemma restates a generic one: `Algebra.norm` is the norm,
multiplicativity and vanishing exactly at `0` are `map_mul` and `Algebra.norm_eq_zero_iff`, and
the value of the norm on the base ring and on the coordinate ring is `Algebra.norm_algebraMap`
and `Algebra.norm_localization`, applied where they are needed rather than re-exported. What is
new is the transport of that degree to the function field, where `RatFunc.intDegree` lives.

Only the last result forces `RatFunc`: the degree theory of rational functions, `RatFunc.intDegree`
and with it Mathlib's place at infinity `RatFunc.inftyValuation`, is stated for no other fraction
field of `F[X]`.

`RatFunc.liftAlgebra` is a *scoped* instance in Mathlib, because it would create a diamond when the
extension is `RatFunc F` itself; files consuming these results open the `RatFunc` scope as this one
does. The repository's own `algebraFractionRingFunctionField` is the same construction for
`FractionRing F[X]`, exported there because that diamond cannot arise for a quadratic extension.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, **Layer 0** (the function field, places, and divisors).
The layer asks for the place at infinity, "where `x` and `y` have their poles", with `ord_∞ x = -2`,
`ord_∞ y = -3` and residue field `K`. That place is this norm followed by Mathlib's place at
infinity of `F(x)`: `ord_∞ f = -deg N(f)`. This file supplies the general degree transport that
`ord_∞` is computed from; the valuation itself and the two coordinate values are proved in
`FunctionField/InfinityPlace.lean`. No order at infinity is defined or claimed here. Layer 0
seeds no declaration this competes with — `Suggested.lean` records that the function-field
layer's "types are new API and are built there, not pinned here".

## Provenance

The route is that of the AINTLIB `HasseWeil` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0,
`dev/hasse-weil` at `a582951fe96b`), `HasseWeil/Curves/Infinity.lean`, declarations `normAsRatFunc`
and `normAsRatFunc_mul`, together with `Curves/NormValuation.lean`.

Changes from the source. There the norm is a definition of its own — `normAsRatFunc`, built from
that development's `fieldNorm` over a `SmoothPlaneCurve` structure wrapping
`WeierstrassCurve.Affine`, with multiplicativity and vanishing proved by hand. Here there is no new
definition and no wrapper: the norm is Mathlib's over `RatFunc F`, so those three lemmas are
Mathlib's, and the coordinate-ring computation is `Algebra.norm_localization` rather than a hand
proof.
-/

public section

open Polynomial WeierstrassCurve

open scoped Polynomial.Bivariate

open scoped RatFunc

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] (W : _root_.WeierstrassCurve.Affine F)

/-- **The degree of the norm of a function regular away from infinity**, as a rational function, is
the degree of its polynomial norm. This is what the order at infinity is computed from, and it is
where `RatFunc F` is forced: `intDegree` is stated for no other fraction field of `F[X]`. -/
@[simp]
theorem intDegree_norm_algebraMap_coordinateRing (u : W.CoordinateRing) :
    (Algebra.norm (RatFunc F) (algebraMap W.CoordinateRing W.FunctionField u)).intDegree =
      (Algebra.norm F[X] u).natDegree := by
  rw [Algebra.norm_localization (R := F[X]) (M := nonZeroDivisors F[X]) (S := W.CoordinateRing),
    RatFunc.intDegree_polynomial]

private theorem norm_algebraMap_polynomial' (d : F[X]) :
    Algebra.norm (RatFunc F) (algebraMap F[X] W.FunctionField d) =
      (algebraMap F[X] (RatFunc F) d) ^ 2 := by
  rw [IsScalarTower.algebraMap_apply F[X] (RatFunc F) W.FunctionField, Algebra.norm_algebraMap,
    finrank_functionField W (RatFunc F)]

/-- **The degree of the norm of `u / d`**: the polynomial norm's degree, less twice that of the
denominator. Stated for an arbitrary numerator `u` in the coordinate ring, so it carries no
hypothesis on the basis coefficients — they may vanish. -/
theorem intDegree_norm_of_mul_eq {f : W.FunctionField} (hf : f ≠ 0) {u : W.CoordinateRing}
    {d : F[X]} (hd : d ≠ 0)
    (h : f * algebraMap F[X] W.FunctionField d = algebraMap W.CoordinateRing W.FunctionField u) :
    (Algebra.norm (RatFunc F) f).intDegree
      = (Algebra.norm F[X] u).natDegree - 2 * d.natDegree := by
  have hNf : Algebra.norm (RatFunc F) f ≠ 0 :=
    fun hz => hf ((Algebra.norm_eq_zero_iff (R := RatFunc F)).mp hz)
  have hdR : algebraMap F[X] (RatFunc F) d ≠ 0 := RatFunc.algebraMap_ne_zero hd
  have hnorm := congrArg (Algebra.norm (RatFunc F)) h
  rw [map_mul, norm_algebraMap_polynomial',
    Algebra.norm_localization (R := F[X]) (M := nonZeroDivisors F[X])
      (S := W.CoordinateRing)] at hnorm
  have := congrArg RatFunc.intDegree hnorm
  rw [RatFunc.intDegree_mul hNf (pow_ne_zero _ hdR), ← map_pow,
    RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial, natDegree_pow] at this
  omega

end WeierstrassCurve.Affine

end

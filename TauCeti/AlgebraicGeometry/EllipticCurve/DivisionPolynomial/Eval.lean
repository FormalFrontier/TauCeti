/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Eval

/-!
# Evaluating the division polynomials at a point of a Weierstrass curve

Mathlib relates the bivariate division polynomials `ψₙ`, `Ψₙ`, `φₙ` to their univariate companions
`ΨSqₙ`, `Φₙ` only inside the coordinate ring `R[W]`, as the identities
`Affine.CoordinateRing.mk_ψ`, `mk_Ψ_sq` and `mk_φ`. This file transports those identities to
honest equalities of ring elements at a point `(x, y)` **on** the curve, where evaluation
`Polynomial.evalEval x y` factors through `R[W]` by Mathlib's `AdjoinRoot.evalEval`.

The point of doing so is that `ΨSqₙ` and `Φₙ` are univariate: on the curve, `evalEval x y (ψ n)`
and `evalEval x y (Ψ n)` agree, and the square of the latter is a polynomial in `x` alone. That is
what later lets a rational-root argument run — not here, where `R` is an arbitrary commutative ring
and the theorem's coefficient hypotheses are not available, but downstream over a unique
factorization domain, where the degrees are Mathlib's `natDegree_Φ` (`n²`, over a nontrivial ring)
and `natDegree_ΨSq` (`n² - 1`, needing no zero divisors and `(n : R) ≠ 0`; in characteristic
dividing `n` the degree can drop). The identities below need none of those hypotheses.

## Main results

* `TauCeti.WeierstrassCurve.evalEval_ψ_eq_evalEval_Ψ`, `evalEval_Ψ_sq_eq_eval_ΨSq`,
  `evalEval_φ_eq_eval_Φ`: the three coordinate-ring identities, evaluated.
* `TauCeti.WeierstrassCurve.evalEval_Ψ_odd`: for odd `n`, `Ψₙ` evaluates to `(preΨ n).eval x`,
  with no `y` left. Composed with the first bullet, `simp` reduces `ψₙ` the same way.

Everything is stated over an arbitrary commutative ring; no domain, field or ellipticity hypothesis
is needed, because a coordinate-ring identity evaluates wherever the Weierstrass equation holds.

This is a prerequisite of the Nagell–Lutz integrality milestone of
`TauCetiRoadmap/EllipticCurves/README.md`, Layer 6, item "The torsion subgroup and Nagell–Lutz",
whose route the roadmap records as "division polynomials".

## Provenance

Ported from the AINTLIB `NagellLutz` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0), pinned by
that roadmap at `dev/modular-curves @ 9fec8eba7652`:
`LutzNagell/LutzNagellTheorem/EvalBridge.lean`. That project runs against its own vendored copy of
Mathlib's division polynomials; here the statements are rebased onto pinned Mathlib's
`WeierstrassCurve.{ψ, Ψ, ΨSq, φ, Φ, preΨ}` and generalised from a field to a commutative ring.
-/

public section

open Polynomial WeierstrassCurve

open scoped Polynomial.Bivariate

namespace TauCeti

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : _root_.WeierstrassCurve R) {x y : R}

/-- The division polynomials `ψₙ` and `Ψₙ` evaluate equally at a point of `W`. -/
@[simp]
theorem evalEval_ψ_eq_evalEval_Ψ (h : W.toAffine.Equation x y) (n : ℤ) :
    (W.ψ n).evalEval x y = (W.Ψ n).evalEval x y :=
  evalEval_eq_of_mk_eq W.toAffine h (Affine.CoordinateRing.mk_ψ W n)

/-- At a point of `W`, the square of `Ψₙ` is the univariate `ΨSqₙ` evaluated at the
`x`-coordinate. -/
@[simp]
theorem evalEval_Ψ_sq_eq_eval_ΨSq (h : W.toAffine.Equation x y) (n : ℤ) :
    (W.Ψ n).evalEval x y ^ 2 = (W.ΨSq n).eval x := by
  simpa [evalEval_pow, evalEval_C] using
    evalEval_eq_of_mk_eq W.toAffine h (Affine.CoordinateRing.mk_Ψ_sq W n)

/-- At a point of `W`, `φₙ` is the univariate `Φₙ` evaluated at the `x`-coordinate. -/
@[simp]
theorem evalEval_φ_eq_eval_Φ (h : W.toAffine.Equation x y) (n : ℤ) :
    (W.φ n).evalEval x y = (W.Φ n).eval x := by
  simpa [evalEval_C] using evalEval_eq_of_mk_eq W.toAffine h (Affine.CoordinateRing.mk_φ W n)

/-- For odd `n` the polynomial `Ψₙ` carries no `y`, so it evaluates to `(preΨ n).eval x` at any
point. This one needs no curve hypothesis. -/
@[simp]
theorem evalEval_Ψ_odd (n : ℤ) (hodd : ¬Even n) :
    (W.Ψ n).evalEval x y = (W.preΨ n).eval x := by
  rw [_root_.WeierstrassCurve.Ψ, ite_eq_right hodd, mul_one, evalEval_C]

end WeierstrassCurve

end TauCeti

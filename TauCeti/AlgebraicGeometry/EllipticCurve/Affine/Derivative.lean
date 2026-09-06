/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
-- Proof-only: `Δ ≠ 0` forces `a₁ ≠ 0 ∨ a₃ ≠ 0` where `2 = 0`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Weierstrass

/-!
# The Weierstrass partial derivatives are derivatives

Mathlib defines the two partial derivatives `WeierstrassCurve.Affine.polynomialX` and
`WeierstrassCurve.Affine.polynomialY` of the Weierstrass polynomial `W(X, Y)` by explicit
formulae, and marks both definitions with the comment
`TODO: define this in terms of Polynomial.derivative`. This file identifies each of them with the
derivative it is named after.

## Main statements

* `WeierstrassCurve.Affine.derivative_polynomial`: `W_Y` is `Polynomial.derivative W(X, Y)`, an
  identity of bivariate polynomials. No evaluation is involved: `R[X][Y]` is a polynomial ring in
  `Y` over `R[X]`, so `Polynomial.derivative` already differentiates in `Y`.
* `WeierstrassCurve.Affine.equivPolynomial_mapCoeffs_polynomial`: `W_X` is the coefficientwise
  derivative of `W(X, Y)`, again an identity of bivariate polynomials with no evaluation involved.
* `WeierstrassCurve.Affine.derivative_eval_polynomial`: the chain rule along a substitution
  `Y := p`, which expresses `derivative (W(X, p))` through *both* partials. For a constant
  `p = C y` the `Y`-term drops out and this reads `W_X(X, y)`.
* `WeierstrassCurve.Affine.polynomialY_ne_zero`: `W_Y` is a nonzero polynomial once `Δ ≠ 0`. This
  is what makes the Weierstrass equation separable in `Y`, and so the function field a separable
  extension of the rational functions in `x`; in characteristic two the leading term of `W_Y`
  vanishes and the discriminant is what rules out `a₁ = a₃ = 0`.

The first three hold over an arbitrary commutative ring; the fourth adds `Δ ≠ 0`.

## Implementation notes

`Polynomial.derivative` on `R[X][Y]` differentiates in `Y`, so `derivative_polynomial` is an
identity of bivariate polynomials with no evaluation anywhere. Differentiating in `X` instead means
differentiating the coefficients, which `Derivation.mapCoeffs` does; reading the result back in
`R[X][Y]` along `PolynomialModule.equivPolynomial` gives the shape standing on the right of
`Polynomial.Bivariate.pderiv_zero_equivMvPolynomial`, so no `MvPolynomial` transport is needed to
state that partial either.

Each partial is therefore stated bare and one at a time, and the chain rule is *derived* from the
two rather than taken as primitive: `derivative_eval_polynomial` follows from
`equivPolynomial_mapCoeffs_polynomial` and `derivative_polynomial` through
`Derivation.apply_eval_eq`. The substituted form remains the one most consumers meet, so it is
kept, but it is now a corollary of the bare identities rather than the only statement of them.

## Provenance

Two of the three identities come from the proof of
`WeierstrassCurve.Affine.Point.nonsingular_of_isUnit_XYIdeal` in `Affine/Point/ToClass.lean`,
which is itself ported from the AINTLIB `HasseWeil` project
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0, by Chris Birkbeck), where they were local `have`s
over a field, stated after evaluating at a point.

They are restated here to different degrees, and only one of them is a straight extraction.
`derivative_polynomial` is the identity the `have` already had, moved ahead of the evaluation and
over a commutative ring. `derivative_eval_polynomial` goes beyond its `have`: that one covered
only the constant substitution `p = C y`, for which the `Y`-term drops out, so the chain rule for
an arbitrary `p : R[X]` is a generalisation of it rather than an extraction of it. The constant
case is what the call site in `ToClass.lean` recovers.

`equivPolynomial_mapCoeffs_polynomial` has no counterpart in the source: the `have`s worked
with the substituted form throughout, and the bare `X`-partial is stated here for the first time.
-/

public section

open Polynomial

namespace WeierstrassCurve.Affine

variable {R : Type*} [CommRing R] {W : Affine R}

/-- **The `Y`-partial derivative of `W(X, Y)` is a `Polynomial.derivative`.** Viewing `R[X][Y]` as
a polynomial ring in `Y` over `R[X]`, differentiating `W(X, Y)` in `Y` gives `W_Y(X, Y)` on the
nose. -/
@[simp] theorem derivative_polynomial : derivative W.polynomial = W.polynomialY := by
  simp only [polynomial, polynomialY, derivative_sub, derivative_add, derivative_mul,
    derivative_C, derivative_X_pow, derivative_X, C_ofNat, Nat.cast_ofNat, zero_mul, zero_add,
    sub_zero, mul_one, pow_one, Nat.add_one_sub_one]

/-- **The `X`-partial derivative of `W(X, Y)` is a coefficientwise derivative.** Differentiating
`W(X, Y)` in `X` means differentiating its coefficients, which `Derivation.mapCoeffs` does; reading
the result back in `R[X][Y]` gives `W_X(X, Y)` on the nose. -/
@[simp] theorem equivPolynomial_mapCoeffs_polynomial :
    PolynomialModule.equivPolynomial (derivative'.mapCoeffs W.polynomial) = W.polynomialX := by
  rw [← PolynomialModule.equivPolynomialSelf_apply_eq]
  have h : PolynomialModule.equivPolynomialSelf (PolynomialModule.single R[X] 0 1) = 1 := by simp
  simp [polynomial, polynomialX, map_sub, map_add, Derivation.leibniz,
    -PolynomialModule.equivPolynomialSelf_apply_eq, map_smul, smul_eq_mul, C_ofNat, h]
  ring

/-- **The chain rule for `W(X, Y)` along a substitution `Y := p`.** Differentiating the
one-variable polynomial `W(X, p)` splits into the two partials of `W`, the `Y`-one weighted by
`p'`. Substituting a constant `p = C y` kills the second term and leaves `W_X(X, y)`. -/
@[simp] theorem derivative_eval_polynomial (p : R[X]) :
    derivative (W.polynomial.eval p) =
      W.polynomialX.eval p + W.polynomialY.eval p * derivative p := by
  -- Evaluating a `PolynomialModule R[X] R[X]` agrees with evaluating the polynomial it names.
  have hbridge : ∀ m : PolynomialModule R[X] R[X],
      PolynomialModule.eval p m = eval p (PolynomialModule.equivPolynomial m) := by
    intro m
    induction m using PolynomialModule.induction_linear <;> simp_all [mul_comm]
  have h := Derivation.apply_eval_eq (derivative' (R := R)) p W.polynomial
  rw [hbridge, equivPolynomial_mapCoeffs_polynomial, derivative_polynomial] at h
  simpa using h

/-- The partial derivative `W_Y = 2Y + a₁X + a₃` of the Weierstrass polynomial is a nonzero
polynomial whenever the discriminant is nonzero. In characteristic two the first term vanishes,
and it is `Δ ≠ 0` that rules out `a₁ = a₃ = 0`. -/
theorem polynomialY_ne_zero (hΔ : W.Δ ≠ 0) : W.polynomialY ≠ 0 := by
  intro h
  rw [WeierstrassCurve.Affine.polynomialY] at h
  have h1 := congr_arg (fun p => p.coeff 1) h
  have h0 := congr_arg (fun p => p.coeff 0) h
  simp only [map_add, map_mul, coeff_add, coeff_mul_X, coeff_C, ↓reduceIte, coeff_mul_C,
    zero_mul, add_zero, coeff_zero, Polynomial.C_eq_zero, mul_coeff_zero, coeff_X, one_ne_zero,
    mul_zero, zero_add] at h1 h0
  have ha1 : W.a₁ = 0 := by
    have := congr_arg (fun p => p.coeff 1) h0
    simp only [coeff_add, coeff_mul_X, coeff_C_zero, coeff_C_succ, add_zero, coeff_zero] at this
    exact this
  have ha3 : W.a₃ = 0 := by
    have := congr_arg (fun p => p.coeff 0) h0
    simp only [coeff_add, mul_coeff_zero, coeff_C_zero, coeff_X_zero, mul_zero, zero_add,
      coeff_zero] at this
    exact this
  -- `2 = 0` and `a₁ = a₃ = 0` together contradict `Δ ≠ 0`.
  exact (WeierstrassCurve.a₁_ne_zero_or_a₃_ne_zero_of_Δ_ne_zero_of_two_eq_zero W hΔ h1).elim
    (fun h => h ha1) fun h => h ha3

end WeierstrassCurve.Affine

end

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import TauCeti.NumberTheory.EllipticDivisibilitySequence.Invariant

/-!
# The invariant polynomial of a Weierstrass curve

This file defines the polynomial

`WeierstrassCurve.invar = 6 X² + b₂ X + b₄`

and proves the division-polynomial identities that pin it down, together with the one identity
connecting `φ` and `ψ` to `IsEllipticNet.invarDenom`. They are the first stage of the `ω` family of
division polynomials, which gives the `Y` coordinate of scalar multiplication in Jacobian
coordinates.

Throughout, `ψ` is Mathlib's division-polynomial sequence `WeierstrassCurve.ψ`, and nothing here
uses or asserts that it is an elliptic net or an elliptic sequence. `IsEllipticNet.invarNum` and
`IsEllipticNet.invarDenom` are defined for an **arbitrary** sequence — `invarDenom W s n` is
`W (n + s) * W n * W (n - s)` — so applying `invarDenom` to `ψ` is the use of a formula, not an
ellipticity hypothesis; the namespace is where those formulas live, not a claim about `ψ`.

The name `invar` records where the polynomial comes from, and that origin is motivation rather than
anything established below: for a sequence that *is* an elliptic net, and over a field where the
relevant denominators are nonzero, `invarNum/invarDenom` is independent of the index — that is the
cancellation of `IsEllipticNet.invarNum_mul_invarDenom` — and its value modulo the Weierstrass
polynomial is `6 X² + b₂ X + b₄`. Neither the hypothesis nor that conclusion is proved here, and
over a `CommRing` the quotient need not exist at all. What this file proves are the polynomial
identities listed below.

## Main definitions

* `WeierstrassCurve.invar`: the invariant polynomial `6 X² + b₂ X + b₄`.

## Main results

* `WeierstrassCurve.preΨ₄_add_Ψ₂Sq_sq`: `preΨ₄ + Ψ₂Sq ^ 2 = invar * Ψ₃`, the identity that pins
  `invar` down. Its certificate is the `b`-relation `4 b₈ = b₂ b₆ - b₄ ²`.
* `WeierstrassCurve.preΨ₄_add_ψ₂_pow_four`: the same identity in the bivariate ring, where it
  acquires a multiple of the Weierstrass polynomial.
* `WeierstrassCurve.C_Ψ₃`: `Ψ₃` through the partial derivatives of the Weierstrass polynomial.
* `WeierstrassCurve.Affine.CoordinateRing.mk_preΨ₄_add_ψ₂_pow_four`: the bivariate identity
  in the coordinate ring, where the multiple of the Weierstrass polynomial vanishes; with
  `WeierstrassCurve.map_invar` and `baseChange_invar`, the naturality the surrounding
  division-polynomial API provides for its other objects.
* `WeierstrassCurve.φ_mul_ψ`: `φ n * ψ n = X ψ(n)³ - invarDenom ψ 1 n`, which is what connects the
  division polynomials to the invariant denominator formula evaluated at `ψ`.

## What is deliberately not here

`WeierstrassCurve.ω` itself and its API — `ω_spec`, `two_mul_ω`, `ψc`, `ψc_spec`, `ω_zero`,
`ω_one`, `ψc_neg`, `map_ω`, `ω_neg` — are **not** in this file. `ω` is defined through
`redInvarDenom` and `complEDS₂Aux`, and `ω_spec` additionally consumes `redInvar_normEDS`, which
routes through `normEDS` being an elliptic sequence — that is `isEllipticSequence_normEDS` in
`NormEDS.lean`, which the pinned Mathlib still records as an open TODO. What is missing for `ω`
is `redInvarDenom` itself together with the upper part of the chain
`redInvar_normEDS ← invar₂_normEDS ← invar_normEDS ← net_normEDS`, which is written in the
source's names. The lower two links have landed: `net_normEDS` is `isEllipticNet_normEDS` and
`invar_normEDS` is `invarNum_mul_invarDenom`. What remains is `invar₂_normEDS` and
`redInvar_normEDS`. Nothing in this file depends on any of it, so the identities land now and `ω`
follows when that gap closes.

## Provenance

Ported from J. Xu and D. K. Angdinata's `LutzNagell/DivisionPolynomialOmega.lean` in AINTLIB
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0, `main` at
`1c1c74664e40071c2c2165bc55ca2616a67ccd6b`), declarations `invar`, `C_Ψ₃_eq` (here `C_Ψ₃`,
matching Mathlib's `C_Ψ₂Sq`), `preΨ₄_add_Ψ₂Sq_sq`, `preΨ₄_add_ψ₂_pow_four` and `φ_mul_ψ`. That
file's header reads
`Authors: Junyan Xu, David Kurniadi Angdinata`; following this repository's convention for adapted
material the upstream authorship is credited here rather than in the copyright header.

Two adaptations, neither of them a choice:

* the source proves `φ_mul_ψ` by `rw [φ, invarDenom]`, unfolding both definitions. The
  `invarDenom` half does not port: `EllipticDivisibilitySequence/Invariant.lean` exports that body
  unexposed, so from this module `rw [invarDenom]` has nothing to rewrite with. It goes through the
  equation lemma `IsEllipticNet.invarDenom_def` instead. `φ` unfolds as before, being Mathlib's.
* the source's local `C_simp` macro is written out at its three use sites rather than carried
  across, a macro being more surface than the one `simp only` call it abbreviates.

The statement of `φ_mul_ψ` was checked against Mathlib's `φ` rather than assumed: Mathlib defines
`φ n = C X * ψ n ^ 2 - ψ (n + 1) * ψ (n - 1)`, so `φ n * ψ n` is
`C X * ψ n ^ 3 - ψ (n + 1) * ψ n * ψ (n - 1)`, and that subtrahend is exactly
`IsEllipticNet.invarDenom ψ 1 n`.
-/

public section

open Polynomial

open scoped Polynomial.Bivariate

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The polynomial `6 X² + b₂ X + b₄` of a Weierstrass curve. What ties it to the division
polynomials is `preΨ₄_add_Ψ₂Sq_sq` below, `preΨ₄ + Ψ₂Sq ^ 2 = invar * Ψ₃`. The name records the
classical invariant of an elliptic net, whose index-independence is not what is proved here; see
the module docstring. -/
noncomputable def invar : R[X] := 6 * X ^ 2 + C W.b₂ * X + C W.b₄

/-- The defining formula for `invar`. The definition body is not exposed, so this equation lemma is
how a consumer computes with it. Not `@[simp]`: the point of naming the polynomial is that
`preΨ₄_add_Ψ₂Sq_sq` can be stated over it, which unfolding everywhere would defeat. -/
theorem invar_def : W.invar = 6 * X ^ 2 + C W.b₂ * X + C W.b₄ := (rfl)

/-- `Ψ₃` expressed through the partial derivatives of the Weierstrass polynomial. -/
theorem C_Ψ₃ :
    C W.Ψ₃ = (3 * C X + CC W.a₂) * C W.Ψ₂Sq - Affine.polynomialX W ^ 2
      + CC W.a₁ * W.ψ₂ * Affine.polynomialX W - CC W.a₁ ^ 2 * Affine.polynomial W := by
  simp_rw [Ψ₃, Ψ₂Sq, Affine.polynomial, Affine.polynomialX, ψ₂, Affine.polynomialY, b₂, b₄, b₆, b₈,
    CC]
  simp only [map_ofNat, C_add, C_sub, C_mul, C_pow]
  ring

/-- **The identity that pins `invar` down**: `preΨ₄ + Ψ₂Sq ^ 2 = invar * Ψ₃`. The certificate is
the `b`-relation `4 * b₈ = b₂ * b₆ - b₄ ^ 2`. -/
theorem preΨ₄_add_Ψ₂Sq_sq : W.preΨ₄ + W.Ψ₂Sq ^ 2 = W.invar * W.Ψ₃ := by
  rw [preΨ₄, Ψ₂Sq, invar, Ψ₃]
  linear_combination (norm := (simp only [map_ofNat, C_sub, C_mul, C_pow]; ring_nf))
    congr(C $W.b_relation) * (@X R _) ^ 2

/-- The bivariate form of `preΨ₄_add_Ψ₂Sq_sq`. Passing to `R[X][Y]` costs a multiple of the
Weierstrass polynomial: `ψ₂ ^ 2` and `C Ψ₂Sq` differ by `4 * Affine.polynomial W`, and the
factor `8` here comes from expanding the square of that difference. -/
theorem preΨ₄_add_ψ₂_pow_four : C W.preΨ₄ + W.ψ₂ ^ 4 =
    C (W.invar * W.Ψ₃) + 8 * Affine.polynomial W * (2 * Affine.polynomial W + C W.Ψ₂Sq) := by
  -- reassociate the fourth power to expose the `ψ₂ ^ 2` subterm that `ψ₂_sq` rewrites
  simp_rw [show 4 = 2 * 2 by rfl, pow_mul, ψ₂_sq, add_sq, ← add_assoc, ← C_pow, ← C_add,
    preΨ₄_add_Ψ₂Sq_sq]
  simp only [C_mul]
  ring

/-- The bivariate identity in the coordinate ring, where the multiple of the Weierstrass
polynomial vanishes: consumers working modulo the curve equation read the identity in this
form. -/
lemma Affine.CoordinateRing.mk_preΨ₄_add_ψ₂_pow_four :
    Affine.CoordinateRing.mk W (C W.preΨ₄ + W.ψ₂ ^ 4) =
      Affine.CoordinateRing.mk W (C (W.invar * W.Ψ₃)) := by
  rw [preΨ₄_add_ψ₂_pow_four]
  simp

/-- **The division polynomials meet the invariant denominator**: `φ n * ψ n` is `X ψ(n)³` less
`IsEllipticNet.invarDenom ψ 1 n`, which is `ψ(n+1) ψ(n) ψ(n-1)`. That denominator is a formula in an
arbitrary sequence, so this is an identity between division polynomials and uses no ellipticity of
`ψ`. It is the step through which the elliptic-net formulas reach the curve. -/
theorem φ_mul_ψ (n : ℤ) :
    W.φ n * W.ψ n = C X * W.ψ n ^ 3 - IsEllipticNet.invarDenom W.ψ 1 n := by
  rw [WeierstrassCurve.φ, IsEllipticNet.invarDenom_def]
  ring

section BaseChange

variable {S : Type*} [CommRing S] (f : R →+* S)

/-- `invar` commutes with mapping the coefficients along a ring homomorphism. -/
@[simp]
lemma map_invar : (W.map f).invar = W.invar.map f := by
  simp [invar]

variable [Algebra R S] {A : Type*} [CommRing A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
  {B : Type*} [CommRing B] [Algebra R B] [Algebra S B] [IsScalarTower R S B] (g : A →ₐ[S] B)

/-- `invar` commutes with base change along an algebra homomorphism between extensions. -/
lemma baseChange_invar : (W⁄B).invar = (W⁄A).invar.map g := by
  rw [← map_invar, map_baseChange]

end BaseChange

end WeierstrassCurve

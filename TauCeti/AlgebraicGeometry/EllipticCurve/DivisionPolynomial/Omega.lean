/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Invariant
public import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.NormEDS
public import TauCeti.AlgebraicGeometry.EllipticCurve.Universal
public import TauCeti.NumberTheory.EllipticDivisibilitySequence.ReducedInvariant

/-!
# The omega family of division polynomials

`ω n` is the bivariate polynomial that the scalar-multiplication development identifies as the
second (Jacobian) coordinate of multiplication by `n` on a Weierstrass curve — that
identification belongs there, not here, and is not yet in the library. This file supplies the
polynomial itself, completing the `(φ, ψ)` pair of Mathlib's division-polynomial API: it defines
`ω` and the 2-complement `ψc` of `ψ`, and proves the defining identity

`2 ω n + a₁ φ n ψ n + a₃ (ψ n)³ = ψc n`,

which pins down `2 ω n` in general and `ω` itself wherever `2` is a nonzerodivisor — the
equation lemma `ω_def` is the unconditional handle. Alongside: the value lemmas `ω_zero` and
`ω_one`, the parity rules `ω_neg` and `ψc_neg`, the complement identity `ψ n * ψc n = ψ (2n)`,
and naturality in the coefficient ring for both families.

## Main definitions

* `WeierstrassCurve.ψc`: the complement of `ψ n` in `ψ (2n)`.
* `WeierstrassCurve.ω`: the `ω` family of division polynomials.

## Main results

* `WeierstrassCurve.ω_spec`: `2 ω n + a₁ φ n ψ n + a₃ (ψ n)³ = ψc n`.
* `WeierstrassCurve.ω_def`: the defining formula, as an equation lemma — the unexposed body's
  handle for consumers, and the only one that determines `ω` where `2` is a zero divisor.
* `WeierstrassCurve.ψ_mul_ψc`: `ψ n * ψc n = ψ (2n)`.
* `WeierstrassCurve.ω_neg`: `ω (-n) = ω n + a₁ φ n ψ n + a₃ (ψ n)³`, proved over the
  universal curve — where `2` is a nonzerodivisor — and specialised.
* `WeierstrassCurve.map_ψc`, `.map_ω`, `.baseChange_ψc`, `.baseChange_ω`: naturality in the
  coefficient ring, in both the ring-hom and the algebra-tower form of the `ψ`/`φ` siblings.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], Exercise 3.7, which defines
  the `(ψ, φ, ω)` triple for a general Weierstrass equation
  `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆` (the short form is offered there only as an optional
  simplification), and whose part (d), `[m]P = (φₘ/ψₘ², ωₘ/ψₘ³)`, is what makes `ω` a
  `Y`-coordinate numerator and fixes the normalisation of `ω` taken here. Part (d) has no Lean
  statement anywhere in this library yet: `DivisionPolynomial/ZSMul.lean` defines `smulY n` as
  `ωₙ/ψₙ³`, but identifying that rational function with the `Y`-coordinate of `n • P` remains to
  be proved.

  The exercise's own recurrence fixes a different normalisation, and the two part company off the
  short form. Its printed `4y ωₘ = ψₘ₋₁² ψₘ₊₂ + ψₘ₋₂ ψₘ₊₁²` is corrected by Silverman's errata
  (the entry `Pages 105-106, Exercise 3.7` of
  `math.brown.edu/johsilve/AEC/AECErrata2013.pdf`) to
  `2 (2y + a₁x + a₃) ωₘ = ψₘ₋₁² ψₘ₊₂ - ψₘ₋₂ ψₘ₊₁²`; as `ψ_mul_ψc` reads that right-hand side as
  `ψ₂ ψcₘ`, and `ψ₂ = 2y + a₁x + a₃`, the corrected recurrence says `2 ωₘ = ψcₘ`, so `ω₁` is
  `(2y + a₁x + a₃)/2`. Part (d) instead forces `ω₁ = y`, which is what `ω_one` records; the two
  normalisations agree exactly when `a₁ = a₃ = 0`. `ω_spec` below is the part-(d) one, its extra
  `a₁ φₘ ψₘ + a₃ ψₘ³` being precisely that discrepancy.

## Provenance

Ported from J. Xu and D. K. Angdinata's `LutzNagell/DivisionPolynomialOmega.lean` in AINTLIB
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0, `main` at
`1c1c74664e40071c2c2165bc55ca2616a67ccd6b`), declarations `ψc`, `ω`, `ω_spec`, `two_mul_ω`,
`ψc_spec` (here `ψ_mul_ψc`, naming its left-hand side), `ω_zero`, `ω_one`, `ψc_neg`,
`map_ω`, `universal_ω_neg` and `ω_neg`. That file's header reads
`Authors: Junyan Xu, David Kurniadi Angdinata`; following this repository's convention for
adapted material the upstream authorship is credited here rather than in the copyright
header. The invariant-polynomial half of that source file is already in
`DivisionPolynomial/Invariant.lean`; this file is the `ω` half, unblocked by
`reducedInvarNum_eq_reducedInvarDenom_mul` (`ReducedInvariant.lean`), the port of the
source's `redInvar_normEDS`. Its `isEllSequence_ψ` is ported separately, in
`DivisionPolynomial/NormEDS.lean`, which needs none of the reduced-invariant theory.

The specification realised here and the well-definedness argument behind `ω_neg` are both
stated in the module docstring of pinned Mathlib's
`Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean` (D. K. Angdinata):
`ωₙ := (ψ₂ₙ / ψₙ - ψₙ(a₁φₙ + a₃ψₙ²)) / 2`, with `2` dividing that difference in the
characteristic-zero universal ring and `ωₙ` its image under the universal morphism. This file
discharges that docstring's `TODO: the bivariate polynomials ωₙ`. The remaining declarations
with no source counterpart are the equation lemmas `ψc_def` and `ω_def` (the module system
keeps both bodies unexposed, so each needs a named handle), the value lemmas `ψc_zero`,
`ψc_one` and `ψc_two` (the `complEDS₂` values read at the curve's parameters), `map_ψc`, and
the two `baseChange_*` forms, which follow Mathlib's sibling `baseChange_ψ`/`baseChange_φ`.
-/

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve

variable {R : Type*} {S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R)

public section

noncomputable section

open Affine (polynomial polynomialX polynomialY negPolynomial)

/-- The complement of `ψ n` in `ψ (2n)`: the parameter-level `complEDS₂` at the curve's
division-polynomial parameters. `ψ_mul_ψc` below is the identity it is named for. -/
protected def ψc : ℤ → R[X][Y] := complEDS₂ W.ψ₂ (C W.Ψ₃) (C W.preΨ₄)

/-- The defining formula for `ψc`, at the level of functions. The definition body is not
exposed, so this equation lemma is how a consumer in another module computes with it. -/
theorem ψc_def : W.ψc = complEDS₂ W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) := (rfl)

/-- `ψc` at `0` is `2`. -/
@[simp] theorem ψc_zero : W.ψc 0 = 2 := by rw [ψc_def, complEDS₂_zero]

/-- `ψc` at `1` is `ψ₂`, matching `ψ 1 * ψc 1 = ψ 2`. -/
@[simp] theorem ψc_one : W.ψc 1 = W.ψ₂ := by rw [ψc_def, complEDS₂_one]

/-- `ψc` at `2` is `preΨ₄`, matching `ψ 2 * ψc 2 = ψ 4`. -/
@[simp] theorem ψc_two : W.ψc 2 = C W.preΨ₄ := by rw [ψc_def, complEDS₂_two]

/-- The `ω` family of division polynomials: `ω n` gives the second coordinate in Jacobian
coordinates of scalar multiplication by `n`. -/
protected def ω (n : ℤ) : R[X][Y] :=
  reducedInvarDenom W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n *
    ((CC W.a₁ * polynomialY W - polynomialX W) * C W.Ψ₃
      + 4 * polynomial W * (2 * polynomial W + C W.Ψ₂Sq))
  - complEDS₂Aux W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n + negPolynomial W * W.ψ n ^ 3

/-- The defining formula for `ω`. The definition body is not exposed, so this equation lemma is
how a consumer in another module computes with it: `ω_spec` fixes only `2 * W.ω n`, which
determines nothing where `2` is a zero divisor. Deliberately not `@[simp]`, for `ψc_def`'s
reason. -/
theorem ω_def (n : ℤ) : W.ω n =
    reducedInvarDenom W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n *
      ((CC W.a₁ * polynomialY W - polynomialX W) * C W.Ψ₃
        + 4 * polynomial W * (2 * polynomial W + C W.Ψ₂Sq))
    - complEDS₂Aux W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n + negPolynomial W * W.ψ n ^ 3 := (rfl)

/-- **The defining identity of `ω`**:
`2 ω n + a₁ φ n ψ n + a₃ (ψ n)³ = ψc n`. -/
theorem ω_spec (n : ℤ) :
    2 * W.ω n + CC W.a₁ * W.φ n * W.ψ n + CC W.a₃ * W.ψ n ^ 3 = W.ψc n := by
  -- The directed steps: reindex `ψc` through the reduced invariant, cancel, and open `ω`.
  rw [ψc_def, complEDS₂_eq_reducedInvarNum_sub, reducedInvarNum_eq_reducedInvarDenom_mul,
    preΨ₄_add_ψ₂_pow_four, mul_assoc (C _), φ_mul_ψ, ψ_eq_normEDS,
    IsEllipticNet.invarDenom_normEDS_one_eq_reducedInvarDenom_mul, WeierstrassCurve.ω,
    ← ψ_eq_normEDS]
  -- The rest is undirected normalisation: unfold the curve constants and push `C` through.
  simp only [invar_def, b₂, b₄, ψ₂, polynomialY, polynomialX, negPolynomial, map_ofNat, C_add,
    C_mul, C_pow]
  ring1

/-- `ω_spec` solved for `2 ω n`. -/
theorem two_mul_ω (n : ℤ) :
    2 * W.ω n = W.ψc n - CC W.a₁ * W.φ n * W.ψ n - CC W.a₃ * W.ψ n ^ 3 := by
  rw [← ω_spec]; abel

/-- `ψ n * ψc n = ψ (2n)`: the complement identity `ψc` is named for. -/
theorem ψ_mul_ψc (n : ℤ) : W.ψ n * W.ψc n = W.ψ (2 * n) :=
  normEDS_mul_complEDS₂ _ _ _ _

/-- `ω` at `0` is `1`, matching `ψ 0 = 0` and `φ 0 = 1`. -/
@[simp] theorem ω_zero : W.ω 0 = 1 := by
  rw [ω_def, reducedInvarDenom_zero, complEDS₂Aux_zero, ψ_zero]
  ring

/-- `ω` at `1` is `Y`, matching `ψ 1 = 1` and `φ 1 = X`: the point `1 • (X, Y)` is `(X, Y)`
itself. -/
@[simp] theorem ω_one : W.ω 1 = Y := by
  rw [ω_def, reducedInvarDenom_one, complEDS₂Aux_one, ψ_one, ψ₂, ← Affine.Y_sub_polynomialY]
  ring1

/-- `ψc` is an even family. -/
@[simp] theorem ψc_neg (n : ℤ) : W.ψc (-n) = W.ψc n := by simp only [ψc_def, complEDS₂_neg]

end

section Map

/-- `ψc` is natural in the coefficient ring. -/
@[simp]
theorem map_ψc (f : R →+* S) (n : ℤ) : (W.map f).ψc n = (W.ψc n).map (mapRingHom f) := by
  simp_rw [ψc_def, ← coe_mapRingHom, map_complEDS₂, map_ψ₂, map_Ψ₃, map_preΨ₄]
  simp

open Affine in
/-- `ω` is natural in the coefficient ring. -/
@[simp]
theorem map_ω (f : R →+* S) (n : ℤ) : (W.map f).ω n = (W.ω n).map (mapRingHom f) := by
  simp_rw [WeierstrassCurve.ω, ← coe_mapRingHom, map_add, map_sub, map_mul,
    map_reducedInvarDenom, map_complEDS₂Aux, map_polynomial, map_polynomialX, map_polynomialY,
    map_negPolynomial, map_ψ₂, map_Ψ₃, map_preΨ₄, map_Ψ₂Sq, map_ψ]
  simp

open Universal in
/-- `ω_neg` over the universal curve. -/
private theorem universal_ω_neg (n : ℤ) :
    curve.ω (-n) = curve.ω n + CC curve.a₁ * curve.φ n * curve.ψ n
      + CC curve.a₃ * curve.ψ n ^ 3 := by
  -- Double both sides — `2` is a nonzerodivisor here — and read the identity off `two_mul_ω`.
  rw [← mul_cancel_left_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero (two_ne_zero (α := Universal.Poly)))]
  simp_rw [left_distrib, two_mul_ω, ψc_neg, ψ_neg, φ_neg]
  ring1

open Universal in
/-- The parity rule for `ω`, `@[simp]` like its `ψ`/`φ`/`ψc` counterparts: without it the
negative index has no elimination route at all. -/
@[simp]
theorem ω_neg (n : ℤ) :
    W.ω (-n) = W.ω n + CC W.a₁ * W.φ n * W.ψ n + CC W.a₃ * W.ψ n ^ 3 := by
  rw [← W.map_specialize, map_ω, universal_ω_neg, map_φ, map_ω, map_ψ]
  simp

end Map

section BaseChange

variable {S : Type*} [CommRing S] [Algebra R S] {A : Type*} [CommRing A] [Algebra R A]
  [Algebra S A] [IsScalarTower R S A] {B : Type*} [CommRing B] [Algebra R B] [Algebra S B]
  [IsScalarTower R S B] (f : A →ₐ[S] B)

/-- `ψc` commutes with base change across an algebra homomorphism, in the form of Mathlib's
`baseChange_ψ`. -/
lemma baseChange_ψc (n : ℤ) : (W⁄B).ψc n = ((W⁄A).ψc n).map (mapRingHom f) := by
  rw [← map_ψc, map_baseChange]

/-- `ω` commutes with base change across an algebra homomorphism, in the form of Mathlib's
`baseChange_φ`. -/
lemma baseChange_ω (n : ℤ) : (W⁄B).ω n = ((W⁄A).ω n).map (mapRingHom f) := by
  rw [← map_ω, map_baseChange]

end BaseChange

end

end WeierstrassCurve

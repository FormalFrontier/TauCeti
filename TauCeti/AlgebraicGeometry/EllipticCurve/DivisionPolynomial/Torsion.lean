/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
public import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Eval
public import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.ZSMul
public import TauCeti.AlgebraicGeometry.EllipticCurve.Integrality
-- Not `public`: `evalEval_ψ₂_sq` is used only inside `den_dvd_four_of_order_two`'s proof,
-- so importers of this file have no reason to see `Discriminant`.
import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Discriminant

/-!
# Integrality of torsion away from order two, under a squarefree hypothesis

The Nagell–Lutz statement is that a torsion point of an integral Weierstrass model has integral
coordinates. **This file does not prove that.** It proves the cases a squarefree hypothesis makes
accessible — an `n`-torsion point for odd `n` with `(n : R)` squarefree, or for even `n` with
`(n / 2 : R)` squarefree provided the point is not itself two-torsion — over an arbitrary unique
factorisation domain `R` with fraction field `K` rather than only over `ℤ/ℚ`. Order two is
genuinely excluded: such a point need not be integral, and what is proved instead is the
denominator bound `den(x) ∣ 4`.

The bridge from the group law to polynomials is `ZSMul.lean`'s
`evalEval_ψ_eq_zero_of_zsmul_eq_zero`: if
`n • P = 0` then `ψₙ` vanishes at `P`. That turns a torsion hypothesis into a polynomial root,
and the root feeds `isInteger_x_of_equation_of_is_root_of_squarefree_leadingCoeff` from
`EllipticCurve/Integrality.lean`, whose squarefree-leading-coefficient hypothesis is supplied by
Mathlib's `leadingCoeff_preΨ` (`= n` for odd `n` and `= n / 2` for even `n`) and
`leadingCoeff_Ψ₂Sq` (`= 4`). Only the `x`-coordinate is stated: `y` is then integral by
`Integrality.lean`'s `isInteger_y_of_equation_of_isInteger_x`, which needs nothing about torsion.

## Main results

* `WeierstrassCurve.isInteger_x_of_odd_torsion_of_squarefree`: for an **odd** `n` with `(n : R)`
  squarefree, an `n`-torsion point has integral `x`. The odd-prime case the Nagell–Lutz route
  quotes is the specialisation `n = p`; primality is not used.
* `WeierstrassCurve.isInteger_x_of_even_torsion_of_squarefree`: for an **even** `n` with
  `(n / 2 : R)` squarefree and `(2 : R) ≠ 0`, an `n`-torsion point that is not two-torsion has
  integral `x`. `WeierstrassCurve.isInteger_x_of_order_four_of_squarefree` is the case `n = 4`,
  where `4 / 2 = 2` collapses both arithmetic premises into `Squarefree (2 : R)`.
* `WeierstrassCurve.den_dvd_four_of_order_two`: order two is the genuine exception — the
  coordinates need not be integral, but the denominator of `x` divides `4`.

## Roadmap

New mathematics: `TauCetiRoadmap/EllipticCurves/README.md:821` — "**The torsion subgroup and
Nagell–Lutz**", whose route is stated at `:830`–`:831` as "division polynomials". The roadmap asks
for the theorem over `ℚ` for both integral models; these are the UFD-level statements that
specialise to it.

## Provenance

Ported from J. Xu and D. K. Angdinata's
`projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDPrimeOrder.lean` in AINTLIB
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0, `main @ 1c1c74664e40071c2c2165bc55ca2616a67ccd6b`):
`x_isInteger_of_odd_prime_torsion_squarefree`
(`:118`), `two_nsmul_eq_zero_of_ψ₂_eq_zero` (`:143`), `integrality_of_order_four_squarefree`
(`:156`) and `den_dvd_of_order_two` (`:183`). That file is byte-identical at `9fec8eba7652`, the
revision the roadmap pins, so the citations hold at either.

Its remaining two declarations are **already in this repository** and are called rather than
restated: `isInteger_of_root_squarefree_leading_coeff` (`:88`) is `Integrality.lean`'s
`isInteger_x_of_equation_of_is_root_of_squarefree_leadingCoeff`, and
`y_isInteger_of_x_isInteger_on_curve` (`:42`) is its `isInteger_y_of_equation_of_isInteger_x`.

Five adaptations. The source's `curveK R K W` (`PIDCurve.lean:32`) is **not ported**: it is a bare
abbreviation for `W.map (algebraMap R K)`, and Mathlib defines `W.baseChange K` to be exactly that
— `rfl`-equal — so this file uses `baseChange`, matching `Integrality.lean` and `Denominator.lean`.
Its companion `curveK_equation_iff` is then just `Affine.equation_iff` and is not needed at all.
Two wrappers are likewise declined because this repository already carries both of their halves:
`evalEval_ψ_odd` (`EvalBridge.lean:62`) is the one-line composite
`(evalEval_ψ_eq_evalEval_Ψ …).trans (evalEval_Ψ_odd …)`, inlined here at its one call site; and
`prime_order_integrality_squarefree` (`:205`) is the conjunction of
`x_isInteger_of_odd_prime_torsion_squarefree` with `y_isInteger_of_x_isInteger_on_curve`, so
callers pair `isInteger_x_of_odd_torsion_of_squarefree` with
`isInteger_y_of_equation_of_isInteger_x` directly.
The source's `evalEval_ψ_eq_zero_of_zsmul_eq_zero` (`:67`) is ported, but **into `ZSMul.lean`**
rather than here: it is a field-level corollary of `zsmul_point_eq_smulEval` with no UFD content,
so placing it beside its own input keeps consumers of the scalar-multiplication bridge from having
to import this file. It also drops the source's `[DecidableEq F]`, which TauCeti's
`zsmul_point_eq_smulEval` does not require. Finally the names are restated to describe their
conclusions: `x_isInteger_of_odd_prime_torsion_squarefree` →
`isInteger_x_of_odd_torsion_of_squarefree` (**generalised**: the source assumes an odd prime, but
primality is used there only to rule out `n = 2`, so this holds for any odd index and covers odd
composite torsion), `integrality_of_order_four_squarefree` →
`isInteger_x_of_even_torsion_of_squarefree` (**generalised** the same way: the source's argument
splits `ψ₄ = preΨ₄ * ψ₂` and reads off `leadingCoeff preΨ₄ = 2`, and `Ψ n = C (preΨ n) * ψ₂` with
`leadingCoeff (preΨ n) = n / 2` runs it verbatim at every even index; the source's own index is
kept as `isInteger_x_of_order_four_of_squarefree`), `den_dvd_of_order_two` →
`den_dvd_four_of_order_two`, `two_nsmul_eq_zero_of_ψ₂_eq_zero` →
`two_zsmul_eq_zero_of_evalEval_ψ₂_eq_zero`, restated for the Jacobian point so that the even-index
theorem needs no `[DecidableEq K]`; that one carries no integrality content and lives in
`DivisionPolynomial/ZSMul.lean`, which this file consumes.
-/

public section

open Polynomial

namespace WeierstrassCurve

open TauCeti.WeierstrassCurve


variable {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
variable {K : Type*} [Field K] [DecidableEq K] [Algebra R K] [IsFractionRing R K]
variable (W : WeierstrassCurve R)

omit [DecidableEq K] in
/-- For an **odd** `n` with `(n : R)` squarefree, an `n`-torsion point has integral
`x`-coordinate.

`ψₙ` vanishes at the point; for odd `n` that value is `preΨₙ` evaluated at `x` alone, whose
leading coefficient is `n` — squarefree by hypothesis, which is what the rational-root argument
in `Integrality.lean` needs.

Oddness is the only arithmetic input: the source states this for an odd prime, but primality is
used there solely to rule out `n = 2`, so odd composite torsion is covered by the same proof.
The `y`-coordinate follows by `isInteger_y_of_equation_of_isInteger_x`. -/
theorem isInteger_x_of_odd_torsion_of_squarefree {x y : K}
    (hns : (W.baseChange K).toAffine.Nonsingular x y)
    {n : ℤ} (hodd : ¬Even n)
    (htors : n • (Jacobian.Point.fromAffine (Affine.Point.some _ _ hns)) = 0)
    (hsf : Squarefree (n : R)) : IsLocalization.IsInteger R x := by
  have hψ := evalEval_ψ_eq_zero_of_zsmul_eq_zero (W.baseChange K) hns n htors
  -- The source's `evalEval_ψ_odd` is this composition; only its two halves are ported here.
  rw [(evalEval_ψ_eq_evalEval_Ψ (W.baseChange K) hns.left n).trans
    (evalEval_Ψ_odd (W.baseChange K) n hodd)] at hψ
  have hmap : (W.baseChange K).preΨ n = (W.preΨ n).map (algebraMap R K) :=
    WeierstrassCurve.map_preΨ ..
  rw [hmap, eval_map, ← aeval_def] at hψ
  have hsf_lc : Squarefree (W.preΨ n).leadingCoeff := by
    rw [W.leadingCoeff_preΨ hsf.ne_zero, ite_eq_right hodd]
    exact hsf
  exact isInteger_x_of_equation_of_is_root_of_squarefree_leadingCoeff W hns.left hψ hsf_lc

omit [DecidableEq K] in
/-- For an **even** `n` with `(n / 2 : R)` squarefree, a point killed by `n` but **not** by `2`
has integral `x`-coordinate.

`ψₙ` vanishes at the point, and for even `n` it is `preΨₙ * ψ₂`; the second factor vanishing
would make the point two-torsion, which `h2ne` excludes, so the first vanishes, and `preΨₙ` has
leading coefficient `n / 2`. Excluding order two is not a technicality — a two-torsion point need
not be integral at all, and `den_dvd_four_of_order_two` is everything that survives there.

`h2` is needed on top of `hsf`: it is `n / 2` that is squarefree, and `(n : R) = 2 * (n / 2 : R)`
is what the leading-coefficient formula asks to be nonzero. The `y`-coordinate follows by
`isInteger_y_of_equation_of_isInteger_x`. -/
theorem isInteger_x_of_even_torsion_of_squarefree {x y : K}
    (hns : (W.baseChange K).toAffine.Nonsingular x y)
    {n : ℤ} (heven : Even n)
    (htors : n • (Jacobian.Point.fromAffine (Affine.Point.some _ _ hns)) = 0)
    (h2ne : (2 : ℤ) • Jacobian.Point.fromAffine (Affine.Point.some _ _ hns) ≠ 0)
    (h2 : (2 : R) ≠ 0) (hsf : Squarefree ((n / 2 : ℤ) : R)) :
    IsLocalization.IsInteger R x := by
  have hψ := evalEval_ψ_eq_zero_of_zsmul_eq_zero (W.baseChange K) hns n htors
  rw [evalEval_ψ_eq_evalEval_Ψ (W.baseChange K) hns.left n, _root_.WeierstrassCurve.Ψ,
    ite_eq_left heven, evalEval_mul, evalEval_C] at hψ
  rcases mul_eq_zero.mp hψ with hpreΨ | hψ₂
  · have hmap : (W.baseChange K).preΨ n = (W.preΨ n).map (algebraMap R K) :=
      WeierstrassCurve.map_preΨ ..
    rw [hmap, eval_map, ← aeval_def] at hpreΨ
    have hn : (n : R) ≠ 0 := by
      rw [← Int.two_mul_ediv_two_of_even heven]
      push_cast
      exact mul_ne_zero h2 hsf.ne_zero
    have hsf_lc : Squarefree (W.preΨ n).leadingCoeff := by
      rw [W.leadingCoeff_preΨ hn, ite_eq_left heven]
      exact hsf
    exact isInteger_x_of_equation_of_is_root_of_squarefree_leadingCoeff W hns.left hpreΨ hsf_lc
  · exact absurd (two_zsmul_eq_zero_of_evalEval_ψ₂_eq_zero (W.baseChange K) hns hψ₂) h2ne

omit [DecidableEq K] in
/-- **An order-four point is integral when `(2 : R)` is squarefree.** The index-four case of
`isInteger_x_of_even_torsion_of_squarefree`, and the statement the Nagell–Lutz route quotes:
`4 / 2 = 2`, so a single squarefree hypothesis carries both of that theorem's arithmetic
premises. -/
theorem isInteger_x_of_order_four_of_squarefree {x y : K}
    (hns : (W.baseChange K).toAffine.Nonsingular x y)
    (h4 : (4 : ℤ) • (Jacobian.Point.fromAffine (Affine.Point.some _ _ hns)) = 0)
    (h2ne : (2 : ℤ) • Jacobian.Point.fromAffine (Affine.Point.some _ _ hns) ≠ 0)
    (hsf : Squarefree (2 : R)) : IsLocalization.IsInteger R x :=
  isInteger_x_of_even_torsion_of_squarefree W hns (by decide) h4 h2ne hsf.ne_zero
    (by simpa using hsf)

omit [DecidableEq K] in
/-- **Order two is the exception, and its denominator divides `4`.** A two-torsion point need not
have integral coordinates; `ψ₂` vanishing forces `Ψ₂Sq` to vanish at `x`, and that polynomial's
leading coefficient is `4`. -/
theorem den_dvd_four_of_order_two {x y : K}
    (hns : (W.baseChange K).toAffine.Nonsingular x y)
    (h2 : (2 : ℤ) • (Jacobian.Point.fromAffine (Affine.Point.some _ _ hns)) = 0) :
    (IsFractionRing.den R x : R) ∣ (4 : R) := by
  -- In characteristic dividing `4` the statement is `_ ∣ 0`; the rational-root argument is only
  -- needed when `Ψ₂Sq` actually has leading coefficient `4`.
  rcases eq_or_ne (4 : R) 0 with h4 | h4_ne
  · rw [h4]
    exact dvd_zero _
  have hψ := evalEval_ψ_eq_zero_of_zsmul_eq_zero (W.baseChange K) hns 2 h2
  rw [WeierstrassCurve.ψ_two] at hψ
  have hΨ_zero : (W.baseChange K).Ψ₂Sq.eval x = 0 := by
    rw [← evalEval_ψ₂_sq (W.baseChange K) hns.left, hψ, zero_pow two_ne_zero]
  have hmap : (W.baseChange K).Ψ₂Sq = W.Ψ₂Sq.map (algebraMap R K) :=
    WeierstrassCurve.map_Ψ₂Sq ..
  rw [hmap, eval_map, ← aeval_def] at hΨ_zero
  have hdvd := den_dvd_of_is_root hΨ_zero
  rwa [W.leadingCoeff_Ψ₂Sq h4_ne] at hdvd


end WeierstrassCurve

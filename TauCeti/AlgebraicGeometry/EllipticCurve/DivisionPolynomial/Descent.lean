/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Eval
public import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Integral
public import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.ZSMul
public import TauCeti.AlgebraicGeometry.EllipticCurve.Integrality

/-!
# Integrality descends along multiplication by `n`

If `n • P` has integral coordinates then so does `P`. This is the descent step of the
Nagell–Lutz argument: it lets an integrality claim about a torsion point be pulled back from a
multiple where it is easier to establish.

The mechanism is one identity between the two `x`-coordinates. `zsmul_point_eq_smulEval` gives the
Jacobian coordinates of `n • P` as `(φₙ : ωₙ : ψₙ)` evaluated at `P`, and comparing that with the
affine representative of `n • P` yields `x' · ΨSqₙ(x) = Φₙ(x)`. Writing `x'` as `algebraMap R K c`
for the `c : R` its integrality supplies, that exhibits `x` as a root of the **monic** polynomial
`Φₙ − C c · ΨSqₙ` over `R`, so integral closure places `x` in `R`, and the curve equation carries
integrality from `x` to `y`.

## Main results

* `WeierstrassCurve.mul_eval_ΨSq_eq_eval_Φ_of_zsmul`: the coordinate identity
  `x' · ΨSqₙ(x) = Φₙ(x)` relating `P` and `n • P`, over a field.
* `WeierstrassCurve.isInteger_of_zsmul_isInteger`: **the descent step.** Over a base `R`
  integrally closed in `K`, if `n • P = P'` and `P'` has integral `x`-coordinate, both
  coordinates of `P` are integral.

## Roadmap

New mathematics: `TauCetiRoadmap/EllipticCurves/README.md:821` — "**The torsion subgroup and
Nagell–Lutz**", route "division polynomials" (`:830`–`:831`). This is the descent half of that
route; it is a prerequisite of the roadmap's stated theorem rather than the theorem itself.

## Provenance

Ported from J. Xu and D. K. Angdinata's
`projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDIntegralMultiple.lean` in AINTLIB
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0, `main @ 1c1c74664e40071c2c2165bc55ca2616a67ccd6b`):
`x_coord_nsmul_eq` (`:48`) and `isInteger_of_nsmul_isInteger` (`:93`). The file is byte-identical
at `9fec8eba7652`, the revision the roadmap pins for this project (`README:1072`), verified by
blob hash, so the citations hold at either.

The source's intermediate `x_isInteger_of_nsmul_x_isInteger` (`:73`) is **not ported**: it is the
composition of the coordinate identity above with the integral-root argument, and this repository
already carries the latter as `Integral.lean`'s `isInteger_of_mul_eval_ΨSq_eq_eval_Φ` — whose own
docstring notes that "no point, and no multiple, occurs in this statement", i.e. it is exactly the
point-free half. The composition is inlined here rather than given a name.

Three adaptations. `curveK R K W` is `W.map (algebraMap R K)`, which is `rfl`-equal to Mathlib's
`W.baseChange K`; this file uses `baseChange`, matching `Integral.lean` and `Integrality.lean`.
The source's `hn : n ≠ 0`, `hn_R : (n : R) ≠ 0` and `_hy'` hypotheses are dropped — none is used
by the proof once the integral-root step is delegated, and `_hy'` is unused upstream too.

**The base ring is generalised, and `K` need not be its fraction field.** The source assumes a
UFD; no factorisation argument occurs anywhere in these two proofs, so integral closedness alone
suffices, and `[IsDomain R]` turns out to be unnecessary as well — `unusedSectionVars` reported it
once the UFD hypothesis was removed. Integral closedness is then asked for *relative to `K`*, as
`[IsIntegrallyClosedIn R K]`, rather than as `[IsIntegrallyClosed R] [IsFractionRing R K]`: this is
the hypothesis `Integral.lean`'s `isInteger_of_mul_eval_ΨSq_eq_eval_Φ` already takes, and it is
strictly weaker, since the pair implies it (`isIntegrallyClosed_iff_isIntegrallyClosedIn`) but says
more besides. The `y`-coordinate step is then exactly `Integrality.lean`'s
`isInteger_y_of_equation_of_isInteger_x`, which asks for `[IsIntegrallyClosedIn R K]` and nothing
else — the same hypothesis this file already carries, so it applies with no bridging.

`[DecidableEq K]` is **not** removable: `n • P` is `zsmul` for Mathlib's `AddCommGroup W.Point`
instance, which is declared under `[DecidableEq F]` because affine addition is defined by cases.
The instance is needed to *state* both theorems, so a `classical` inside the proofs cannot supply
it.
-/

public section

open Polynomial

namespace WeierstrassCurve

open TauCeti.WeierstrassCurve

variable {F : Type*} [Field F] [DecidableEq F] (E : WeierstrassCurve F)

/-- **The `x`-coordinates of `P` and `n • P` satisfy `x' · ΨSqₙ(x) = Φₙ(x)`.**

The division-polynomial formula for the `x`-coordinate of a multiple, cleared of its denominator,
so that it holds with no side condition on `ΨSqₙ(x)` vanishing. -/
-- `zsmul_point_eq_smulEval` presents `n • P` as the Jacobian class of `(φₙ : ωₙ : ψₙ)` evaluated
-- at `P`; comparing that with the affine representative `(x' : y' : 1)` and reading off the
-- `X`-coordinate gives the identity, after rewriting `φₙ` and `ψₙ²` into `Φₙ` and `ΨSqₙ`.
theorem mul_eval_ΨSq_eq_eval_Φ_of_zsmul {x y : F} (hns : E.toAffine.Nonsingular x y)
    {x' y' : F} (hns' : E.toAffine.Nonsingular x' y') {n : ℤ}
    (hnP : n • (Affine.Point.some _ _ hns) = Affine.Point.some _ _ hns') :
    x' * (E.ΨSq n).eval x = (E.Φ n).eval x := by
  have hJac : n • Jacobian.Point.fromAffine (Affine.Point.some _ _ hns) =
      Jacobian.Point.fromAffine (Affine.Point.some _ _ hns') := by
    have h := congrArg (Jacobian.Point.toAffineAddEquiv E).symm hnP
    rw [map_zsmul] at h
    simpa using h
  have hsmul := zsmul_point_eq_smulEval E hns n
  -- `≈` on `Fin 3 → F` is the Jacobian equivalence, so its `HasEquiv` instance must be in scope.
  -- The two triples represent the same Jacobian point, so they differ by a unit scalar.
  open Jacobian in
  have hequiv : smulEval E x y n ≈ ![x', y', 1] := by
    rw [Jacobian.Point.ext_iff, hsmul] at hJac; exact Quotient.exact hJac
  have hX := Jacobian.X_eq_of_equiv hequiv
  simp only [smulEval, Function.comp, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hX
  norm_num at hX
  rw [evalEval_φ_eq_eval_Φ E hns.left n] at hX
  have hΨSq := evalEval_Ψ_sq_eq_eval_ΨSq E hns.left n
  rw [← evalEval_ψ_eq_evalEval_Ψ E hns.left n] at hΨSq
  rw [hΨSq] at hX
  exact hX.symm

variable {R : Type*} [CommRing R]
variable {K : Type*} [Field K] [DecidableEq K] [Algebra R K] [IsIntegrallyClosedIn R K]
variable (W : WeierstrassCurve R)

/-- **Integrality descends along multiplication by `n`.** If `n • P = P'` and `P'` has integral
`x`-coordinate, then both coordinates of `P` are integral.

The conclusion is for every `n`, with no primality, no bound on the order of `P`, and no hypothesis
that `P` is torsion at all. -/
-- With `c : R` the witness to `hx'`, the coordinate identity exhibits `x` as a root of the monic
-- `Φₙ − C c · ΨSqₙ` over `R`, so integral closure puts `x` in `R`; the curve equation then carries
-- that to `y`.
theorem isInteger_of_zsmul_isInteger {x y : K}
    (hns : (W.baseChange K).toAffine.Nonsingular x y) {n : ℤ}
    {x' y' : K} (hns' : (W.baseChange K).toAffine.Nonsingular x' y')
    (hnP : n • (Affine.Point.some _ _ hns) = Affine.Point.some _ _ hns')
    (hx' : IsLocalization.IsInteger R x') :
    IsLocalization.IsInteger R x ∧ IsLocalization.IsInteger R y := by
  have hid := mul_eval_ΨSq_eq_eval_Φ_of_zsmul (W.baseChange K) hns hns' hnP
  have hx := isInteger_of_mul_eval_ΨSq_eq_eval_Φ W n hx' hid
  exact ⟨hx, isInteger_y_of_equation_of_isInteger_x W hns.left hx⟩

end WeierstrassCurve

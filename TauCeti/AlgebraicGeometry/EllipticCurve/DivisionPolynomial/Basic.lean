/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms

/-!
# Identities among the division polynomials

Two identities the Nagell–Lutz route needs and Mathlib lacks — one univariate, one bivariate —
and the consumer the univariate one exists for.

Mathlib gives the univariate polynomials `Φₙ` in two registers. `Φ_three` and `Φ_four` are stated
through the division polynomials `Ψ₃`, `preΨ₄` and `Ψ₂Sq`; `Φ_two` is stated through the
`b`-invariants, as `X ^ 4 - C b₄ * X ^ 2 - C (2 * b₆) * X - C b₈`. This file supplies the `n = 2`
member of the first register, which Mathlib does not have, together with the one evaluation
identity that the same Nagell–Lutz route needs and Mathlib likewise lacks: what `ψ₂` reduces to on
a curve in characteristic-≠-2 normal form.

## Main results

* `WeierstrassCurve.Φ_two_eq_X_mul_Ψ₂Sq_sub_Ψ₃`: `Φ₂ = X · Ψ₂Sq - Ψ₃`.
* `WeierstrassCurve.eval_Ψ₃_eq_sub_mul_eval_Ψ₂Sq`: its consumer — from the cleared doubling
  relation `x' · ΨSq₂(x) = Φ₂(x)`, the factorisation `Ψ₃(x) = (x - x') · Ψ₂Sq(x)`.
* `WeierstrassCurve.evalEval_ψ₂_of_isCharNeTwoNF`: `ψ₂(x, y) = 2y` whenever `a₁ = a₃ = 0`. The
  two-division polynomial is `2y + a₁x + a₃`, so Mathlib's `IsCharNeTwoNF` collapses it. It sits
  here rather than with its consumer because it is a plain identity among Mathlib's division
  polynomials over any commutative ring — the same reason as the two above — and because a
  consumer-side home would tie its availability to torsion imports it does not need.

All three hold over an arbitrary commutative ring, with no ellipticity and no division. The first
has no hypothesis at all; the second's is an equation between ring elements; the third's is
Mathlib's `IsCharNeTwoNF` instance, which is a condition on the curve's coefficients rather than on
a point. The first two are statements about univariate polynomials and mention no point at all; the
third evaluates the bivariate `ψ₂`, but at an arbitrary `(x, y)` — it does not ask that the pair lie
on the curve.

Declarations here are stated in the root
`WeierstrassCurve` namespace, not under `TauCeti`, because they extend Mathlib's own
division-polynomial API and mention nothing of this repository's — the same call
`DivisionPolynomial/Invariant.lean` makes for `invar`, `C_Ψ₃` and `preΨ₄_add_Ψ₂Sq_sq`, and what
`scripts/lint-dot-notation.py` requires so that `W.Φ_two_eq_X_mul_Ψ₂Sq_sub_Ψ₃` elaborates.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, Layer 6, item "The torsion subgroup and Nagell–Lutz",
names the discriminant half of the theorem twice: at `:827` as
"`lutz_nagell_integrality_general`, with its discriminant companion", and in the Layer 6 note at
`:1163`–`:1170` as "the `κ² ∣ 4Δ` discriminant form". The `Φ 2` identity is the step that turns the
doubling formula for the `x`-coordinate into the factorisation `Ψ₃(x) = (x - x')·Ψ₂Sq(x)` that
argument runs on, and `evalEval_ψ₂_of_isCharNeTwoNF` is what turns `ψ₂` into `2y` once the model
is short. The rest of that route has since landed — the point-level doubling formula in
`DivisionPolynomial/Descent.lean` and the integrality theorem as
`isInteger_or_order_two_of_torsion` — so the consumers named above now exist. Nothing in this file
assumes them: every declaration here is a statement about polynomials.

## Provenance

Ported from AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at `dev/modular-curves @
9fec8eba7652`, the revision that roadmap pins for `projects/NagellLutz` (`:1071`).

The `Φ 2` identity is **unnamed** in the source. It appears only as the inner `show` of the
`eval`-level wrapper `Phi2_eval_eq`, in two files and with byte-identical proofs:
`LutzNagell/LutzNagellTheorem/PIDMain.lean:305` and
`LutzNagell/LutzNagellTheorem/GeneralDiscriminant.lean:89`. Naming it at polynomial level is the
adaptation; the tactic script is the source's, with its bare `simp` squeezed to `simp only`.

The factorisation is also unnamed there: it is the anonymous
`have hPsi3_eq : eval x Ψ₃ = (x - x') * eval x Ψ₂Sq := by linarith` inside
`kappa_sq_dvd_four_Psi3` (`GeneralDiscriminant.lean:153`), stated over `ℚ` after both `eval`-level
wrappers have fired. `PIDMain.lean:390` carries a variant of the same step with `κ₀ ^ 2` already
substituted for `Ψ₂Sq(x)`. Here it is stated over any commutative ring, since nothing in it needs a
field, and it takes the doubling relation as a hypothesis rather than reconstructing it.

`evalEval_ψ₂_of_isCharNeTwoNF` is **not** from that source. It began as a `shortCurve`-specific
identity in the short-model port and was generalised to `IsCharNeTwoNF` when review observed that
its one-line proof never uses `a₂ = 0`; `shortCurve` picks it up through Mathlib's
`isCharNeTwoNF_of_isShortNF`.

The source's two `eval`-level wrappers themselves are deliberately not ported. `Phi2_eval_eq` is
the `Φ 2` identity followed by `eval_sub, eval_mul, eval_X`, and `PsiSq_two_eval_eq` is Mathlib's
`ΨSq_two` under `eval`; neither earns a declaration once the polynomial identity has one.
-/

public section

open Polynomial

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- **`Φ 2` through the division polynomials**: `Φ₂ = X · Ψ₂Sq - Ψ₃`.

The index-`2` companion to Mathlib's `Φ_three` and `Φ_four`, which are stated in the division
polynomials where `Φ_two` is stated in the `b`-invariants. It is the shape the `x`-coordinate of a
doubled point is read in, that coordinate being `Φ₂/ΨSq₂`. -/
theorem Φ_two_eq_X_mul_Ψ₂Sq_sub_Ψ₃ : W.Φ 2 = X * W.Ψ₂Sq - W.Ψ₃ := by
  -- `Φ n = X * ΨSq n - preΨ (n + 1) * preΨ (n - 1) * (if Even n then 1 else Ψ₂Sq)`; at `n = 2` the
  -- three division polynomials involved are `ΨSq 2 = Ψ₂Sq`, `preΨ 3 = Ψ₃` and `preΨ 1 = 1`.
  rw [WeierstrassCurve.Φ, ΨSq_two]
  simp only [Int.reduceAdd, preΨ_three, Int.reduceSub, preΨ_one, mul_one, even_two, ↓reduceIte]

/-- **`Ψ₃` factorises through the doubling formula**: if `x'` and `x` satisfy the `x`-coordinate
doubling relation in its cleared form `x' · ΨSq₂(x) = Φ₂(x)`, then `Ψ₃(x) = (x - x') · Ψ₂Sq(x)`.

The hypothesis is an equation between ring elements rather than the quotient `x' = Φ₂(x)/ΨSq₂(x)`,
so this holds over an arbitrary commutative ring, with no division and no hypothesis that
`ΨSq₂(x)` is a non-zero-divisor. -/
theorem eval_Ψ₃_eq_sub_mul_eval_Ψ₂Sq {x x' : R} (h : x' * (W.ΨSq 2).eval x = (W.Φ 2).eval x) :
    (W.Ψ₃).eval x = (x - x') * (W.Ψ₂Sq).eval x := by
  rw [ΨSq_two, W.Φ_two_eq_X_mul_Ψ₂Sq_sub_Ψ₃, eval_sub, eval_mul, eval_X] at h
  linear_combination h

/-- **In characteristic-≠-2 normal form, `ψ₂` is `2y`.** The two-division polynomial is
`2y + a₁x + a₃`, so `a₁ = a₃ = 0` collapses it — and that collapse is what turns the long model's
order-two exception into the classical `y = 0`.

Stated at `IsCharNeTwoNF` rather than at `shortCurve`, which is the weakest hypothesis the one-line
proof uses: `y² = x³ + a₂x² + a₄x + a₆` needs no `a₂ = 0`. Mathlib's
`isCharNeTwoNF_of_isShortNF` hands the instance to `shortCurve` for free, so the short-model call
sites are unchanged. Over any commutative ring, because both `ℤ` (for the integral conclusion) and
`ℚ` (for the point) need it. -/
@[simp] lemma evalEval_ψ₂_of_isCharNeTwoNF {R : Type*} [CommRing R] (W : WeierstrassCurve R)
    [W.IsCharNeTwoNF] (x y : R) : W.ψ₂.evalEval x y = 2 * y := by
  simp [WeierstrassCurve.ψ₂, Affine.polynomialY]

end WeierstrassCurve

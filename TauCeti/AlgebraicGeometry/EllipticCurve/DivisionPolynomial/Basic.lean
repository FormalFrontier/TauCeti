/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic

/-!
# Identities among the univariate division polynomials

Mathlib gives the univariate polynomials `Φₙ` in two registers. `Φ_three` and `Φ_four` are stated
through the division polynomials `Ψ₃`, `preΨ₄` and `Ψ₂Sq`; `Φ_two` is stated through the
`b`-invariants, as `X ^ 4 - C b₄ * X ^ 2 - C (2 * b₆) * X - C b₈`. This file supplies the `n = 2`
member of the first register, which Mathlib does not have.

## Main results

* `WeierstrassCurve.Φ_two_eq_X_mul_Ψ₂Sq_sub_Ψ₃`: `Φ₂ = X · Ψ₂Sq - Ψ₃`.
* `WeierstrassCurve.eval_Ψ₃_eq_sub_mul_eval_Ψ₂Sq`: its consumer — from the cleared doubling
  relation `x' · ΨSq₂(x) = Φ₂(x)`, the factorisation `Ψ₃(x) = (x - x') · Ψ₂Sq(x)`.

Both hold over an arbitrary commutative ring, with no point of a curve, no ellipticity and no
division; the first has no hypothesis at all and the second's is an equation between ring elements.
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
argument runs on. The rest of that route — the point-level doubling formula and
`lutz_nagell_integrality_general` — is not in this repository yet, and nothing here assumes it.

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

end WeierstrassCurve

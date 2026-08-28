/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.InfinityPlace.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Basic
-- `natDegree_Φ` and `natDegree_ΨSq` are used only inside the proofs below, so private.
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree

/-!
# The place at infinity on the coordinates of `[n]`

`Affine/FunctionField/InfinityPlace/Basic.lean` computes the valuation at infinity of the
coordinate functions: `v_∞ x = exp 2` and `v_∞ y = exp 3`, i.e. `x` has a double pole at `O`
and `y` a triple one. This file does the same for `x ∘ [n]`, the `x`-coordinate of `[n]` at the
generic point built in `Isogeny/MulByInt/Basic.lean`.

The answer, **for `n` nonzero in `F`**, is that nothing changes: `v_∞ (x ∘ [n]) = exp 2 = v_∞ x`.
The pole order at `O` is unaffected by `[n]`, even though the *total* degree of the pole divisor
grows like `n²` — the extra poles sit at the other points of `[n]⁻¹(O)`, not at `O`.

Every result below carries `(n : F) ≠ 0`, inherited from Mathlib's `natDegree_ΨSq`, which reads
the degree of `ψₙ²` off the leading coefficient `n ²`. So `n = 0` and the multiples of the
characteristic are **not** covered: this file does not say what `v_∞ (x ∘ [p])` is in
characteristic `p`. Closing that needs the same `IsCoprime (W.Φ n) (W.ΨSq n)` that
`Isogeny/MulByInt/Basic.lean` records as the gap in `psiFunctionField_ne_zero`.

## The computation

`x ∘ [n]` is `Φₙ / ψₙ²`, and both `Φₙ` and `ψₙ²` are images of *univariate* polynomials: `Φₙ`
by `Affine.CoordinateRing.mk_φ`, and `ψₙ²` by `psiFunctionField_sq`. The valuation of such an
image is read off its degree by `Affine.infinityPlace_algebraMap_polynomial`, which lives in
`Affine/FunctionField/InfinityPlace/Basic.lean` because it is about the function field and not
about `[n]`: `v_∞` is the square of Mathlib's `RatFunc.inftyValuation`, which on a polynomial is
`exp (natDegree)`. So the two
degrees `n²` and `n² - 1` (`natDegree_Φ`, `natDegree_ΨSq`) give `exp (2 * n²)` and
`exp (2 * (n² - 1))`, and the quotient is `exp 2`.

The `- 1` in the second degree is the whole content: it is why the answer is `exp 2` rather
than something growing with `n`.

## Main results

* `TauCeti.Isogeny.infinityPlace_phiFunctionField`,
  `TauCeti.Isogeny.infinityPlace_psiFunctionField_sq`: the two pole orders, `2n²` and
  `2(n² - 1)`.
* `TauCeti.Isogeny.infinityPlace_mulByIntX`: `v_∞ (x ∘ [n]) = exp 2`, for `(n : F) ≠ 0`.
* `TauCeti.Isogeny.infinityPlace_mulByIntX_eq_infinityPlace_genericX`: equivalently, for
  `(n : F) ≠ 0`, `[n]` does not change the pole order of `x` at infinity.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.5 and III.4.
* Adapted from the AINTLIB `HasseWeil` project (Chris Birkbeck),
  [`HasseWeil/OrdAtInftyBridge.lean`](https://github.com/CBirkbeck/AINTLIB), Apache-2.0, at
  commit `513e83879e2f8cbc626eb9e04d660e92be16ccba`, declarations `ordAtInfty_Φ_ff`,
  `ordAtInfty_ΨSq_ff`, `mulByInt_x_ne_zero` and `ordAtInfty_mulByInt_x`.

  The source states these through its own `ordAtInfty : K(E) → WithTop ℤ` on a
  `SmoothPlaneCurve` wrapper; both are re-based here onto the valuation `infinityPlace` that
  `main` already has, so `ord = -2` appears as `v = exp 2`. Its `ordAtInfty_x_gen`,
  `ordAtInfty_y_gen` and `ordAtInfty_algebraMap_F_nonzero` are **not** ported: they exist as
  `infinityPlace.X`, `infinityPlace.mk_Y` and `infinityPlace.C`.
-/

public section

open Polynomial WeierstrassCurve

open scoped Polynomial.Bivariate RatFunc

namespace TauCeti

variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)

namespace Isogeny

-- The canonical `mk W (C p) = algebraMap _ _ p`, exposed in `Affine/CoordinateRing.lean` for
-- this use. It sits under TauCeti's own `WeierstrassCurve.Affine` root, not Mathlib's, so it is
-- opened by name rather than reached through the `Affine.` prefix used elsewhere here.
open TauCeti.WeierstrassCurve.Affine.CoordinateRing (mk_C_eq_algebraMap)

/-- `Φₙ` at the generic point is the image of the univariate `Φₙ`. -/
theorem phiFunctionField_eq_algebraMap (n : ℤ) :
    phiFunctionField W n = algebraMap F[X] W.FunctionField (W.Φ n) := by
  rw [phiFunctionField_def, Affine.CoordinateRing.mk_φ,
    mk_C_eq_algebraMap, ← IsScalarTower.algebraMap_apply]

/-- **`Φₙ` has a pole of order `2n²` at infinity.** Its degree is `n²` and it is nonzero for
every `n`, both without any hypothesis on the characteristic. -/
@[simp]
theorem infinityPlace_phiFunctionField (n : ℤ) :
    W.infinityPlace (phiFunctionField W n) = WithZero.exp (2 * (n.natAbs : ℤ) ^ 2) := by
  rw [phiFunctionField_eq_algebraMap,
    Affine.infinityPlace_algebraMap_polynomial W (W.Φ_ne_zero n), W.natDegree_Φ n]
  push_cast
  ring_nf

/-- **`ψₙ²` has a pole of order `2(n² - 1)` at infinity.**

Not `@[simp]`, unlike the two valuation lemmas around it: `psiFunctionField_sq`
(`Isogeny/MulByInt/Basic.lean`) is itself `@[simp]` and rewrites this left-hand side's argument
`psiFunctionField W n ^ 2`, so the statement is not in simp-normal form and `simpNF` rejects the
tag. Stating it in that normal form instead would remove every mention of `ψₙ`, which is the
content of the lemma — the same trade-off recorded for `infinityPlace.X` in
`Affine/FunctionField/InfinityPlace/Basic.lean`.

The hypothesis is Mathlib's: `natDegree_ΨSq` reads the degree off the leading coefficient `n²`,
which vanishes when the characteristic divides `n`. -/
theorem infinityPlace_psiFunctionField_sq {n : ℤ} (hnF : (n : F) ≠ 0) :
    W.infinityPlace (psiFunctionField W n ^ 2) =
      WithZero.exp (2 * ((n.natAbs : ℤ) ^ 2 - 1)) := by
  rw [psiFunctionField_sq, mk_C_eq_algebraMap,
    ← IsScalarTower.algebraMap_apply,
    Affine.infinityPlace_algebraMap_polynomial W (W.ΨSq_ne_zero hnF), W.natDegree_ΨSq hnF]
  -- `natDegree_ΨSq` gives `n.natAbs ^ 2 - 1` as a *natural* subtraction, so the cast only
  -- distributes once `1 ≤ n.natAbs ^ 2` is available.
  have hn0 : n ≠ 0 := fun h ↦ hnF (by simp [h])
  have h1 : 1 ≤ n.natAbs ^ 2 := Nat.one_le_pow _ _ (Int.natAbs_pos.mpr hn0)
  congr 1
  rw [Nat.cast_sub h1]
  push_cast
  ring

/-- **`[n]` does not move the pole of `x` at infinity, when `(n : F) ≠ 0`**:
`v_∞ (x ∘ [n]) = exp 2`, the same value `infinityPlace.X` gives for `x` itself. The hypothesis is
on the image of `n` in `F`, so `n = 0` and the multiples of the characteristic are excluded.

The two pole orders `2n²` and `2(n² - 1)` differ by exactly `2`, and that difference is the
answer. The total pole divisor of `x ∘ [n]` does grow with `n`, but its other poles sit at the
remaining points of `[n]⁻¹(O)`, which this valuation does not see. -/
@[simp]
theorem infinityPlace_mulByIntX {n : ℤ} (hnF : (n : F) ≠ 0) :
    W.infinityPlace (mulByIntX W n) = WithZero.exp 2 := by
  rw [mulByIntX_def, map_div₀, infinityPlace_phiFunctionField,
    infinityPlace_psiFunctionField_sq W hnF, ← WithZero.exp_sub]
  ring_nf

/-- The same statement read against `x` itself: for `(n : F) ≠ 0`, `[n]` preserves the valuation
at infinity of the `x`-coordinate. -/
theorem infinityPlace_mulByIntX_eq_infinityPlace_genericX {n : ℤ} (hnF : (n : F) ≠ 0) :
    W.infinityPlace (mulByIntX W n) = W.infinityPlace (W.genericX) := by
  -- `infinityPlace.X` is stated on the two-step `F[X] → CoordinateRing → FunctionField` image,
  -- which is exactly `genericX_def`'s right-hand side; collapsing the tower first would destroy
  -- the pattern it matches on.
  rw [infinityPlace_mulByIntX W hnF, Affine.genericX_def, Affine.infinityPlace.X]

end Isogeny

end TauCeti

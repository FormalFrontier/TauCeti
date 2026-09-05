/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.RatFunc.IntermediateField
public import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Coprimality

/-!
# The degree of the rational function `Φₙ / ΨSqₙ`

`Coprimality.lean` shows that `Φₙ` and `ΨSqₙ` are coprime on a nonsingular curve, so for `n ≠ 0`
the quotient `Φₙ / ΨSqₙ` is already in lowest terms. This file draws the consequence: it has
**degree `n²`**, in the sense that adjoining it to `F` inside `F(x)` leaves an extension of
dimension `n²`.

For `n ≠ 0` that quotient is the `x`-coordinate of `n • (x, y)`, so the theorem says the
`x`-coordinate map of `[n]` is a rational map of degree `n²`. At `n = 0` it is not a coordinate of
anything — `[0]` sends every point to infinity, and `ΨSq₀ = 0` makes the quotient the junk value
`0` — but the theorem still holds there, as an equality of two zeros; see its docstring.

This is the arithmetic half of `deg [n] = n²` (Silverman III.6.4(a), proved in III.6.2(d)).
The other half is the tower
`F(x, y)` over `F(x)`, which is quadratic on both storeys and therefore cancels; neither that nor
the isogeny `[n]` itself appears here.

## Main results

* `WeierstrassCurve.finrank_adjoin_Φ_div_ΨSq`: `[F(x) : F(Φₙ/ΨSqₙ)] = n²`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6.4(a), whose proof
  is III.6.2(d).

## Provenance

Adapted from the AINTLIB `HasseWeil` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0), pinned
at `513e83879e2f8cbc626eb9e04d660e92be16ccba`: `HasseWeil/Basic.lean`, private declarations
`max_natDegree_num_denom_mulByInt` and `finrank_ratFunc_mulByInt`. Adapted rather than ported:
that version assumes `n ≠ 0`.
-/

public section

open Polynomial

namespace WeierstrassCurve

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

/-- **`Φₙ / ΨSqₙ` has degree `n²`**: adjoining it to `F` inside the rational function field
leaves an extension of dimension `n²`. For `n ≠ 0` this is the statement that the `x`-coordinate
map of `[n]` is a rational map of degree `n²` — the arithmetic half of `deg [n] = n²`.

Nonsingularity is assumed only where it is used. At `n = 0` the quotient is not a coordinate of
anything — `[0]` sends every point to infinity, and `ΨSq₀` vanishes, making the quotient the junk
value `0` — and the equality holds there for a singular `W` too, as one between two zeros: `F⟮0⟯`
is `⊥` and `F(x)` is not finite-dimensional over `F`, so the `finrank` is `0` by convention, while
`(0 : ℤ).natAbs ^ 2` is `0` as well. `TauCeti.RatFunc.finrank_adjoin_X_pow` reads the same way at
`n = 0`, for the same reason. -/
@[simp]
theorem finrank_adjoin_Φ_div_ΨSq (n : ℤ) (hΔ : n ≠ 0 → W.Δ ≠ 0) :
    Module.finrank
      (IntermediateField.adjoin F
        {algebraMap F[X] (RatFunc F) (W.Φ n) / algebraMap F[X] (RatFunc F) (W.ΨSq n)})
      (RatFunc F) = n.natAbs ^ 2 := by
  -- `RatFunc.finrank_eq_max_natDegree` reads the dimension off the numerator and denominator of
  -- the reduced fraction. For `n ≠ 0` those are `Φₙ` and `ΨSqₙ` up to a unit, since
  -- `isCoprime_Φ_ΨSq` puts the quotient in lowest terms; `natDegree_Φ` gives the numerator degree
  -- `n²` exactly, while `natDegree_ΨSq_le` only bounds the denominator degree by `n² - 1` — all
  -- the maximum needs, and the honest bound, since that degree drops in characteristic dividing
  -- `n`. At `n = 0` the fraction is `0`, so it is handled first, before any of this.
  classical
  rcases eq_or_ne n 0 with rfl | hn
  · rw [WeierstrassCurve.ΨSq_zero, map_zero, div_zero, RatFunc.finrank_eq_max_natDegree]
    simp
  have hΨ : W.ΨSq n ≠ 0 := W.ΨSq_ne_zero_of_Δ_ne_zero (hΔ hn) hn
  have hcop : IsCoprime (W.Φ n) (W.ΨSq n) := W.isCoprime_Φ_ΨSq n (hΔ hn)
  have hgu : IsUnit (gcd (W.Φ n) (W.ΨSq n)) := gcd_isUnit_iff_isRelPrime.mpr hcop.isRelPrime
  obtain ⟨c, hc, hgcd⟩ := Polynomial.isUnit_iff.mp hgu
  have hcinv : c⁻¹ ≠ 0 := inv_ne_zero hc.ne_zero
  rw [RatFunc.finrank_eq_max_natDegree, RatFunc.num_div, RatFunc.denom_div _ hΨ]
  -- `set` abstracts the gcd in `hgcd` as well, so `hgcd : C c = g` and the rewrites below match
  -- `g` syntactically rather than by unfolding it. It is needed because the `gcd` elaborated in a
  -- `have` statement is otherwise a different term from the one in the goal.
  set g := gcd (W.Φ n) (W.ΨSq n)
  have hΨdiv : W.ΨSq n / g ≠ 0 := by
    rw [← hgcd, Polynomial.div_C]
    exact mul_ne_zero hΨ (Polynomial.C_ne_zero.mpr hcinv)
  have hlc : (W.ΨSq n / g).leadingCoeff⁻¹ ≠ 0 :=
    inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hΨdiv)
  -- Dividing by the unit `g` and scaling by a nonzero constant leave both degrees alone. The two
  -- sides are handled separately because `rw` would rewrite both occurrences of the shared
  -- leading-coefficient factor at once.
  have hΦnd : (C (W.ΨSq n / g).leadingCoeff⁻¹ * (W.Φ n / g)).natDegree = (W.Φ n).natDegree := by
    rw [Polynomial.natDegree_C_mul hlc, ← hgcd, Polynomial.div_C,
      Polynomial.natDegree_mul_C hcinv]
  have hΨnd : (C (W.ΨSq n / g).leadingCoeff⁻¹ * (W.ΨSq n / g)).natDegree =
      (W.ΨSq n).natDegree := by
    rw [Polynomial.natDegree_C_mul hlc, ← hgcd, Polynomial.div_C,
      Polynomial.natDegree_mul_C hcinv]
  rw [hΦnd, hΨnd, W.natDegree_Φ n]
  exact max_eq_left ((W.natDegree_ΨSq_le n).trans (Nat.sub_le _ _))

end WeierstrassCurve

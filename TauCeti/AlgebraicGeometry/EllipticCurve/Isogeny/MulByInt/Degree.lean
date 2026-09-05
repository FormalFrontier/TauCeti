/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.DivisionPolynomialTower
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Degree
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.MapsInfinity

/-!
# The degree of multiplication by `n`

**`deg [n] = n²`.** The degree of an isogeny is the degree of `F(W)` over the image of its
function-field pullback — the pulled-back copy of the *target* function field. For `[n]` the
target is `F(W)` again, and the pullback carries the affine coordinate `x` to `Φₙ / ΨSqₙ`. That
image is pinned down by where the coordinate goes, and `DivisionPolynomialTower.lean` computes
its index as `n²` by way of the intermediate tower `F(Φₙ/ΨSqₙ) ⊆ F(x) ⊆ F(W)`.

## Main results

* `TauCeti.Isogeny.fieldPullback_mulByIntIsogeny_X`: the function-field pullback of `[n]` sends
  the affine coordinate to `Φₙ / ΨSqₙ`, read in `F(x)` rather than in the coordinate ring.
* `TauCeti.Isogeny.degree_mulByIntIsogeny`: `deg [n] = n²`, for an `n` whose division polynomial
  does not vanish at the generic point, and
  `TauCeti.Isogeny.degree_mulByIntIsogenyOfNeZero` for every `n ≠ 0`, that hypothesis being
  discharged from nonsingularity.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6.4(a).
-/

public section

open Polynomial

open scoped RatFunc

namespace TauCeti.Isogeny

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

/-- **The pullback of `[n]` sends the affine coordinate to `Φₙ / ΨSqₙ`**, with the quotient
formed in `F(x)` and then carried into `F(W)`. This is `mulByIntX` in the shape the degree
tower asks for. -/
@[simp]
theorem fieldPullback_mulByIntIsogeny_X [W.IsElliptic] {n : ℤ}
    (hn : psiFunctionField W n ≠ 0) :
    (mulByIntIsogeny W hn).fieldPullback (algebraMap F[X] W.toAffine.FunctionField X) =
      algebraMap (RatFunc F) W.toAffine.FunctionField
        (algebraMap F[X] (RatFunc F) (W.Φ n) / algebraMap F[X] (RatFunc F) (W.ΨSq n)) := by
  -- Unordered on purpose: the two sides meet in the middle, the pullback side coming down
  -- through the coordinate ring and the quotient side up out of `F(x)`.
  simp only [IsScalarTower.algebraMap_apply F[X] W.toAffine.CoordinateRing
      W.toAffine.FunctionField, fieldPullback_algebraMap, mulByIntIsogeny_pullback,
    AdjoinRoot.algebraMap_eq, mulByIntPullback_X, mulByIntX_def,
    phiFunctionField_eq_algebraMap, psiFunctionField_sq,
    TauCeti.WeierstrassCurve.Affine.CoordinateRing.mk_C_eq_algebraMap,
    ← IsScalarTower.algebraMap_apply, map_div₀]

/-- **`deg [n] = n²`** (Silverman III.6.4(a)). The pullback of `[n]` sends the affine coordinate
to `Φₙ / ΨSqₙ`, so its image is the field the tower
`F(Φₙ/ΨSqₙ) ⊆ F(x) ⊆ F(W)` measures, of index `n²`. -/
@[simp]
theorem degree_mulByIntIsogeny [W.IsElliptic] {n : ℤ} (hn : psiFunctionField W n ≠ 0) :
    (mulByIntIsogeny W hn).degree = n.natAbs ^ 2 := by
  rw [degree_def]
  exact W.finrank_fieldRange_of_apply_X_eq_Φ_div_ΨSq (fun _ => W.isUnit_Δ.ne_zero)
    (mulByIntIsogeny W hn).fieldPullback (fieldPullback_mulByIntIsogeny_X W hn)

/-- **`deg [n] = n²` for every `n ≠ 0`**, the non-vanishing hypothesis discharged from
nonsingularity as in `mulByIntIsogenyOfNeZero`. -/
-- Not `@[simp]`: `mulByIntIsogenyOfNeZero` is an `abbrev`, so `simp` sees through it to
-- `degree_mulByIntIsogeny` and `simpNF` rejects the pair as duplicates. It is stated anyway
-- because this is the form the roadmap result takes, and a caller holding `n ≠ 0` should not
-- have to unfold an abbreviation to find it.
theorem degree_mulByIntIsogenyOfNeZero [W.IsElliptic] {n : ℤ} (hn : n ≠ 0) :
    (mulByIntIsogenyOfNeZero W hn).degree = n.natAbs ^ 2 :=
  degree_mulByIntIsogeny W _

end TauCeti.Isogeny

end

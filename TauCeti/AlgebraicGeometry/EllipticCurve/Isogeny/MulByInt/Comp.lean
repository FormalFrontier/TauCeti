/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.GenericPoint
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.MapsInfinity
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Neg

/-!
# The multiplication isogenies compose: `[m] ∘ [n] = [m n]`

`[n]` is built from the division polynomials: its pullback sends the two coordinate functions of
`W` to `φₙ/ψₙ²` and `ωₙ/ψₙ³`. Reading a composite of two such pullbacks through those formulas
would mean composing rational functions of division polynomials, which is not how the identity is
proved here.

Instead every multiplication isogeny is identified by its **tautological point**: the point of
`W` over `F(W)` that its pullback cuts out is `n • ` the generic point, because the division
polynomials are precisely the Jacobian coordinates of a multiple of a point. A coordinate
pullback is determined by its tautological point, and `Isogeny/GenericPoint.lean` computes the
tautological point of a composite as that of the outer factor transported along the inner
factor's function-field map. Transport is additive and carries the generic point to the inner
factor's tautological point, so the composite of `[m]` and `[n]` has tautological point
`m • (n • ` generic `) = (m n) • ` generic. That is `[m n]`.

The same identification gives the two degenerate cases for free — `[1]` is the identity and
`[-n]` is `[n]` followed by negation — and, because a tautological point is never the point at
infinity, it shows the generic point is **not torsion**, whence `n ↦ [n]` is injective: `ℤ` sits
in `End(W)` faithfully.

## Main results

* `TauCeti.Isogeny.tautologicalPoint_mulByIntPullback`: the tautological point of `[n]` is
  `n • ` the generic point.
* `WeierstrassCurve.Affine.zsmul_genericPoint_ne_zero` and
  `WeierstrassCurve.Affine.eq_of_zsmul_genericPoint_eq`: the generic point of an elliptic curve
  is not torsion, and its multiples are pairwise distinct.
* `TauCeti.Isogeny.mulByIntIsogeny_one`: `[1]` is the identity isogeny.
* `TauCeti.Isogeny.mulByIntIsogeny_comp_mulByIntIsogeny`: `[m] ∘ [n] = [m n]`.
* `TauCeti.Isogeny.negIsogeny_comp_mulByIntIsogeny`: `[-n]` is `[n]` followed by negation.
* `TauCeti.Isogeny.mulByIntIsogeny_inj`: `[m] = [n]` exactly when `m = n`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4 and III.6.
-/

public section

open Polynomial WeierstrassCurve

open scoped Polynomial.Bivariate

namespace TauCeti

open _root_.WeierstrassCurve.Affine

variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)

namespace Isogeny

open Jacobian in
/-- The Jacobian triple `(φₙ, ωₙ, ψₙ)` at the generic point represents the same point as the
affine representative of `(φₙ/ψₙ², ωₙ/ψₙ³)`: the two differ by the scalar `ψₙ`.

`≈` is the Jacobian equivalence on triples, whose `HasEquiv` instance is scoped, which is why
the namespace is opened for this declaration alone. -/
private theorem equiv_mulByInt {n : ℤ} (hn : psiFunctionField W n ≠ 0) :
    ![phiFunctionField W n, omegaFunctionField W n, psiFunctionField W n] ≈
      ![mulByIntX W n, mulByIntY W n, 1] := by
  have hx : psiFunctionField W n ^ 2 * mulByIntX W n = phiFunctionField W n := by
    rw [mulByIntX_def]; field_simp
  have hy : psiFunctionField W n ^ 3 * mulByIntY W n = omegaFunctionField W n := by
    rw [mulByIntY_def]; field_simp
  have hsm : psiFunctionField W n • ![mulByIntX W n, mulByIntY W n, 1] =
      ![phiFunctionField W n, omegaFunctionField W n, psiFunctionField W n] := by
    funext i
    fin_cases i
    · simpa [smul_fin3] using hx
    · simpa [smul_fin3] using hy
    · simp [smul_fin3]
  exact hsm ▸ smul_equiv _ (isUnit_iff_ne_zero.2 hn)

/-- **The tautological point of `[n]` is `n` times the generic point.** The Jacobian triple
`(φₙ : ωₙ : ψₙ)` at the generic point represents `n • ` the generic point, and dividing it
through by `ψₙ` — which is what `[n]`'s two rational coordinates do — reads that class in affine
coordinates. -/
theorem tautologicalPoint_mulByIntPullback [W.IsElliptic] {n : ℤ}
    (hn : psiFunctionField W n ≠ 0) :
    (mulByIntPullback W hn).tautologicalPoint = n • W.genericPoint := by
  have hns' : (W⁄W.FunctionField).toAffine.Nonsingular (mulByIntX W n) (mulByIntY W n) :=
    equation_iff_nonsingular.mp (equation_mulByInt W hn)
  have htriple : smulEval (W⁄W.FunctionField).toAffine W.genericX W.genericY n =
      ![phiFunctionField W n, omegaFunctionField W n, psiFunctionField W n] := by
    funext i
    fin_cases i
    · exact smulEval_genericPoint_X W n
    · exact smulEval_genericPoint_Y W n
    · exact smulEval_genericPoint_Z W n
  have hJ : n • Jacobian.Point.fromAffine
        (Affine.Point.some _ _ W.nonsingular_genericX_genericY) =
      Jacobian.Point.fromAffine (Affine.Point.some _ _ hns') := by
    rw [Jacobian.Point.ext_iff,
      zsmul_point_eq_smulEval (W⁄W.FunctionField) W.nonsingular_genericX_genericY n, htriple]
    exact Quotient.sound (equiv_mulByInt W hn)
  have hsmul : n • W.genericPoint = Affine.Point.some _ _ hns' := by
    have h := congrArg (Jacobian.Point.toAffineAddEquiv (W⁄W.FunctionField)) hJ
    rw [map_zsmul] at h
    simpa [genericPoint_eq_some, Jacobian.Point.fromAffine_some,
      Jacobian.Point.toAffineLift_some] using h
  rw [hsmul]
  refine Point.eq_of_coords (CoordinatePullback.tautologicalPoint_ne_zero _)
    (Point.some_ne_zero _) ?_ ?_
  · rw [CoordinatePullback.xCoord_tautologicalPoint, Point.xCoord_some, mulByIntPullback_X]
  · rw [CoordinatePullback.yCoord_tautologicalPoint, Point.yCoord_some, mulByIntPullback_Y]

end Isogeny

end TauCeti

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)

/-- **The generic point of an elliptic curve is not torsion.** Its `n`-th multiple is the
tautological point of `[n]`, and a tautological point is an affine point, never the point at
infinity. -/
theorem zsmul_genericPoint_ne_zero [W.IsElliptic] {n : ℤ} (hn : n ≠ 0) :
    n • W.genericPoint ≠ 0 := by
  rw [← TauCeti.Isogeny.tautologicalPoint_mulByIntPullback W
    (TauCeti.Isogeny.psiFunctionField_ne_zero_of_Δ_ne_zero W W.isUnit_Δ.ne_zero hn)]
  exact TauCeti.CoordinatePullback.tautologicalPoint_ne_zero _

/-- **The multiples of the generic point are pairwise distinct**, the generic point having
infinite order. -/
theorem eq_of_zsmul_genericPoint_eq [W.IsElliptic] {m n : ℤ}
    (h : m • W.genericPoint = n • W.genericPoint) : m = n := by
  by_contra hmn
  exact zsmul_genericPoint_ne_zero W (sub_ne_zero.2 hmn) (by simp [sub_zsmul, h])

end WeierstrassCurve.Affine

namespace TauCeti

open _root_.WeierstrassCurve.Affine

variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)

namespace Isogeny

variable [W.IsElliptic]

/-- **`[1]` is the identity isogeny**, its tautological point being the generic point itself. -/
theorem mulByIntIsogeny_one (h₁ : psiFunctionField W 1 ≠ 0) :
    mulByIntIsogeny W h₁ = Isogeny.id W :=
  Isogeny.ext (CoordinatePullback.tautologicalPoint_injective (by
    rw [mulByIntIsogeny_pullback, tautologicalPoint_mulByIntPullback, Isogeny.id_pullback,
      CoordinatePullback.tautologicalPoint_id, one_zsmul]))

/-- **`[m] ∘ [n] = [m n]`.** Both sides are pullbacks with tautological point `(m n) • ` the
generic point: on the left the composite transports `m • ` generic along `[n]`'s function-field
map, which sends the generic point to `n • ` generic, and transport is additive. -/
theorem mulByIntIsogeny_comp_mulByIntIsogeny {m n : ℤ}
    (hm : psiFunctionField W m ≠ 0) (hn : psiFunctionField W n ≠ 0)
    (hmn : psiFunctionField W (m * n) ≠ 0) :
    (mulByIntIsogeny W hm).comp (mulByIntIsogeny W hn) = mulByIntIsogeny W hmn :=
  Isogeny.ext (CoordinatePullback.tautologicalPoint_injective (by
    rw [tautologicalPoint_comp, mulByIntIsogeny_pullback, tautologicalPoint_mulByIntPullback,
      map_zsmul, ← tautologicalPoint_eq_map_genericPoint, mulByIntIsogeny_pullback,
      tautologicalPoint_mulByIntPullback, mulByIntIsogeny_pullback,
      tautologicalPoint_mulByIntPullback, smul_smul]))

/-- **`[m] ∘ [n] = [m n]` for nonzero `m` and `n`**, the non-vanishing hypotheses discharged from
the discriminant as in `mulByIntIsogenyOfNeZero`. -/
theorem mulByIntIsogenyOfNeZero_comp_mulByIntIsogenyOfNeZero {m n : ℤ} (hm : m ≠ 0) (hn : n ≠ 0) :
    (mulByIntIsogenyOfNeZero W hm).comp (mulByIntIsogenyOfNeZero W hn) =
      mulByIntIsogenyOfNeZero W (mul_ne_zero hm hn) :=
  mulByIntIsogeny_comp_mulByIntIsogeny W _ _ _

/-- **`[-n]` is `[n]` followed by negation.** Negation of an isogeny is postcomposition with
`negIsogeny`, which is negation of the tautological point. -/
theorem negIsogeny_comp_mulByIntIsogeny {n : ℤ} (hn : psiFunctionField W n ≠ 0)
    (hneg : psiFunctionField W (-n) ≠ 0) :
    (negIsogeny W).comp (mulByIntIsogeny W hn) = mulByIntIsogeny W hneg :=
  Isogeny.ext (CoordinatePullback.tautologicalPoint_injective (by
    rw [tautologicalPoint_comp, negIsogeny_pullback, tautologicalPoint_negPullback, map_neg,
      ← tautologicalPoint_eq_map_genericPoint, mulByIntIsogeny_pullback,
      tautologicalPoint_mulByIntPullback, mulByIntIsogeny_pullback,
      tautologicalPoint_mulByIntPullback, neg_zsmul]))

/-- **`ℤ` sits faithfully in the endomorphisms**: the multiplication isogenies are pairwise
distinct. -/
theorem mulByIntIsogeny_inj {m n : ℤ} (hm : psiFunctionField W m ≠ 0)
    (hn : psiFunctionField W n ≠ 0) :
    mulByIntIsogeny W hm = mulByIntIsogeny W hn ↔ m = n := by
  refine ⟨fun h => _root_.WeierstrassCurve.Affine.eq_of_zsmul_genericPoint_eq W ?_, ?_⟩
  · rw [← tautologicalPoint_mulByIntPullback W hm, ← tautologicalPoint_mulByIntPullback W hn,
      ← mulByIntIsogeny_pullback, ← mulByIntIsogeny_pullback, h]
  · rintro rfl
    rfl

end Isogeny

end TauCeti

end

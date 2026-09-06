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

On an elliptic curve `W`, the multiplication isogeny `[n]` is defined for those `n` whose
division polynomial `ψₙ` does not vanish at the generic point — by
`psiFunctionField_ne_zero_of_Δ_ne_zero`, every `n ≠ 0`. For such integers this file proves
`[m] ∘ [n] = [m n]`, together with the degenerate cases `[1] = id` and `[-1] = negIsogeny`, and
that `[m] = [n]` only if `m = n`. Each identity is recorded both with the `ψ`-nonvanishing
hypotheses it needs and in the `mulByIntIsogenyOfNeZero` form a caller holding `m ≠ 0`, `n ≠ 0`
can use directly.

`[0]` is not among the isogenies compared: `ψ₀ = 0`, so `mulByIntIsogeny` is undefined there,
and the distinctness statements range only over the integers at which `[·]` is defined.

Distinctness rests on the generic point of `W` having infinite order, which is proved here as
well.

## Main results

* `TauCeti.Isogeny.map_genericPoint_mulByIntIsogeny`: the function-field map of `[n]` carries the
  generic point to `n • ` the generic point.
* `WeierstrassCurve.Affine.zsmul_genericPoint_ne_zero` and
  `WeierstrassCurve.Affine.zsmul_genericPoint_injective`: the generic point of an elliptic curve
  is not torsion, and its multiples are pairwise distinct.
* `TauCeti.Isogeny.mulByIntIsogeny_one` and `TauCeti.Isogeny.mulByIntIsogenyOfNeZero_one`: `[1]`
  is the identity isogeny.
* `TauCeti.Isogeny.mulByIntIsogeny_comp_mulByIntIsogeny` and
  `TauCeti.Isogeny.mulByIntIsogenyOfNeZero_comp_mulByIntIsogenyOfNeZero`: `[m] ∘ [n] = [m n]`.
* `TauCeti.Isogeny.mulByIntIsogeny_neg_one` and
  `TauCeti.Isogeny.mulByIntIsogenyOfNeZero_neg_one`: `[-1]` is `negIsogeny`.
* `TauCeti.Isogeny.negIsogeny_comp_mulByIntIsogeny` and
  `TauCeti.Isogeny.negIsogeny_comp_mulByIntIsogenyOfNeZero`: `[-n]` is `[n]` followed by
  negation, the case `m = -1` of the composition law.
* `TauCeti.Isogeny.mulByIntIsogeny_inj` and `TauCeti.Isogeny.mulByIntIsogenyOfNeZero_inj`:
  `[m] = [n]` exactly when `m = n`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4 and III.6.
-/

-- Every identity below is proved by comparing tautological points rather than by composing the
-- rational functions `φₙ/ψₙ²` and `ωₙ/ψₙ³`: a coordinate pullback is determined by its
-- tautological point, that of `[n]` is `n • ` the generic point
-- (`tautologicalPoint_mulByIntPullback`, in `MulByInt/Basic.lean` beside the Jacobian-coordinate
-- lemmas it needs), and that of a composite is the outer factor's transported along the inner
-- factor's function-field map (`Isogeny/GenericPoint.lean`), a transport which is additive.

public section

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
theorem zsmul_genericPoint_injective [W.IsElliptic] :
    Function.Injective fun n : ℤ => n • W.genericPoint := by
  intro m n h
  by_contra hmn
  exact zsmul_genericPoint_ne_zero W (sub_ne_zero.2 hmn) (by simp [sub_zsmul, h])

end WeierstrassCurve.Affine

namespace TauCeti

open _root_.WeierstrassCurve.Affine

variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)

namespace Isogeny

variable [W.IsElliptic]

/-- **The function-field map of `[n]` carries the generic point to `n • ` the generic point**,
the generic point transported along a pullback being that pullback's tautological point. -/
@[simp]
theorem map_genericPoint_mulByIntIsogeny {n : ℤ} (hn : psiFunctionField W n ≠ 0) :
    Point.map (mulByIntIsogeny W hn).fieldPullback W.genericPoint = n • W.genericPoint := by
  rw [← tautologicalPoint_eq_map_genericPoint, mulByIntIsogeny_pullback,
    tautologicalPoint_mulByIntPullback]

/-- **`[1]` is the identity isogeny**, its tautological point being the generic point itself. -/
@[simp]
theorem mulByIntIsogeny_one (h₁ : psiFunctionField W 1 ≠ 0) :
    mulByIntIsogeny W h₁ = Isogeny.id W :=
  Isogeny.ext (CoordinatePullback.tautologicalPoint_injective (by
    rw [mulByIntIsogeny_pullback, tautologicalPoint_mulByIntPullback, Isogeny.id_pullback,
      CoordinatePullback.tautologicalPoint_id, one_zsmul]))

/-- **`[1] = id` in the `mulByIntIsogenyOfNeZero` form**, the non-vanishing hypothesis
discharged from the discriminant. -/
-- Not `@[simp]`: `mulByIntIsogenyOfNeZero` is an `abbrev`, so `simp` sees through it to the
-- unconditional `mulByIntIsogeny_one` and `simpNF` rejects the pair as duplicates. The two
-- composition lemmas below escape this only because their `mulByIntIsogeny` forms carry a side
-- condition `simp` cannot discharge.
theorem mulByIntIsogenyOfNeZero_one : mulByIntIsogenyOfNeZero W (one_ne_zero (α := ℤ)) =
    Isogeny.id W :=
  mulByIntIsogeny_one W _

/-- **`[m] ∘ [n] = [m n]`.** Both sides are pullbacks with tautological point `(m n) • ` the
generic point: on the left the composite transports `m • ` generic along `[n]`'s function-field
map, which sends the generic point to `n • ` generic, and transport is additive. -/
@[simp]
theorem mulByIntIsogeny_comp_mulByIntIsogeny {m n : ℤ}
    (hm : psiFunctionField W m ≠ 0) (hn : psiFunctionField W n ≠ 0)
    (hmn : psiFunctionField W (m * n) ≠ 0) :
    (mulByIntIsogeny W hm).comp (mulByIntIsogeny W hn) = mulByIntIsogeny W hmn :=
  Isogeny.ext (CoordinatePullback.tautologicalPoint_injective (by
    rw [tautologicalPoint_comp, mulByIntIsogeny_pullback, tautologicalPoint_mulByIntPullback,
      map_zsmul, map_genericPoint_mulByIntIsogeny, mulByIntIsogeny_pullback,
      tautologicalPoint_mulByIntPullback, smul_smul]))

/-- **`[m] ∘ [n] = [m n]` for nonzero `m` and `n`**, the non-vanishing hypotheses discharged from
the discriminant as in `mulByIntIsogenyOfNeZero`. -/
@[simp]
theorem mulByIntIsogenyOfNeZero_comp_mulByIntIsogenyOfNeZero {m n : ℤ} (hm : m ≠ 0) (hn : n ≠ 0) :
    (mulByIntIsogenyOfNeZero W hm).comp (mulByIntIsogenyOfNeZero W hn) =
      mulByIntIsogenyOfNeZero W (mul_ne_zero hm hn) :=
  mulByIntIsogeny_comp_mulByIntIsogeny W _ _ _

/-- **`[·]` depends only on the integer.** Two non-vanishing witnesses for equal integers name
the same isogeny, by proof irrelevance. This is what transports the composition law between the
index `(-1) * n` it produces and the index `-n`. -/
theorem mulByIntIsogeny_congr {m n : ℤ} (hm : psiFunctionField W m ≠ 0)
    (hn : psiFunctionField W n ≠ 0) (hmn : m = n) :
    mulByIntIsogeny W hm = mulByIntIsogeny W hn := by
  subst hmn
  rfl

/-- **`[-1]` is negation**, both having the negated generic point for tautological point. This is
the identification that makes `[-n]` a case of `[m] ∘ [n] = [m n]`. -/
@[simp]
theorem mulByIntIsogeny_neg_one (h : psiFunctionField W (-1) ≠ 0) :
    mulByIntIsogeny W h = negIsogeny W :=
  Isogeny.ext (CoordinatePullback.tautologicalPoint_injective (by
    rw [mulByIntIsogeny_pullback, tautologicalPoint_mulByIntPullback, negIsogeny_pullback,
      tautologicalPoint_negPullback, neg_one_zsmul]))

/-- **`[-1] = negIsogeny` in the `mulByIntIsogenyOfNeZero` form**, the non-vanishing hypothesis
discharged from the discriminant. -/
-- Not `@[simp]`, for the reason recorded at `mulByIntIsogenyOfNeZero_one`.
theorem mulByIntIsogenyOfNeZero_neg_one :
    mulByIntIsogenyOfNeZero W (neg_ne_zero.2 (one_ne_zero (α := ℤ))) = negIsogeny W :=
  mulByIntIsogeny_neg_one W _

/-- **`[-n]` is `[n]` followed by negation**: the case `m = -1` of `[m] ∘ [n] = [m n]`, read
through `[-1] = negIsogeny`. -/
@[simp]
theorem negIsogeny_comp_mulByIntIsogeny {n : ℤ} (hn : psiFunctionField W n ≠ 0)
    (hneg : psiFunctionField W (-n) ≠ 0) :
    (negIsogeny W).comp (mulByIntIsogeny W hn) = mulByIntIsogeny W hneg := by
  have hone : psiFunctionField W (-1) ≠ 0 :=
    psiFunctionField_ne_zero_of_Δ_ne_zero W W.isUnit_Δ.ne_zero (neg_ne_zero.2 one_ne_zero)
  have hmul : psiFunctionField W (-1 * n) ≠ 0 := by rwa [neg_one_mul]
  rw [← mulByIntIsogeny_neg_one W hone, mulByIntIsogeny_comp_mulByIntIsogeny W hone hn hmul]
  exact mulByIntIsogeny_congr W hmul hneg (neg_one_mul n)

/-- **`[-n]` is `[n]` followed by negation, for nonzero `n`**, the non-vanishing hypotheses
discharged from the discriminant as in `mulByIntIsogenyOfNeZero`. -/
@[simp]
theorem negIsogeny_comp_mulByIntIsogenyOfNeZero {n : ℤ} (hn : n ≠ 0) :
    (negIsogeny W).comp (mulByIntIsogenyOfNeZero W hn) =
      mulByIntIsogenyOfNeZero W (neg_ne_zero.2 hn) :=
  negIsogeny_comp_mulByIntIsogeny W _ _

/-- **The multiplication isogenies are pairwise distinct**: `[m] = [n]` exactly when `m = n`, for
the integers `m`, `n` at which `[·]` is defined. -/
@[simp]
theorem mulByIntIsogeny_inj {m n : ℤ} (hm : psiFunctionField W m ≠ 0)
    (hn : psiFunctionField W n ≠ 0) :
    mulByIntIsogeny W hm = mulByIntIsogeny W hn ↔ m = n := by
  refine ⟨fun h => ?_, ?_⟩
  · have hgen : m • W.genericPoint = n • W.genericPoint := by
      rw [← tautologicalPoint_mulByIntPullback W hm, ← tautologicalPoint_mulByIntPullback W hn,
        ← mulByIntIsogeny_pullback, ← mulByIntIsogeny_pullback, h]
    exact _root_.WeierstrassCurve.Affine.zsmul_genericPoint_injective W hgen
  · rintro rfl
    rfl

/-- **`[m] = [n]` exactly when `m = n`, for nonzero `m` and `n`**, the non-vanishing hypotheses
discharged from the discriminant as in `mulByIntIsogenyOfNeZero`. -/
-- Not `@[simp]`, for the reason recorded at `mulByIntIsogenyOfNeZero_one`.
theorem mulByIntIsogenyOfNeZero_inj {m n : ℤ} (hm : m ≠ 0) (hn : n ≠ 0) :
    mulByIntIsogenyOfNeZero W hm = mulByIntIsogenyOfNeZero W hn ↔ m = n :=
  mulByIntIsogeny_inj W _ _

end Isogeny

end TauCeti

end

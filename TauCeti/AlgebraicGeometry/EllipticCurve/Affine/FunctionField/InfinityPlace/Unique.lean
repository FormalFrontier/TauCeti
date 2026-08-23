/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.InfinityPlace.Basic
-- Proof-only: Mathlib's evaluation of a valuation of `F(x)` with `v X > 1` is used inside
-- `val_algebraMap_eq_zpow_intDegree`; no statement here mentions Ostrowski's theorem.
import Mathlib.NumberTheory.RatFunc.Ostrowski

/-!
# The place at infinity is the only place of `F(W)` where `x` has a pole

`FunctionField/InfinityPlace/Basic.lean` builds the valuation `W.infinityPlace` of the function
field of an affine Weierstrass curve and computes `v_∞ x = exp 2`, so `x` has a pole there. This
file proves the converse, and with it the uniqueness of that place: **a valuation of `F(W)` which
is trivial on `F` and gives `x` a value greater than `1` is equivalent to `W.infinityPlace`.**
Equivalence of valuations is the right conclusion — the hypothesis does not see the value group,
and a valuation is only ever determined up to equivalence by its valuation ring.

The route has three steps, and none of them needs a Riemann–Roch theorem or a normalisation.

* **On the rational functions the values are forced.** Restricting `v` along
  `F(x) → F(W)` gives a valuation of `F(x)`, trivial on `F`, with `v x > 1`; Mathlib's Ostrowski
  file evaluates such a valuation outright, `v A = (v x) ^ A.intDegree`
  (`RatFunc.valuation_eq_valuation_X_zpow_intDegree_of_one_lt_valuation_X`). So the pole order of a
  rational function is its degree, for `v` and for `v_∞` alike.
* **The Weierstrass equation fixes `v y`.** Reading `y (y + a₁x + a₃) = x³ + a₂x² + a₄x + a₆`
  through `v`, the cubic on the right has value `(v x) ^ 3` by the previous step, while the left
  factor `y + a₁x + a₃` has value `max (v y) (v x)`; a value of `y` at most `v x` would make the
  left-hand side at most `(v x) ^ 2`. Hence `v x < v y` and `(v y) ^ 2 = (v x) ^ 3`. This is the
  familiar `ord_∞ x = -2`, `ord_∞ y = -3` — but as a *consequence* of `v x > 1`, over any value
  group, so it is available before the place is known.
* **Every function is `A + B y` and the two terms never cancel.** `F(W)` is spanned by `1` and `y`
  over `F(x)`, so a function is `A + B y` with `A, B` rational. Squaring, the two values are
  `(v x) ^ (2 · deg A)` and `(v x) ^ (2 · deg B + 3)`, whose exponents differ in parity, so they
  are never equal and the valuation of the sum is the larger of the two. Hence
  `v (A + B y) ≤ 1` holds exactly when `deg A ≤ 0` and `2 · deg B + 3 ≤ 0` — a condition on two
  integers with no mention of `v`. Two valuations satisfying the hypothesis therefore have the
  same integers, so they are equivalent.

## Main results

* `WeierstrassCurve.Affine.isEquiv_infinityPlace_of_one_lt`: **the uniqueness theorem** — a
  valuation of `F(W)` trivial on `F` at which `x` has a pole is equivalent to `W.infinityPlace`.
* `WeierstrassCurve.Affine.val_algebraMap_eq_zpow_intDegree` and
  `WeierstrassCurve.Affine.val_algebraMap_eq_pow_natDegree`: the value of a rational function, and
  of a polynomial, in `x`, as a power of `v x`; `val_algebraMap_le_pow` is the bound that also
  covers the zero polynomial.
* `WeierstrassCurve.Affine.val_X_lt_val_mk_Y` and `WeierstrassCurve.Affine.val_mk_Y_sq`:
  `v x < v y` and
  `(v y) ^ 2 = (v x) ^ 3` — the pole orders `2` and `3`, for any such `v`.
* `WeierstrassCurve.Affine.val_add_mul_mk_Y_le_one_iff`: the criterion the theorem is proved by,
  worth stating because it computes the valuation ring of every such `v` in closed form.
* `WeierstrassCurve.Affine.exists_ratFunc_add_mul_mk_Y`: every function is `A + B y` with `A` and
  `B` rational — the spanning half of the quadratic extension, in the form these arguments use.
* `WeierstrassCurve.Affine.mk_Y_mul_add_eq`: the Weierstrass equation, read in the function field.
* `WeierstrassCurve.Affine.one_lt_infinityPlace_X`: `1 < v_∞ x`, the instance of the hypothesis
  that `W.infinityPlace` itself satisfies.

The hypotheses are exactly `v.IsTrivialOn F` and `1 < v x`: no ellipticity, no nonsingularity, no
perfect or algebraically closed base field, and no Dedekind hypothesis on the coordinate ring. The
Weierstrass equation is the only geometry used, and it holds for singular cubics too.

## What is deliberately not here

**The affine-place classification.** The complementary case `v x ≤ 1` requires the coordinate
ring, whereas this file uses only the Weierstrass equation. The downstream file
`Affine/FunctionField/PointPlace.lean` proves that case with the generic affine-model place API,
packages the infinity valuation as `TauCeti.Place.infinity`, and combines both cases into the
point--place dictionary.

**No divisor group.** The downstream point--place file supplies a unified normalized place type
and its degree. Building divisors as finite formal sums of all such places remains separate work.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, **Layer 0** (the function field, places, and divisors).
Its §Places asks for "the places of `W.FunctionField` over `K`" with `W.infinityPlace` singled out
as the one place beyond the affine ones; this is the statement that pins it down, and it is what
turns a valuation produced by some construction — the restriction of `v_∞` along an isogeny, in
`Isogeny/InfinityPlace.lean` — into *the* place at infinity. The dual-isogeny milestone of Layer 1
names that step: "an unpointed induced-place map for finite function-field embeddings, with the
named criterion `MapsInfinity λ ↔ λ_*(O₂) = O₃`".

## Provenance

Not a port, and no code from an external formalisation is copied or adapted here. The one
substantial input is Mathlib's
`RatFunc.valuation_eq_valuation_X_zpow_intDegree_of_one_lt_valuation_X` (María Inés de
Frutos-Fernández, Xavier Généreux, from the Ostrowski file for `K(X)`), which does
the rational-function half; the rest is the Weierstrass equation and the quadratic extension.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, I.1–I.2.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.
-/

public section

open Polynomial WeierstrassCurve

open scoped Polynomial.Bivariate RatFunc

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
  {W : WeierstrassCurve.Affine F} (v : Valuation W.FunctionField Γ)

/-- The restriction of `v` to the rational function field values `X` at `v x`. -/
private theorem comap_ratFuncX :
    (v.comap (algebraMap (RatFunc F) W.FunctionField)) RatFunc.X
      = v (algebraMap F[X] W.FunctionField Polynomial.X) := by
  rw [Valuation.comap_apply, ← RatFunc.algebraMap_X,
    ← IsScalarTower.algebraMap_apply F[X] (RatFunc F) W.FunctionField]

section Trivial

variable [v.IsTrivialOn F]

/-- The restriction of `v` to the rational function field is again trivial on the base field. -/
private instance : (v.comap (algebraMap (RatFunc F) W.FunctionField)).IsTrivialOn F where
  eq_one c hc := by
    rw [Valuation.comap_apply, ← IsScalarTower.algebraMap_apply F (RatFunc F) W.FunctionField]
    exact Valuation.IsTrivialOn.eq_one c hc

variable (hx : 1 < v (algebraMap F[X] W.FunctionField Polynomial.X))

include hx

/-- **A rational function in `x` is valued at its degree**: `v A = (v x) ^ deg A`. This is
Mathlib's evaluation of a valuation of `F(x)` with `v X > 1`, restricted along `F(x) → F(W)`. -/
theorem val_algebraMap_eq_zpow_intDegree {A : RatFunc F} (hA : A ≠ 0) :
    v (algebraMap (RatFunc F) W.FunctionField A)
      = v (algebraMap F[X] W.FunctionField Polynomial.X) ^ A.intDegree := by
  have h := RatFunc.valuation_eq_valuation_X_zpow_intDegree_of_one_lt_valuation_X
    (v := v.comap (algebraMap (RatFunc F) W.FunctionField)) (by rw [comap_ratFuncX]; exact hx) hA
  rwa [Valuation.comap_apply, comap_ratFuncX] at h

/-- **A polynomial in `x` is valued at its degree**: `v p = (v x) ^ natDegree p`. -/
theorem val_algebraMap_eq_pow_natDegree {p : F[X]} (hp : p ≠ 0) :
    v (algebraMap F[X] W.FunctionField p)
      = v (algebraMap F[X] W.FunctionField Polynomial.X) ^ p.natDegree := by
  have hA : algebraMap F[X] (RatFunc F) p ≠ 0 :=
    fun h ↦ hp (FaithfulSMul.algebraMap_injective F[X] (RatFunc F) (by simpa using h))
  have := val_algebraMap_eq_zpow_intDegree v hx hA
  rw [← IsScalarTower.algebraMap_apply F[X] (RatFunc F) W.FunctionField,
    RatFunc.intDegree_polynomial, zpow_natCast] at this
  exact this

/-- The degree bound form, which also covers `p = 0`: a polynomial of degree at most `n` in `x`
has value at most `(v x) ^ n`. -/
theorem val_algebraMap_le_pow {p : F[X]} {n : ℕ} (hp : p.natDegree ≤ n) :
    v (algebraMap F[X] W.FunctionField p)
      ≤ v (algebraMap F[X] W.FunctionField Polynomial.X) ^ n := by
  rcases eq_or_ne p 0 with rfl | hp0
  · simp
  · rw [val_algebraMap_eq_pow_natDegree v hx hp0]
    exact pow_le_pow_right₀ hx.le hp

end Trivial

section Relation

variable (W)

/-- `AdjoinRoot.mk_C` in the `algebraMap` spelling the rewrite below wants. (`CoordinateRing.lean`
carries a private lemma of the same shape; neither file exports one, and importing that file here
for a one-line wrapper around a Mathlib lemma would pull in the Dedekind development.) -/
private theorem coordinateRing_mk_C (p : F[X]) :
    CoordinateRing.mk W (Polynomial.C p) = algebraMap F[X] W.CoordinateRing p :=
  AdjoinRoot.mk_C p

/-- **The Weierstrass equation, in the function field**:
`y * (y + (a₁X + a₃)) = X³ + a₂X² + a₄X + a₆`. Grouping the two left-hand terms as a product is
what makes the valuation of the left-hand side a product of two values, which is how the pole
orders of `x` and `y` are compared below. -/
theorem mk_Y_mul_add_eq :
    algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y) *
        (algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y)
          + algebraMap F[X] W.FunctionField (Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃))
      = algebraMap F[X] W.FunctionField
          (Polynomial.X ^ 3 + Polynomial.C W.a₂ * Polynomial.X ^ 2
            + Polynomial.C W.a₄ * Polynomial.X + Polynomial.C W.a₆) := by
  have hY : CoordinateRing.mk W Y * (CoordinateRing.mk W Y
      + algebraMap F[X] W.CoordinateRing (Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃))
      = algebraMap F[X] W.CoordinateRing (Polynomial.X ^ 3 + Polynomial.C W.a₂ * Polynomial.X ^ 2
          + Polynomial.C W.a₄ * Polynomial.X + Polynomial.C W.a₆) := by
    rw [← coordinateRing_mk_C, ← coordinateRing_mk_C, ← map_add, ← map_mul]
    exact AdjoinRoot.mk_eq_mk.mpr ⟨1, by rw [polynomial]; ring1⟩
  rw [IsScalarTower.algebraMap_apply F[X] W.CoordinateRing W.FunctionField,
    IsScalarTower.algebraMap_apply F[X] W.CoordinateRing W.FunctionField, ← map_add, ← map_mul, hY]

end Relation

section Decompose

variable (W)

/-- **Every function is `A + B y` with `A` and `B` rational functions of `x`.** Clearing a
polynomial denominator reduces to the coordinate ring, where Mathlib's basis `{1, Y}` supplies the
decomposition. -/
theorem exists_ratFunc_add_mul_mk_Y (z : W.FunctionField) :
    ∃ A B : RatFunc F, algebraMap (RatFunc F) W.FunctionField A
      + algebraMap (RatFunc F) W.FunctionField B *
        algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y) = z := by
  -- Write `z` over a polynomial denominator, and decompose its numerator on the basis `{1, Y}`.
  obtain ⟨⟨u, ⟨-, p, hp, rfl⟩⟩, h⟩ := IsLocalization.surj
    (Algebra.algebraMapSubmonoid W.CoordinateRing (nonZeroDivisors F[X])) z
  obtain ⟨a, b, rfl⟩ := CoordinateRing.exists_smul_basis_eq u
  have hp0 : algebraMap F[X] W.FunctionField p ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective F[X] W.FunctionField)).2
      (nonZeroDivisors.ne_zero hp)
  rw [← IsScalarTower.algebraMap_apply F[X] W.CoordinateRing W.FunctionField, Algebra.smul_def,
    Algebra.smul_def, map_add, map_mul, map_mul, map_one, mul_one,
    ← IsScalarTower.algebraMap_apply F[X] W.CoordinateRing W.FunctionField,
    ← IsScalarTower.algebraMap_apply F[X] W.CoordinateRing W.FunctionField] at h
  refine ⟨algebraMap F[X] (RatFunc F) a / algebraMap F[X] (RatFunc F) p,
    algebraMap F[X] (RatFunc F) b / algebraMap F[X] (RatFunc F) p, ?_⟩
  rw [map_div₀, map_div₀, ← IsScalarTower.algebraMap_apply F[X] (RatFunc F) W.FunctionField,
    ← IsScalarTower.algebraMap_apply F[X] (RatFunc F) W.FunctionField,
    ← IsScalarTower.algebraMap_apply F[X] (RatFunc F) W.FunctionField]
  field_simp
  linear_combination -h

end Decompose

section PoleOrders

variable [v.IsTrivialOn F]
  (hx : 1 < v (algebraMap F[X] W.FunctionField Polynomial.X))

include hx

/-- The Weierstrass equation, valued: the left-hand product has value `(v x) ^ 3`. -/
private theorem val_mul_val_add :
    v (algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y)) *
        v (algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y)
          + algebraMap F[X] W.FunctionField (Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃))
      = v (algebraMap F[X] W.FunctionField Polynomial.X) ^ 3 := by
  have hP : (Polynomial.X ^ 3 + Polynomial.C W.a₂ * Polynomial.X ^ 2
      + Polynomial.C W.a₄ * Polynomial.X + Polynomial.C W.a₆ : F[X]).natDegree = 3 := by
    compute_degree!
  rw [← map_mul, mk_Y_mul_add_eq, val_algebraMap_eq_pow_natDegree v hx (p := _) (by
    intro h; rw [h, Polynomial.natDegree_zero] at hP; omega), hP]

/-- The linear coefficient `a₁X + a₃` has value at most `v x`. -/
private theorem val_add_le :
    v (algebraMap F[X] W.FunctionField (Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃))
      ≤ v (algebraMap F[X] W.FunctionField Polynomial.X) := by
  have : (Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃ : F[X]).natDegree ≤ 1 := by
    compute_degree
  simpa using val_algebraMap_le_pow v hx this

/-- **`y` has a higher pole than `x`.** If `v y ≤ v x` then the left-hand side of the Weierstrass
equation has value at most `(v x) ^ 2`, while its right-hand side has value `(v x) ^ 3`. -/
theorem val_X_lt_val_mk_Y :
    v (algebraMap F[X] W.FunctionField Polynomial.X)
      < v (algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y)) := by
  by_contra hle
  rw [not_lt] at hle
  have h1 := (v.map_add (algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y))
    (algebraMap F[X] W.FunctionField
      (Polynomial.C W.a₁ * Polynomial.X + Polynomial.C W.a₃))).trans
    (max_le hle (val_add_le v hx))
  have h2 := val_mul_val_add v hx
  have h3 : v (algebraMap F[X] W.FunctionField Polynomial.X) ^ 3
      ≤ v (algebraMap F[X] W.FunctionField Polynomial.X) ^ 2 := by
    rw [← h2, sq]
    exact mul_le_mul' hle h1
  exact absurd h3 (not_le.mpr (pow_lt_pow_right₀ hx (by norm_num)))

/-- **The pole orders of `x` and `y` are in the ratio `2 : 3`**: `(v y) ^ 2 = (v x) ^ 3`. Once
`v x < v y` is known, the second factor of the Weierstrass equation has value `v y`. -/
theorem val_mk_Y_sq :
    v (algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y)) ^ 2
      = v (algebraMap F[X] W.FunctionField Polynomial.X) ^ 3 := by
  rw [sq, ← val_mul_val_add v hx]
  congr 1
  exact (v.map_add_eq_of_lt_left ((val_add_le v hx).trans_lt (val_X_lt_val_mk_Y v hx))).symm

omit [v.IsTrivialOn F] in
/-- `v x` is a unit of the value group, being larger than `1`. -/
private theorem ne_zero_val_X : v (algebraMap F[X] W.FunctionField Polynomial.X) ≠ 0 :=
  (zero_lt_one.trans hx).ne'

/-- The square of the value of `B y` is `(v x) ^ (2 deg B + 3)`: an odd power, where the square of
the value of a rational function is an even one. -/
private theorem val_mul_mk_Y_sq {B : RatFunc F} (hB : B ≠ 0) :
    v (algebraMap (RatFunc F) W.FunctionField B *
        algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y)) ^ 2
      = v (algebraMap F[X] W.FunctionField Polynomial.X) ^ (2 * B.intDegree + 3) := by
  rw [map_mul, mul_pow, val_algebraMap_eq_zpow_intDegree v hx hB, val_mk_Y_sq v hx,
    ← zpow_natCast (v (algebraMap F[X] W.FunctionField Polynomial.X)) 3,
    ← zpow_natCast (v (algebraMap F[X] W.FunctionField Polynomial.X) ^ B.intDegree) 2,
    ← zpow_mul, ← zpow_add₀ (ne_zero_val_X v hx)]
  congr 1
  push_cast
  ring

/-- `B y` lies in the valuation ring exactly when `2 deg B + 3 ≤ 0`. -/
private theorem val_mul_mk_Y_le_one_iff {B : RatFunc F} (hB : B ≠ 0) :
    v (algebraMap (RatFunc F) W.FunctionField B *
        algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y)) ≤ 1
      ↔ 2 * B.intDegree + 3 ≤ 0 := by
  rw [← sq_le_one_iff₀ zero_le, val_mul_mk_Y_sq v hx hB, zpow_le_one_iff_right₀ hx]

/-- A rational function of `x` lies in the valuation ring exactly when its degree is at most
`0`. -/
private theorem val_algebraMap_le_one_iff {A : RatFunc F} (hA : A ≠ 0) :
    v (algebraMap (RatFunc F) W.FunctionField A) ≤ 1 ↔ A.intDegree ≤ 0 := by
  rw [val_algebraMap_eq_zpow_intDegree v hx hA, zpow_le_one_iff_right₀ hx]

/-- **The valuation ring of `v`, in closed form**: `A + B y` lies in it exactly when
`deg A ≤ 0` and `2 deg B + 3 ≤ 0`. The two summands never have the same value — after squaring,
their exponents have opposite parities — so the valuation of the sum is the larger of the two, and
the resulting condition mentions `v` nowhere. -/
theorem val_add_mul_mk_Y_le_one_iff (A B : RatFunc F) :
    v (algebraMap (RatFunc F) W.FunctionField A
        + algebraMap (RatFunc F) W.FunctionField B *
          algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y)) ≤ 1
      ↔ (A = 0 ∨ A.intDegree ≤ 0) ∧ (B = 0 ∨ 2 * B.intDegree + 3 ≤ 0) := by
  rcases eq_or_ne A 0 with rfl | hA
  · rcases eq_or_ne B 0 with rfl | hB
    · simp
    · simpa [hB] using val_mul_mk_Y_le_one_iff v hx hB
  · rcases eq_or_ne B 0 with rfl | hB
    · simpa [hA] using val_algebraMap_le_one_iff v hx hA
    · have hne : v (algebraMap (RatFunc F) W.FunctionField A)
          ≠ v (algebraMap (RatFunc F) W.FunctionField B *
            algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W Y)) := by
        intro heq
        have hsq : v (algebraMap F[X] W.FunctionField Polynomial.X) ^ (2 * A.intDegree)
            = v (algebraMap F[X] W.FunctionField Polynomial.X) ^ (2 * B.intDegree + 3) := by
          rw [← val_mul_mk_Y_sq v hx hB, ← heq, val_algebraMap_eq_zpow_intDegree v hx hA,
            ← zpow_natCast (v (algebraMap F[X] W.FunctionField Polynomial.X) ^ A.intDegree) 2,
            ← zpow_mul]
          congr 1
          push_cast
          ring
        have := zpow_right_injective₀ (zero_lt_one.trans hx) hx.ne' hsq
        omega
      rw [v.map_add_of_distinct_val hne, max_le_iff, val_algebraMap_le_one_iff v hx hA,
        val_mul_mk_Y_le_one_iff v hx hB]
      simp [hA, hB]

end PoleOrders

section Main

variable (W)

/-- **`x` has a pole at the place at infinity**: `1 < v_∞ x`, since `v_∞ x = exp 2`. This is the
instance of the uniqueness theorem's hypothesis satisfied by `W.infinityPlace` itself. -/
theorem one_lt_infinityPlace_X :
    1 < infinityPlace W (algebraMap F[X] W.FunctionField Polynomial.X) := by
  rw [IsScalarTower.algebraMap_apply F[X] W.CoordinateRing W.FunctionField, infinityPlace.X,
    ← WithZero.exp_zero]
  exact WithZero.exp_lt_exp.2 (by norm_num)

variable {W}

/-- **The place at infinity is the only place of `F(W)` at which `x` has a pole**: a valuation of
the function field which is trivial on the base field and satisfies `1 < v x` is equivalent to
`W.infinityPlace`. Both valuations satisfy `val_add_mul_mk_Y_le_one_iff`, whose right-hand side is
a condition on two integers, so their valuation rings agree. -/
theorem isEquiv_infinityPlace_of_one_lt [v.IsTrivialOn F]
    (hx : 1 < v (algebraMap F[X] W.FunctionField Polynomial.X)) :
    v.IsEquiv (infinityPlace W) := by
  refine Valuation.isEquiv_iff_val_le_one.mpr fun {z} ↦ ?_
  obtain ⟨A, B, rfl⟩ := exists_ratFunc_add_mul_mk_Y W z
  rw [val_add_mul_mk_Y_le_one_iff v hx, val_add_mul_mk_Y_le_one_iff _ (one_lt_infinityPlace_X W)]

end Main

end WeierstrassCurve.Affine

end

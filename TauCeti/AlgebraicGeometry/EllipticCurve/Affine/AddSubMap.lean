/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.AddSubMap

/-!
# The addition-and-subtraction map on symmetric `x`-coordinates

Mathlib defines `sym2x P Q`, the symmetric function of the two `x`-coordinates recording the
unordered pair `{P, Q}`, and the quadratic map `addSubMap` that should induce
`{P, Q} ↦ {P + Q, P - Q}` on it. This file proves that it does — up to a nonzero scalar, which
is all a projective statement can assert, and all a scale-invariant height needs.

No height appears here; the consumer is
`TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.NaiveHeight`.

## Main results

* `WeierstrassCurve.Affine.Point.sym2x_eq_xRep` : `sym2x` in projective `xRep` coordinates.
* `WeierstrassCurve.Affine.Point.exists_smul_sym2x_add_sub_eq_addSubMap_sym2x` : there is a
  nonzero `t` with `t • sym2x (P + Q) (P - Q) = addSubMap W ∘ sym2x P Q`.

## Relation to Mathlib

Mathlib's `sym2x`, `addSubMap`, `addSubMapCoeff` and `isHomogeneous_addSubMap` are *consumed*, not
restated. The declarations here are absent from Mathlib at the version this repository pins: the
source brackets this material with a reference to Mathlib PR `#40303`, and
`Mathlib/NumberTheory/Height/EllipticCurve.lean` — by the same author — carries a `TODO` naming
this scope. This is a deliberate, temporary duplication with a defined end: if a later pin bump
lands that upstream work, the superseded declarations here must be deleted and their uses
repointed at Mathlib in the same pull request, per this repository's no-compatibility-shims rule.

## References

* [M. Stoll, *EllipticCurves*](https://github.com/MichaelStollBayreuth/EllipticCurves), commit
  `66889eada51a74c2f5dfb7fb5909b0b5a0a2d96e`, `EllipticCurves/MordellWeil.lean`, Apache-2.0.
-/

public section

open MvPolynomial Nat

namespace WeierstrassCurve

namespace Affine

variable {F : Type*} [Field F] {W : Affine F}

/-! ### `sym2x` and the addition-and-subtraction map -/

/-- `sym2x` written out in the projective `xRep` coordinates.

Public, and stated rather than unfolded, because Mathlib's `sym2x` is **not exposed**:
`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/AddSubMap.lean` opens a plain `public section`, so
across the module boundary the body is unavailable and both `simp [Point.sym2x]` and
`rw [Point.sym2x]` are rejected outright — `Invalid simp theorem \`sym2x\`: Expected a definition
with an exposed body`, and `Invalid rewrite argument`. Mathlib exports only the four
per-constructor `@[simp]` lemmas, so the general equation is recovered here by matching on those
four cases.

It is the *coordinate bridge*, not a competing spelling of `sym2x`: the canonical definition
remains Mathlib's. It is exported rather than kept `private` because the commuting square below
and the height bound in `TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.NaiveHeight` both
need it, `private` does not cross a module boundary, and the placement review asked for exactly
this ("expose or locally restate only the coordinate bridge needed by the height bound"). -/
lemma Point.sym2x_eq_xRep (P Q : W.Point) :
    P.sym2x Q = ![P.xRep 0 * Q.xRep 0, P.xRep 0 * Q.xRep 1 + P.xRep 1 * Q.xRep 0,
      P.xRep 1 * Q.xRep 1] := by
  match P, Q with
  | 0, 0 => simp [Point.xRep_zero]
  | 0, .some x y h => simp [Point.xRep_zero, Point.xRep_some]
  | .some x y h, 0 => simp [Point.xRep_zero, Point.xRep_some]
  | .some x y h, .some x' y' h' => simp [Point.xRep_some]

private lemma Point.sym2x_P_P_eq_addSubMap (P : W.Point) :
    sym2x P P = fun i ↦ (addSubMap W i).eval <| P.sym2x 0 := by
  match P with
  | 0 =>
    simp only [sym2x_zero_zero, succ_eq_add_one, reduceAdd, addSubMap, Fin.isValue]
    ext i : 1
    fin_cases i <;> simp
  | some .. =>
    simp only [sym2x_some_some, succ_eq_add_one, reduceAdd, sym2x_some_zero, addSubMap, Fin.isValue]
    ext i : 1
    fin_cases i <;> simp [pow_two, two_mul]

section Decidable

variable [DecidableEq F]

private lemma Point.sym2x_P_add_P_zero (P : W.Point) :
    ∃ t : F, t ≠ 0 ∧ t • sym2x (P + P) 0 = fun i ↦ (addSubMap W i).eval <| P.sym2x P := by
  match P with
  | 0 =>
    refine ⟨1, one_ne_zero, ?_⟩
    rw [add_zero, sym2x_zero_zero, one_smul, addSubMap]
    ext i : 1
    fin_cases i <;> simp
  | some x y h =>
    have Hrs : (fun i ↦ (addSubMap W i).eval <| (some x y h).sym2x (some x y h)) =
          ![x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈,
            4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆, 0] := by
      ext i : 1
      fin_cases i <;> simp [addSubMap] <;> ring
    rw [Hrs]
    by_cases! H : y = W.negY x y
    · have H' := (den_duplication_eq_zero_iff h.1).mpr H
      rw [H', add_self_of_Y_eq H, sym2x_zero_zero]
      refine ⟨_, den_duplication_ne_zero_or_num_duplication_ne_zero h |>.neg_resolve_left H', ?_⟩
      simp
    · have H' := (den_duplication_eq_zero_iff h.1).not.mpr H
      refine ⟨_, H', ?_⟩
      simp [Point.sym2x_eq_xRep, Point.xRep_add_self_of_Y_ne h H, mul_div_cancel₀ _ H']

/-- `sym2x (P + Q) (P - Q)` is equal, up to scaling by a nonzero constant, to `addSubMap W`
applied to `sym2x P Q`. -/
lemma Point.exists_smul_sym2x_add_sub_eq_addSubMap_sym2x (P Q : W.Point) :
    ∃ t : F, t ≠ 0 ∧ t • sym2x (P + Q) (P - Q) = fun i ↦ (addSubMap W i).eval <| sym2x P Q := by
  rcases eq_or_ne P Q with rfl | hPQ
  · simpa using P.sym2x_P_add_P_zero
  rcases eq_or_ne Q (-P) with rfl | hPQ'
  · simpa [sym2x_neg_right, Point.sym2x_comm 0] using P.sym2x_P_add_P_zero
  match P, Q with
  | P, 0 =>  exact ⟨1, one_ne_zero, by simpa using P.sym2x_P_P_eq_addSubMap⟩
  | 0, Q =>
    refine ⟨1, one_ne_zero, ?_⟩
    simpa [sym2x_neg_right, sym2x_comm _ Q] using Q.sym2x_P_P_eq_addSubMap
  | some xP yP hP, some xQ yQ hQ =>
    have hxPQ : xP ≠ xQ := fun Heq ↦ by grind only [X_eq_iff.mp Heq]
    have Hrs : (fun i ↦ (addSubMap W i).eval <| (some xP yP hP).sym2x (some xQ yQ hQ)) =
        ![(xP * xQ) ^ 2 - W.b₄ * (xP * xQ) - W.b₆ * (xP + xQ) - W.b₈,
          2 * (xP + xQ) * (xP * xQ) + W.b₂ * (xP * xQ) + W.b₄ * (xP + xQ) + W.b₆,
          (xP - xQ) ^ 2] := by
      ext i : 1
      fin_cases i <;> simp [addSubMap]
      ring
    have : xP - xQ ≠ 0 := sub_ne_zero_of_ne hxPQ
    refine ⟨(xP - xQ) ^ 2, pow_ne_zero 2 this, ?_⟩
    -- The following relations are needed for the `grobner` calls below.
    have HeqP := (W.equation_iff xP yP).mp hP.1
    have HeqQ := (W.equation_iff xQ yQ).mp hQ.1
    rw [Hrs, Point.sym2x_eq_xRep, Point.xRep_add_of_X_ne hP hQ hxPQ,
      Point.xRep_sub_of_X_ne hP hQ hxPQ,
      b₂, b₄, b₆, b₈]
    ext i : 1
    fin_cases i <;> simp [field] <;> grobner

end Decidable

end Affine

end WeierstrassCurve

end

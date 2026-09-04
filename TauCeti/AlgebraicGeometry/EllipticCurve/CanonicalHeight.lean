/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.NaiveHeight

/-!
# The canonical (Néron–Tate) height

The naïve height `h` is quadratic only up to a bounded error: `approx_parallelogram_law` gives a
constant `C` with `|h(P + Q) + h(P - Q) - 2(h P + h Q)| ≤ C`. Tate's observation is that averaging
that error away along the doubling map removes it. This file carries
out that construction and records the facts that pin the definition down: the limit exists, it
stays within a bounded distance of half of `h`, and it takes the expected values at `0` and under
negation. That the result is *honestly* quadratic — the exact parallelogram law — is a separate
theorem and is not established in this file.

`canonicalHeight P = (1/2) · lim_{n → ∞} h(2ⁿ P) / 4ⁿ`

The factor `1/2` is the standard normalisation and is not cosmetic. The naïve height here is the
height of the `x`-coordinate, and `x` has a *double* pole at the point at infinity, so `h_x` is the
height attached to the divisor `2(O)`. Heights scale linearly in the divisor, so the height
attached to `(O)` — the one the Néron–Tate pairing, the regulator and the BSD formula are stated
with — is half of it. Getting this wrong would scale every later invariant.

## Main definitions

* `WeierstrassCurve.Affine.Point.canonicalHeight`: the limit above.

## Main results

* `WeierstrassCurve.Affine.Point.tendsto_naiveHeight_two_pow_nsmul_div_four_pow`: the defining
  limit is attained, so `canonicalHeight` is the limit and not the junk value `limUnder`
  returns when a sequence does not converge. Properties that genuinely need passage to the limit
  are proved by transporting a property of `h` along this; the values at `0` and under negation
  do not, and are proved termwise instead.
* `WeierstrassCurve.Affine.Point.canonicalHeight_zero` and
  `WeierstrassCurve.Affine.Point.canonicalHeight_neg`: its values at the two points every consumer
  meets first, as `@[simp]` normal forms.
* `WeierstrassCurve.Affine.Point.abs_canonicalHeight_sub_naiveHeight_le`: the canonical height stays
  within a bounded distance of *half* the naïve one, by a
  constant depending only on the curve. This is what makes the two interchangeable in
  finiteness arguments — in particular Northcott finiteness transfers to it.

## Implementation notes

The doubling bound `|h(2P) - 4 h(P)| ≤ C` is the parallelogram law at `Q = P`, where `P - Q = 0`
and `h(0) = 0`. Only that specialisation is used here, so it is kept private.

Convergence is `cauchySeq_of_le_geometric` at ratio `1/4`: consecutive terms of
`h(2ⁿ P) / (2 · 4ⁿ)` differ by
`|h(2 · 2ⁿ P) - 4 h(2ⁿ P)| / (2 · 4ⁿ⁺¹) ≤ C / (2 · 4ⁿ⁺¹) = (C/8) · (1/4)ⁿ`. The same estimate
feeds Mathlib's
`dist_le_of_le_geometric_of_tendsto₀`, which bounds the distance from the *zeroth* term — and the
zeroth term is `h(P) / 2` — giving `|canonicalHeight P - h(P)/2| ≤ (C / 8) / (1 - 1/4) = C / 6`
with no further work.

The `[DecidableEq F]` hypothesis is not incidental: `W.Point`'s `AddCommGroup` instance needs it,
since the addition formula case-splits on whether the two points share an `x`-coordinate. Without
it `2 ^ n • P` does not elaborate.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VIII.9.
-/

public section

open Filter Height Topology

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F} [AdmissibleAbsValues F] [DecidableEq F]

/-- **The canonical (Néron–Tate) height** `canonicalHeight P = lim h(2ⁿ P) / (2 · 4ⁿ)`.

The `2` is the standard normalisation: `h` is the height of the `x`-coordinate, which has a double
pole at infinity, so `h` is attached to `2(O)` and the Néron–Tate height to `(O)` is half of it.

The limit exists whenever the curve is elliptic
(`Point.tendsto_naiveHeight_two_pow_nsmul_div_four_pow`); the definition itself needs no hypothesis
beyond those making `2 ^ n • P` meaningful, so it is stated without one. -/
noncomputable def Point.canonicalHeight (P : W.Point) : ℝ :=
  limUnder atTop fun n : ℕ ↦ ((2 ^ n) • P).naiveHeight / (2 * 4 ^ n)

variable (W) in
/-- The parallelogram law at `Q = P`: doubling multiplies the naïve height by `4` up to a bounded
error. The constant is nonnegative, which the geometric estimate below needs. -/
private theorem exists_abs_naiveHeight_two_nsmul_sub [W.toAffine.IsElliptic] :
    ∃ C, 0 ≤ C ∧ ∀ P : W.Point, |(2 • P).naiveHeight - 4 * P.naiveHeight| ≤ C := by
  obtain ⟨C, hC⟩ := approx_parallelogram_law W
  refine ⟨C, le_trans (abs_nonneg _) (hC 0 0), fun P ↦ ?_⟩
  have h := hC P P
  -- `P - P = 0` and `h 0 = 0`, so the law collapses to the doubling statement.
  rw [sub_self, Point.naiveHeight_zero] at h
  rw [two_nsmul]
  convert h using 2
  ring

/-- Consecutive terms of `h(2ⁿ P) / (2 · 4ⁿ)` differ geometrically at ratio `1/4`, by
`(C/8) · (1/4)ⁿ`. This is the single estimate both results below run on. -/
private theorem dist_naiveHeight_div_succ_le {C : ℝ}
    (hC : ∀ P : W.Point, |(2 • P).naiveHeight - 4 * P.naiveHeight| ≤ C) (P : W.Point) (n : ℕ) :
    dist (((2 ^ n) • P).naiveHeight / (2 * 4 ^ n))
        (((2 ^ (n + 1)) • P).naiveHeight / (2 * 4 ^ (n + 1)))
      ≤ C / 8 * (1 / 4) ^ n := by
  have key : ((2 : ℕ) ^ (n + 1)) • P = 2 • (((2 : ℕ) ^ n) • P) := by
    rw [smul_smul]; congr 1; ring
  have e : ((2 : ℕ) ^ n • P).naiveHeight / (2 * 4 ^ n)
        - ((2 : ℕ) ^ (n + 1) • P).naiveHeight / (2 * 4 ^ (n + 1))
      = (4 * ((2 : ℕ) ^ n • P).naiveHeight - (2 • ((2 : ℕ) ^ n • P)).naiveHeight)
          / (2 * 4 ^ (n + 1)) := by
    rw [key]; field_simp [pow_succ]; ring
  rw [Real.dist_eq, e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * 4 ^ (n + 1)),
    div_le_iff₀ (by positivity : (0 : ℝ) < 2 * 4 ^ (n + 1))]
  have h := hC ((2 : ℕ) ^ n • P)
  rw [abs_sub_comm] at h
  calc |4 * ((2 : ℕ) ^ n • P).naiveHeight - (2 • ((2 : ℕ) ^ n • P)).naiveHeight| ≤ C := h
    _ = C / 8 * (1 / 4 : ℝ) ^ n * (2 * 4 ^ (n + 1)) := by
        have h1 : ((1 : ℝ) / 4) ^ n * 4 ^ n = 1 := by rw [← mul_pow]; norm_num
        linear_combination (-C) * h1

/-- **The defining limit is attained.** `canonicalHeight` is `limUnder`, which returns a junk value
on a divergent sequence; this says the sequence converges, so the definition means what it says. -/
theorem Point.tendsto_naiveHeight_two_pow_nsmul_div_four_pow [W.toAffine.IsElliptic] (P : W.Point) :
    Tendsto (fun n : ℕ ↦ ((2 ^ n) • P).naiveHeight / (2 * 4 ^ n)) atTop
      (𝓝 P.canonicalHeight) := by
  obtain ⟨C, _, hC⟩ := exists_abs_naiveHeight_two_nsmul_sub W
  exact (cauchySeq_of_le_geometric (1 / 4) (C / 8) (by norm_num)
    (dist_naiveHeight_div_succ_le hC P)).tendsto_limUnder

/-- The point at infinity has canonical height zero: every term of the defining sequence is
`h 0 / (2 · 4 ^ n) = 0`. This is termwise, so it needs no convergence and no ellipticity. -/
@[simp]
theorem Point.canonicalHeight_zero : (0 : W.Point).canonicalHeight = 0 := by
  have h : (fun n : ℕ ↦ ((2 ^ n) • (0 : W.Point)).naiveHeight / (2 * 4 ^ n)) = fun _ ↦ 0 := by
    funext n; simp
  rw [Point.canonicalHeight, h]
  exact tendsto_const_nhds.limUnder_eq

/-- Negation preserves the canonical height, because it preserves the naïve height and commutes
with doubling, so the two defining sequences agree termwise — again with no convergence or
ellipticity needed. -/
@[simp]
theorem Point.canonicalHeight_neg (P : W.Point) :
    (-P).canonicalHeight = P.canonicalHeight := by
  have h : (fun n : ℕ ↦ ((2 ^ n) • (-P)).naiveHeight / (2 * 4 ^ n))
      = fun n : ℕ ↦ ((2 ^ n) • P).naiveHeight / (2 * 4 ^ n) := by
    funext n; rw [smul_neg, Point.naiveHeight_neg]
  rw [Point.canonicalHeight, Point.canonicalHeight, h]

/-- **The canonical height differs from half the naïve height by a bounded amount**, the bound
depending only on the curve. The half is the normalisation described in the module docstring;
Northcott finiteness for `h` transfers to the canonical height through this. -/
theorem Point.abs_canonicalHeight_sub_naiveHeight_le [W.toAffine.IsElliptic] :
    ∃ D, ∀ P : W.Point, |P.canonicalHeight - P.naiveHeight / 2| ≤ D := by
  obtain ⟨C, _, hC⟩ := exists_abs_naiveHeight_two_nsmul_sub W
  refine ⟨C / 8 / (1 - 1 / 4), fun P ↦ ?_⟩
  have hd := dist_le_of_le_geometric_of_tendsto₀ (1 / 4) (C / 8) (by norm_num)
    (dist_naiveHeight_div_succ_le hC P) (P.tendsto_naiveHeight_two_pow_nsmul_div_four_pow)
  -- the zeroth term of the sequence is `h P / 2`
  simpa [Real.dist_eq, abs_sub_comm] using hd

end WeierstrassCurve.Affine

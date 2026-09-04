/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.NaiveHeight
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import TauCeti.LinearAlgebra.End.InvertibleTwo
import TauCeti.LinearAlgebra.QuadraticForm.OfParallelogram

/-!
# The canonical (Néron–Tate) height

The naïve height `h` is quadratic only up to a bounded error: `approx_parallelogram_law` gives a
constant `C` with `|h(P + Q) + h(P - Q) - 2(h P + h Q)| ≤ C`. Tate's observation is that averaging
that error away along the doubling map removes it. This file carries
out that construction and records the facts that pin the definition down: the limit exists, it
stays within a bounded distance of half of `h`, and it takes the expected values at `0` and under
negation, and it is *honestly* quadratic — it satisfies the parallelogram law exactly, which is
what the whole averaging was for.

`canonicalHeight P = (1/2) · lim_{n → ∞} h(2ⁿ P) / 4ⁿ`

The factor `1/2` is the standard normalisation and is not cosmetic. The naïve height here is the
height of the `x`-coordinate, and `x` has a *double* pole at the point at infinity, so `h_x` is the
height attached to the divisor `2(O)`. Heights scale linearly in the divisor, so the height
attached to `(O)` — the one the Néron–Tate pairing, the regulator and the BSD formula are stated
with — is half of it. Getting this wrong would scale every later invariant.

## Main definitions

* `WeierstrassCurve.Affine.Point.canonicalHeight`: the limit above.
* `WeierstrassCurve.Affine.canonicalHeightQuadratic`: the canonical height as a `ℤ`-quadratic map
  with real values, which is the form Mathlib's polarisation API consumes.
* `WeierstrassCurve.Affine.neronTatePairing`: the **Néron–Tate pairing**, the bilinear form
  associated with that quadratic map.

## Main results

* `WeierstrassCurve.Affine.Point.tendsto_naiveHeight_two_pow_nsmul_div_four_pow`: the defining
  limit is attained, so `canonicalHeight` is the limit and not the junk value `limUnder`
  returns when a sequence does not converge. Properties that genuinely need passage to the limit
  are proved by transporting a property of `h` along this; the values at `0` and under negation
  do not, and are proved termwise instead.
* `WeierstrassCurve.Affine.Point.canonicalHeight_zero` and
  `WeierstrassCurve.Affine.Point.canonicalHeight_neg`: its values at the two points every consumer
  meets first, as `@[simp]` normal forms.
* `WeierstrassCurve.Affine.Point.canonicalHeight_parallelogram_law`: the canonical height
  satisfies the parallelogram law **exactly**, where the naïve height satisfies it only up to a
  bounded error. This is the point of the construction: it is the quadratic function the naïve
  height was approximating.
* `WeierstrassCurve.Affine.Point.canonicalHeight_two_nsmul`: the doubling normal form
  `canonicalHeight (2 • P) = 4 * canonicalHeight P`, the parallelogram law at `Q = P`.
* `WeierstrassCurve.Affine.Point.canonicalHeight_zsmul` and
  `WeierstrassCurve.Affine.Point.canonicalHeight_nsmul`: the value at `n • P` is `n ^ 2` times the
  value at `P`. This exhibits the canonical height as a quadratic form on `W.Point`; the general
  statement it specialises lives in `TauCeti/LinearAlgebra/QuadraticForm/OfParallelogram.lean`.
* `WeierstrassCurve.Affine.Point.canonicalHeight_nonneg`: it is non-negative, read off the
  defining sequence termwise.
* `WeierstrassCurve.Affine.Point.canonicalHeight_eq_zero_iff_isOfFinAddOrder`: it vanishes exactly
  on the torsion points. The two directions are also available separately, because they need
  different hypotheses: `canonicalHeight_eq_zero_of_isOfFinAddOrder` is quadraticity at a
  vanishing multiple and needs no finiteness, while `isOfFinAddOrder_of_canonicalHeight_eq_zero`
  assumes Northcott finiteness for the canonical height itself.
* `WeierstrassCurve.Affine.Point.abs_canonicalHeight_sub_naiveHeight_le`: the canonical height stays
  within a bounded distance of *half* the naïve one, by a
  constant depending only on the curve. This is what makes the two interchangeable in
  finiteness arguments — in particular Northcott finiteness transfers to it, which the `Northcott`
  instance below makes formal.
* `WeierstrassCurve.Affine.neronTatePairing_apply`: the pairing is the polarisation — its value
  at `P, Q` is half of `canonicalHeight (P + Q) - canonicalHeight P - canonicalHeight Q`.
* `WeierstrassCurve.Affine.neronTatePairing_self`: it recovers the canonical height on the
  diagonal, so the pairing and the height determine each other.
* `WeierstrassCurve.Affine.neronTatePairing_eq_zero_of_isOfFinAddOrder_left` and
  `WeierstrassCurve.Affine.neronTatePairing_eq_zero_of_isOfFinAddOrder_right`: it vanishes as soon
  as either argument is torsion, which is what lets it descend to the free quotient
  `W.Point ⧸ torsion` where the regulator is defined.
* `WeierstrassCurve.Affine.neronTatePairing_comm` and
  `WeierstrassCurve.Affine.neronTatePairing_flip`: it is symmetric, pointwise and as an equality
  of bilinear maps.

## Implementation notes

The doubling bound `|h(2P) - 4 h(P)| ≤ C` is the approximate parallelogram law at `Q = P`, where
`P - Q = 0` and `h(0) = 0`. **Convergence** needs only that specialisation, which is why it is
private; `canonicalHeight_parallelogram_law` needs the full two-point law, and takes it directly
from `approx_parallelogram_law`.

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

/-- **The canonical height satisfies the parallelogram law exactly.**

The naïve height satisfies it only up to a bounded error (`approx_parallelogram_law`); dividing
that error by `2 · 4ⁿ` and letting `n → ∞` removes it. This is what the construction is for: the
canonical height is the quadratic function that `h` was approximating. The normalisation factor
`1/2` is common to both sides, so it does not affect the identity. -/
theorem Point.canonicalHeight_parallelogram_law [W.toAffine.IsElliptic] (P Q : W.Point) :
    (P + Q).canonicalHeight + (P - Q).canonicalHeight
      = 2 * (P.canonicalHeight + Q.canonicalHeight) := by
  obtain ⟨C, hC⟩ := approx_parallelogram_law W
  set f : W.Point → ℕ → ℝ := fun X n ↦ ((2 ^ n) • X).naiveHeight / (2 * 4 ^ n) with hf
  have hlim : ∀ X : W.Point, Tendsto (f X) atTop (𝓝 X.canonicalHeight) :=
    fun X ↦ X.tendsto_naiveHeight_two_pow_nsmul_div_four_pow
  -- the same combination, read two ways: as a limit of the four sequences, and as something
  -- squeezed to `0` by the error bound divided by `2 · 4ⁿ`.
  have hg : Tendsto (fun n ↦ f (P + Q) n + f (P - Q) n - 2 * (f P n + f Q n)) atTop
      (𝓝 ((P + Q).canonicalHeight + (P - Q).canonicalHeight
            - 2 * (P.canonicalHeight + Q.canonicalHeight))) :=
    ((hlim _).add (hlim _)).sub (((hlim _).add (hlim _)).const_mul 2)
  have hbound : ∀ n, ‖f (P + Q) n + f (P - Q) n - 2 * (f P n + f Q n)‖ ≤ C / 4 ^ n := by
    intro n
    have h := hC ((2 ^ n) • P) ((2 ^ n) • Q)
    rw [← smul_add, ← smul_sub] at h
    simp only [hf, Real.norm_eq_abs]
    -- The four terms are separate quotients by `2 · 4ⁿ`; `abs_div` below needs them as a single
    -- quotient, and no rewrite reaches that shape, since collecting them is division arithmetic
    -- rather than a rewrite. `field_simp` proves the collected form, so it is named here and
    -- rewritten in one step; the denominator is nonzero by `positivity` at each later use.
    rw [show f (P + Q) n + f (P - Q) n - 2 * (f P n + f Q n)
        = (((2 ^ n) • (P + Q)).naiveHeight + ((2 ^ n) • (P - Q)).naiveHeight
            - 2 * (((2 ^ n) • P).naiveHeight + ((2 ^ n) • Q).naiveHeight)) / (2 * 4 ^ n) from by
      simp only [hf]; field_simp]
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * 4 ^ n),
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [h, abs_nonneg (((2 ^ n) • (P + Q)).naiveHeight + ((2 ^ n) • (P - Q)).naiveHeight
      - 2 * (((2 ^ n) • P).naiveHeight + ((2 ^ n) • Q).naiveHeight)),
      pow_pos (by norm_num : (0 : ℝ) < 4) n]
  have hzero : Tendsto (fun n ↦ f (P + Q) n + f (P - Q) n - 2 * (f P n + f Q n)) atTop (𝓝 0) := by
    refine squeeze_zero_norm hbound ?_
    simpa using (tendsto_const_nhds (x := C)).div_atTop
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 4))
  linarith [tendsto_nhds_unique hg hzero]

-- Not `@[simp]`: `canonicalHeight_nsmul` is, and it rewrites `2 • P` first, which would leave
-- this lemma's left-hand side out of simp-normal form — the environment linter reports exactly
-- that. Kept as a named lemma because `4 * canonicalHeight P` is the sharper right-hand side and
-- is what a `rw` wants.
/-- **Doubling scales the canonical height by four.** The parallelogram law at `Q = P`, where
`P - Q = 0` contributes nothing. -/
theorem Point.canonicalHeight_two_nsmul [W.toAffine.IsElliptic] (P : W.Point) :
    (2 • P).canonicalHeight = 4 * P.canonicalHeight := by
  have h := canonicalHeight_parallelogram_law P P
  rw [sub_self, canonicalHeight_zero, add_zero] at h
  rw [two_nsmul]
  linarith
-- Read off the defining sequence termwise: each term is a quotient of non-negative quantities.
-- The bounded difference from `h` would only give `canonicalHeight P ≥ -C/6`, so it is not used.
/-- **The canonical height is non-negative.** This is what makes it a candidate for the
positive-definite form behind the Néron–Tate pairing and the regulator, and what lets
`canonicalHeight P = 0` be a meaningful characterisation of torsion rather than one inequality
among two. -/
theorem Point.canonicalHeight_nonneg [W.toAffine.IsElliptic] (P : W.Point) :
    0 ≤ P.canonicalHeight :=
  ge_of_tendsto' P.tendsto_naiveHeight_two_pow_nsmul_div_four_pow fun n ↦
    div_nonneg (Point.naiveHeight_nonneg _) (by positivity)

-- The parallelogram law in the shape `TauCeti.QuadraticMap.map_zsmul_of_parallelogram` consumes:
-- that statement uses `2 • ·` in an arbitrary abelian group, while `canonicalHeight` lands in `ℝ`
-- where the natural spelling is `2 * ·`.
private theorem canonicalHeight_parallelogram_nsmul [W.toAffine.IsElliptic] (P Q : W.Point) :
    (P + Q).canonicalHeight + (P - Q).canonicalHeight
      = 2 • P.canonicalHeight + 2 • Q.canonicalHeight := by
  rw [two_smul, two_smul]
  linarith [Point.canonicalHeight_parallelogram_law P Q]

/-- **The canonical height is quadratic in the point**: it takes `n • P` to `n ^ 2` times its
value at `P`, for an integer `n`. -/
@[simp]
theorem Point.canonicalHeight_zsmul [W.toAffine.IsElliptic] (n : ℤ) (P : W.Point) :
    (n • P).canonicalHeight = (n : ℝ) ^ 2 * P.canonicalHeight := by
  rw [TauCeti.QuadraticMap.map_zsmul_of_parallelogram (smul_right_injective ℝ two_ne_zero)
    canonicalHeight_parallelogram_nsmul n P]
  ring

/-- **The canonical height is quadratic in the point**, for a natural multiple. -/
@[simp]
theorem Point.canonicalHeight_nsmul [W.toAffine.IsElliptic] (n : ℕ) (P : W.Point) :
    (n • P).canonicalHeight = (n : ℝ) ^ 2 * P.canonicalHeight := by
  rw [← natCast_zsmul, Point.canonicalHeight_zsmul]
  push_cast
  ring

/-- **A torsion point has canonical height zero.** Unlike the converse this needs no Northcott
hypothesis, so it holds over every field carrying admissible absolute values. -/
theorem Point.canonicalHeight_eq_zero_of_isOfFinAddOrder [W.toAffine.IsElliptic] {P : W.Point}
    (h : IsOfFinAddOrder P) : P.canonicalHeight = 0 := by
  -- Quadraticity at `n = addOrderOf P`, where `n • P = 0` and `n ≠ 0`: `n² * canonicalHeight P`
  -- vanishes, and `n² ≠ 0`.
  simpa [h.addOrderOf_pos.ne'] using (Point.canonicalHeight_nsmul (addOrderOf P) P).symm

/-- **Northcott finiteness transfers from the naïve height to the canonical one.** This is what
lets the results below assume Northcott for the canonical height itself while callers supply only
the naïve height — or, through `MordellWeil/NaiveHeight.lean`, only the field height. -/
instance [W.toAffine.IsElliptic] [Northcott (Point.naiveHeight (W := W))] :
    Northcott (Point.canonicalHeight (W := W)) := by
  -- `abs_canonicalHeight_sub_naiveHeight_le` gives a `D` for which `canonicalHeight Q ≤ B` forces
  -- `naiveHeight Q ≤ 2 (B + D)`, so every sublevel set of the former sits inside a finite sublevel
  -- set of the latter.
  obtain ⟨D, hD⟩ := Point.abs_canonicalHeight_sub_naiveHeight_le (W := W)
  refine ⟨fun B ↦ (Northcott.finite_le (h := Point.naiveHeight (W := W)) (2 * (B + D))).subset ?_⟩
  intro Q hQ
  simp only [Set.mem_ofPred_eq] at hQ ⊢
  linarith [(abs_le.1 (hD Q)).1]

/-- **A point of canonical height zero is torsion.** The hypothesis is `Northcott` for the
canonical height, the class this API takes finiteness from; the instance above supplies it from
the naïve height and `MordellWeil/NaiveHeight.lean` from the field height, so a caller carrying
either of those needs nothing extra. -/
theorem Point.isOfFinAddOrder_of_canonicalHeight_eq_zero [W.toAffine.IsElliptic]
    [Northcott (Point.canonicalHeight (W := W))] {P : W.Point} (h : P.canonicalHeight = 0) :
    IsOfFinAddOrder P := by
  -- Quadraticity sends every multiple to `n² * canonicalHeight P = 0`, so they all lie in the
  -- sublevel set `{Q | canonicalHeight Q ≤ 0}`, which Northcott makes finite.
  refine finite_multiples.1 ?_
  refine (Northcott.finite_le (h := Point.canonicalHeight (W := W)) 0).subset ?_
  rintro Q ⟨n, rfl⟩
  simp [h]

/-- **The canonical height vanishes exactly on the torsion points**, identifying the kernel of
the canonical height with the torsion subgroup. This is one input to positive definiteness on the
free part, and so to the regulator; the others — polarising it, and finite generation of `W.Point`
— are elsewhere, and neither is supplied here. -/
@[simp]
theorem Point.canonicalHeight_eq_zero_iff_isOfFinAddOrder [W.toAffine.IsElliptic]
    [Northcott (Point.canonicalHeight (W := W))] (P : W.Point) :
    P.canonicalHeight = 0 ↔ IsOfFinAddOrder P :=
  ⟨Point.isOfFinAddOrder_of_canonicalHeight_eq_zero,
    Point.canonicalHeight_eq_zero_of_isOfFinAddOrder⟩

variable (W) in
/-- **The canonical height as a `ℤ`-quadratic map** with values in `ℝ`, which is what makes
Mathlib's polarisation API available to it. -/
noncomputable def canonicalHeightQuadratic [W.toAffine.IsElliptic] : QuadraticMap ℤ W.Point ℝ :=
  TauCeti.QuadraticMap.ofParallelogram (smul_right_injective ℝ two_ne_zero)
    canonicalHeight_parallelogram_nsmul

-- Proved by applying `ofParallelogram_apply` rather than by unfolding the definition: since
-- `canonicalHeight_parallelogram_nsmul` is `private`, the elaborator hoists it into an auxiliary
-- constant that `simp [canonicalHeightQuadratic]` cannot see through.
/-- The quadratic map is the canonical height. -/
@[simp]
theorem canonicalHeightQuadratic_apply [W.toAffine.IsElliptic] (P : W.Point) :
    canonicalHeightQuadratic W P = P.canonicalHeight :=
  TauCeti.QuadraticMap.ofParallelogram_apply _ _ P

/-- The quadratic map is the canonical height, as functions. -/
-- `QuadraticMap.polar` takes the function rather than its values, so this is the form that
-- rewrites `polar ⇑(canonicalHeightQuadratic W)` into `polar Point.canonicalHeight`; the same
-- reason `TauCeti.QuadraticMap.coe_ofParallelogram` is stated unapplied.
@[simp]
theorem coe_canonicalHeightQuadratic [W.toAffine.IsElliptic] :
    (canonicalHeightQuadratic W : W.Point → ℝ) = fun P ↦ P.canonicalHeight :=
  TauCeti.QuadraticMap.coe_ofParallelogram _ _

variable (W) in
-- `QuadraticMap.associated'` is available here because `TauCeti.instInvertibleTwoModuleEndInt`
-- supplies the `Invertible (2 : Module.End ℤ ℝ)` that the halving needs.
/-- **The Néron–Tate pairing** `⟨P, Q⟩`, the bilinear form associated with the canonical height.
It is Mathlib's `QuadraticMap.associated'`, the halved polar form. -/
noncomputable def neronTatePairing [W.toAffine.IsElliptic] : LinearMap.BilinMap ℤ W.Point ℝ :=
  QuadraticMap.associated' (canonicalHeightQuadratic W)

-- Deliberately **not** `@[simp]`, for the reason recorded on
-- `Point.naiveHeight_eq_logHeight`: tagging a defining equation makes the pairing disappear on
-- sight, which puts the sharper `neronTatePairing_self` out of simp-normal form. With `@[simp]`
-- here the `simpNF` linter fails on `neronTatePairing_self`, reporting that its left-hand side
-- simplifies to `((P + P).canonicalHeight - P.canonicalHeight - P.canonicalHeight) / 2`.
/-- **The Néron–Tate pairing is the polarisation of the canonical height**: its value at `P, Q`
is half of `canonicalHeight (P + Q) - canonicalHeight P - canonicalHeight Q`. -/
theorem neronTatePairing_apply [W.toAffine.IsElliptic] (P Q : W.Point) : neronTatePairing W P Q =
    ((P + Q).canonicalHeight - P.canonicalHeight - Q.canonicalHeight) / 2 := by
  simp [neronTatePairing, QuadraticMap.associated_apply, inv_mul_eq_div]

/-- **The pairing recovers the canonical height on the diagonal.** -/
@[simp]
theorem neronTatePairing_self [W.toAffine.IsElliptic] (P : W.Point) :
    neronTatePairing W P P = P.canonicalHeight :=
  (QuadraticMap.associated_eq_self_apply ℤ (canonicalHeightQuadratic W) P).trans
    (canonicalHeightQuadratic_apply P)

/-- **The pairing kills torsion in its first argument.** Together with symmetry this is what lets
the pairing descend to the free quotient `W.Point ⧸ torsion`, where the regulator lives. -/
@[simp]
theorem neronTatePairing_eq_zero_of_isOfFinAddOrder_left [W.toAffine.IsElliptic] {P : W.Point}
    (h : IsOfFinAddOrder P) (Q : W.Point) : neronTatePairing W P Q = 0 := by
  -- `P ↦ ⟨P, Q⟩` is additive, so it preserves finite order, and `ℝ` is torsion-free.
  -- (Taken through `flip` rather than on `neronTatePairing W` itself, because the space of
  -- linear maps carries no `IsAddTorsionFree` instance.)
  simpa using ((((neronTatePairing W).flip Q).toAddMonoidHom.isOfFinAddOrder h).eq_zero')

/-- **The pairing is symmetric**: `⟨P, Q⟩ = ⟨Q, P⟩`. -/
theorem neronTatePairing_comm [W.toAffine.IsElliptic] (P Q : W.Point) :
    neronTatePairing W P Q = neronTatePairing W Q P :=
  QuadraticMap.associated_isSymm ℤ (canonicalHeightQuadratic W) P Q

/-- **The pairing kills torsion in its second argument.** -/
@[simp]
theorem neronTatePairing_eq_zero_of_isOfFinAddOrder_right [W.toAffine.IsElliptic] (P : W.Point)
    {Q : W.Point} (h : IsOfFinAddOrder Q) : neronTatePairing W P Q = 0 := by
  rw [neronTatePairing_comm, neronTatePairing_eq_zero_of_isOfFinAddOrder_left h]

-- `LinearMap.IsSymm` does not apply to a bilinear map whose target is not the scalar ring, which
-- is why symmetry is stated pointwise above and as `flip` here; Mathlib documents
-- `QuadraticMap.associated_flip` as the general-target version for exactly this reason.
/-- **The pairing is symmetric**, as an equality of bilinear maps. -/
@[simp]
theorem neronTatePairing_flip [W.toAffine.IsElliptic] :
    (neronTatePairing W).flip = neronTatePairing W :=
  QuadraticMap.associated_flip ℤ (canonicalHeightQuadratic W)

end WeierstrassCurve.Affine

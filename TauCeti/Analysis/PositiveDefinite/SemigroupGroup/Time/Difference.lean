/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PositiveDefinite.Function.Difference
public import TauCeti.Analysis.PositiveDefinite.SemigroupGroup.Time.Axis
public import TauCeti.Analysis.PositiveDefinite.SemigroupGroup.Time.Slice

/-!
# Time differences of a bounded semigroup-group positive-definite function

A Berg--Christensen--Ressel positive-definite function `F` on the involutive semigroup `ℝ≥0 × V`
which is *bounded* has positive-definite time decrements: for every `h : ℝ≥0` the function

`(t, a) ↦ F (t, a) - F (t + h, a)`

is again semigroup-group positive definite. This is the negative of Mathlib's forward difference
`Δ_[(h, 0)]`, as `TauCeti.sub_timeShift_eq_neg_fwdDiff` records. Boundedness is essential —
`(t, a) ↦ exp t` is positive definite on `ℝ≥0 × V` and increases — and enters through the
moment-problem estimate `TauCeti.posSemidef_sub_comp_shift`, applied to the BCR kernel and the time
shift, which is symmetric for that kernel because the time variables enter through their sum.

Iterating gives that the alternating iterated differences `(-1) ^ n Δⁿ F` are again semigroup-group
positive definite, in forward-difference form and in the explicit binomial form
`(t, a) ↦ ∑ k ≤ n, (-1) ^ k (n choose k) F (t + k h, a)`. That is a statement about quadratic forms,
not a pointwise sign: nonnegativity of the values themselves is asserted only along the zero-spatial
axis, where positive definiteness specializes to the sign law `0 ≤ (-1) ^ n Δⁿ F (t, 0)` and hence
to the classical statement that `t ↦ F (t, 0)` is *completely monotone in the finite-difference
sense*:

`0 ≤ ∑ k ≤ n, (-1) ^ k (n choose k) F (t + k h, 0)`.

The two-variable statements are proved here from the kernel estimate, because the involutive-monoid
wrapper carrying the BCR involution is private to
`TauCeti/Analysis/PositiveDefinite/SemigroupGroup/Basic.lean`. The one-variable statements about the
zero-spatial axis, on the other hand, are exactly the generic `TauCeti.IsPositiveDefinite` theory of
`TauCeti/Analysis/PositiveDefinite/Function/Difference.lean`, applied to the bounded
positive-definite function `t ↦ F (t, 0)` on `ℝ≥0` with its trivial involution, and are obtained
from it here. Accordingly they assume only that the *time axis* is bounded, `‖F (t, 0)‖ ≤ C`,
rather than that `F` is bounded on all of `ℝ≥0 × V`.

This advances `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part C, Milestone 2
("BCR semigroup--Bochner"). Nothing below assumes a topology on `V` or any continuity of `F`, and
no measure is constructed here: the results are the purely algebraic finite-difference statements
that the later, topological half of the milestone consumes. In *that* setting — `V` a suitable
topological group and `F` continuous — Bochner's theorem represents each fixed-time slice
`F (t, ·)` by a finite measure `μ_t` on `V`, and the difference statement below then makes
`F (t, ·) - F (t + h, ·)` representable too, so that `μ_{t + h} ≤ μ_t`; the alternating sums
become the complete monotonicity in `t` that the representing Laplace measure of the BCR
existence half must integrate.

## Main declarations

* `TauCeti.sub_timeShift_eq_neg_fwdDiff`: the time decrement is the negative of Mathlib's forward
  difference along `(h, 0)`.
* `TauCeti.IsSemigroupGroupPD.sub_timeShift`: the time decrement of a bounded semigroup-group
  positive-definite function is semigroup-group positive definite.
* `TauCeti.IsSemigroupGroupPD.neg_one_pow_mul_fwdDiff_iter` and
  `TauCeti.IsSemigroupGroupPD.alternating_sum`: the alternating iterated differences in the time
  variable are semigroup-group positive definite, in forward-difference and in binomial form.
* `TauCeti.IsSemigroupGroupPD.timeAxis_neg_one_pow_mul_fwdDiff_iter_nonneg`: those alternating
  differences are nonnegative at each point of the zero-spatial axis, assuming only that the axis
  is bounded.
* `TauCeti.IsSemigroupGroupPD.timeAxis_alternating_sum_nonneg` and
  `TauCeti.IsSemigroupGroupPD.timeAxis_alternating_sum_re_nonneg`: a bounded time axis
  `t ↦ F (t, 0)` is completely monotone in the finite-difference sense, in the order of `ℂ` and
  for real parts.
* `TauCeti.IsSemigroupGroupPD.timeAxis_sub_nonneg` and
  `TauCeti.IsSemigroupGroupPD.timeAxis_re_antitone`: a bounded time axis is nonincreasing.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Theorem 4.1.13 and Chapter 4.
-/

public section

open scoped ComplexOrder NNReal fwdDiff

namespace TauCeti

section Difference

variable {V : Type*} [AddCommGroup V]

/-- Adding `(h, 0)` shifts the time coordinate only. -/
private theorem add_timeShift (h : ℝ≥0) (x : ℝ≥0 × V) : x + (h, 0) = (x.1 + h, x.2) := by
  simp [Prod.ext_iff]

/-- Adding `k • (h, 0)` shifts the time coordinate only. -/
private theorem add_nsmul_timeShift (h : ℝ≥0) (k : ℕ) (x : ℝ≥0 × V) :
    x + k • ((h, 0) : ℝ≥0 × V) = (x.1 + k • h, x.2) := by
  simp [Prod.ext_iff]

/-- The time decrement `x ↦ F x - F (x.1 + h, x.2)` is the negative of Mathlib's forward difference
along `(h, 0)`; in particular it is *not* the backward difference `F (t) - F (t - h)`. -/
theorem sub_timeShift_eq_neg_fwdDiff {F : ℝ≥0 × V → ℂ} (h : ℝ≥0) :
    (fun x : ℝ≥0 × V => F x - F (x.1 + h, x.2)) = -Δ_[((h, 0) : ℝ≥0 × V)] F := by
  simpa only [add_timeShift] using sub_shift_eq_neg_fwdDiff F ((h, 0) : ℝ≥0 × V)

/-- Along the zero-spatial axis, differencing `F` in the direction `(h, 0)` is differencing the
time axis `t ↦ F (t, 0)` in the direction `h`. This is what lets the one-variable results be
transported to the product-space forward difference. -/
private theorem fwdDiff_iter_timeShift_zero (n : ℕ) (F : ℝ≥0 × V → ℂ) (h t : ℝ≥0) :
    Δ_[((h, 0) : ℝ≥0 × V)]^[n] F (t, 0) = Δ_[h]^[n] (fun u : ℝ≥0 => F (u, 0)) t := by
  simp only [fwdDiff_iter_eq_sum_shift, add_nsmul_timeShift]

namespace IsSemigroupGroupPD

/-- **The time decrement of a bounded semigroup-group positive-definite function is semigroup-group
positive definite.** The Berg--Christensen--Ressel kernel `(p, q) ↦ F (p.1 + q.1, p.2 - q.2)` sees
the time shift `p ↦ (p.1 + h, p.2)` as a symmetric shift, because the two time variables enter
through their sum, so the bounded-kernel estimate `TauCeti.posSemidef_sub_comp_shift` applies.
Boundedness cannot be dropped: `(t, a) ↦ exp t` is semigroup-group positive definite and
*increases* in time. -/
theorem sub_timeShift {F : ℝ≥0 × V → ℂ} {C : ℝ} (hF : IsSemigroupGroupPD F)
    (hbdd : ∀ x, ‖F x‖ ≤ C) (h : ℝ≥0) :
    IsSemigroupGroupPD fun x : ℝ≥0 × V => F x - F (x.1 + h, x.2) := by
  have hkey := posSemidef_sub_comp_shift (K := fun p q : ℝ≥0 × V => F (p.1 + q.1, p.2 - q.2))
    (σ := fun p : ℝ≥0 × V => (p.1 + h, p.2)) hF.posSemidef
    (fun p q => by rw [add_assoc, add_comm h q.1]) (fun p q => hbdd _)
  refine IsSemigroupGroupPD.of_posSemidef ?_
  have heq : (fun p q : ℝ≥0 × V => F (p.1 + q.1, p.2 - q.2) - F (p.1 + h + q.1, p.2 - q.2)) =
      fun p q : ℝ≥0 × V => F (p.1 + q.1, p.2 - q.2) - F (p.1 + q.1 + h, p.2 - q.2) := by
    funext p q
    rw [add_right_comm]
  rw [heq] at hkey
  exact hkey

omit [AddCommGroup V] in
/-- The time decrement of a function bounded by `C` is bounded by `2 * C`. Only used to propagate
the bound through the induction in `neg_one_pow_mul_fwdDiff_iter`. -/
private theorem norm_sub_timeShift_le {F : ℝ≥0 × V → ℂ} {C : ℝ} (hbdd : ∀ x, ‖F x‖ ≤ C) (h : ℝ≥0)
    (x : ℝ≥0 × V) : ‖F x - F (x.1 + h, x.2)‖ ≤ 2 * C := by
  refine (norm_sub_le _ _).trans ?_
  have h₁ := hbdd x
  have h₂ := hbdd (x.1 + h, x.2)
  linarith

/-- **The alternating iterated time differences of a bounded semigroup-group positive-definite
function are semigroup-group positive definite.** This is the iterate of
`IsSemigroupGroupPD.sub_timeShift`: each differencing step doubles the admissible bound, which is
harmless because only the existence of *some* bound is used. -/
theorem neg_one_pow_mul_fwdDiff_iter (n : ℕ) {F : ℝ≥0 × V → ℂ} {C : ℝ}
    (hF : IsSemigroupGroupPD F) (hbdd : ∀ x, ‖F x‖ ≤ C) (h : ℝ≥0) :
    IsSemigroupGroupPD fun x : ℝ≥0 × V => (-1 : ℂ) ^ n * Δ_[((h, 0) : ℝ≥0 × V)]^[n] F x := by
  induction n generalizing F C with
  | zero => simpa using hF
  | succ n ih =>
      have hG := ih (hF.sub_timeShift hbdd h) (norm_sub_timeShift_le hbdd h)
      rwa [sub_timeShift_eq_neg_fwdDiff, neg_one_pow_mul_fwdDiff_iter_succ] at hG

/-- The alternating iterated time difference of a semigroup-group positive-definite function whose
time axis is bounded is nonnegative along the zero-spatial axis. Only the time axis has to be
bounded: the statement is the one-variable
`TauCeti.IsPositiveDefinite.neg_one_pow_mul_fwdDiff_iter_add_star_self_nonneg` for `t ↦ F (t, 0)`,
at `t / 2`. -/
theorem timeAxis_neg_one_pow_mul_fwdDiff_iter_nonneg (n : ℕ) {F : ℝ≥0 × V → ℂ} {C : ℝ}
    (hF : IsSemigroupGroupPD F) (hbdd : ∀ t : ℝ≥0, ‖F (t, 0)‖ ≤ C) (h t : ℝ≥0) :
    0 ≤ (-1 : ℂ) ^ n * Δ_[((h, 0) : ℝ≥0 × V)]^[n] F (t, 0) := by
  rw [fwdDiff_iter_timeShift_zero]
  have haxis := hF.timeAxis_isPositiveDefinite.neg_one_pow_mul_fwdDiff_iter_add_star_self_nonneg n
    (C := C) hbdd (star_trivial h) (t / 2)
  simpa only [star_trivial, add_halves] using haxis

/-- **The alternating iterated time differences, expanded as binomial sums, are semigroup-group
positive definite.** This is `IsSemigroupGroupPD.neg_one_pow_mul_fwdDiff_iter` with the
forward-difference operator resolved into the explicit alternating sum; it is the form in which the
measure-theoretic half of the Berg--Christensen--Ressel representation slices the differences by
time. -/
theorem alternating_sum (n : ℕ) {F : ℝ≥0 × V → ℂ} {C : ℝ} (hF : IsSemigroupGroupPD F)
    (hbdd : ∀ x, ‖F x‖ ≤ C) (h : ℝ≥0) :
    IsSemigroupGroupPD fun x : ℝ≥0 × V =>
      ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * (n.choose k) * F (x.1 + k • h, x.2) := by
  have hpd := neg_one_pow_mul_fwdDiff_iter n hF hbdd h
  have heq : (fun x : ℝ≥0 × V => (-1 : ℂ) ^ n * Δ_[((h, 0) : ℝ≥0 × V)]^[n] F x) =
      fun x : ℝ≥0 × V =>
        ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * (n.choose k) * F (x.1 + k • h, x.2) := by
    funext x
    rw [neg_one_pow_mul_fwdDiff_iter_eq_alternating_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [add_nsmul_timeShift]
  rwa [heq] at hpd

/-- **A semigroup-group positive-definite function with bounded time axis is completely monotone
along that axis, in the finite-difference sense:** all alternating binomial sums of its values
along an arithmetic progression of times are nonnegative. This is the form in which the Laplace
half of the Berg--Christensen--Ressel representation consumes positive definiteness. The time axis
is then a bounded positive-definite function on `ℝ≥0` with the trivial involution, so this is
`TauCeti.IsPositiveDefinite.alternating_sum_add_star_self_nonneg` at `t / 2`. -/
theorem timeAxis_alternating_sum_nonneg (n : ℕ) {F : ℝ≥0 × V → ℂ} {C : ℝ}
    (hF : IsSemigroupGroupPD F) (hbdd : ∀ t : ℝ≥0, ‖F (t, 0)‖ ≤ C) (h t : ℝ≥0) :
    0 ≤ ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * (n.choose k) * F (t + k • h, 0) := by
  have haxis := hF.timeAxis_isPositiveDefinite.alternating_sum_add_star_self_nonneg n (C := C)
    hbdd (star_trivial h) (t / 2)
  simpa only [star_trivial, add_halves] using haxis

/-- The real-part form of `IsSemigroupGroupPD.timeAxis_alternating_sum_nonneg`: the alternating
binomial sums of `t ↦ (F (t, 0)).re` are nonnegative. This is the shape consumed by the
real-valued complete-monotonicity API. -/
theorem timeAxis_alternating_sum_re_nonneg (n : ℕ) {F : ℝ≥0 × V → ℂ} {C : ℝ}
    (hF : IsSemigroupGroupPD F) (hbdd : ∀ t : ℝ≥0, ‖F (t, 0)‖ ≤ C) (h t : ℝ≥0) :
    0 ≤ ∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * n.choose k * (F (t + k • h, (0 : V))).re := by
  have hre := (Complex.nonneg_iff.mp (hF.timeAxis_alternating_sum_nonneg n hbdd h t)).1
  rw [Complex.re_sum] at hre
  refine le_of_le_of_eq hre (Finset.sum_congr rfl fun k _ => ?_)
  have hcast : ((-1 : ℂ) ^ k * (n.choose k) : ℂ) = (((-1 : ℝ) ^ k * n.choose k : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcast, Complex.re_ofReal_mul]

/-- Along the zero-spatial axis, a later value of a semigroup-group positive-definite function with
bounded time axis is dominated by an earlier one, in the order of `ℂ`. This is
`TauCeti.IsPositiveDefinite.sub_shift_add_star_self_nonneg` for the time axis, at `t / 2`. -/
theorem timeAxis_sub_nonneg {F : ℝ≥0 × V → ℂ} {C : ℝ} (hF : IsSemigroupGroupPD F)
    (hbdd : ∀ t : ℝ≥0, ‖F (t, 0)‖ ≤ C) (h t : ℝ≥0) : 0 ≤ F (t, (0 : V)) - F (t + h, 0) := by
  have haxis := hF.timeAxis_isPositiveDefinite.sub_shift_add_star_self_nonneg (C := C)
    hbdd (star_trivial h) (t / 2)
  simpa only [star_trivial, add_halves] using haxis

/-- The bounded time axis of a semigroup-group positive-definite function is nonincreasing: its
real part is an antitone function of time. -/
theorem timeAxis_re_antitone {F : ℝ≥0 × V → ℂ} {C : ℝ} (hF : IsSemigroupGroupPD F)
    (hbdd : ∀ t : ℝ≥0, ‖F (t, 0)‖ ≤ C) : Antitone fun t : ℝ≥0 => (F (t, (0 : V))).re := by
  intro t u hle
  obtain ⟨h, rfl⟩ : ∃ h : ℝ≥0, u = t + h := ⟨u - t, (add_tsub_cancel_of_le hle).symm⟩
  have hre := (Complex.nonneg_iff.mp (hF.timeAxis_sub_nonneg hbdd h t)).1
  simp only [Complex.sub_re] at hre
  linarith

end IsSemigroupGroupPD

end Difference

end TauCeti

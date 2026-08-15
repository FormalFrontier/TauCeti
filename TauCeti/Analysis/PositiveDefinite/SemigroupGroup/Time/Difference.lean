/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Group.ForwardDiff
public import TauCeti.Analysis.PositiveDefinite.Kernel.Shift
public import TauCeti.Analysis.PositiveDefinite.SemigroupGroup.Time.Slice

/-!
# Time differences of a bounded semigroup-group positive-definite function

A Berg--Christensen--Ressel positive-definite function `F` on the involutive semigroup `ℝ≥0 × V`
which is *bounded* has positive-definite backward time differences: for every `h : ℝ≥0` the
function

`(t, a) ↦ F (t, a) - F (t + h, a)`

is again semigroup-group positive definite. Boundedness is essential — `(t, a) ↦ exp t` is
positive definite on `ℝ≥0 × V` and increases — and enters through the moment-problem estimate
`TauCeti.posSemidef_sub_comp_shift`, applied to the BCR kernel and the time shift, which is
symmetric for that kernel because the time variables enter through their sum.

Iterating gives the alternating sign law `(-1) ^ n Δⁿ F ≥ 0` for Mathlib's forward difference
operator `Δ_[(h, 0)]`, and, along the zero-spatial axis, the classical statement that
`t ↦ F (t, 0)` is *completely monotone in the finite-difference sense*:

`0 ≤ ∑ k ≤ n, (-1) ^ k (n choose k) F (t + k h, 0)`.

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

* `TauCeti.IsSemigroupGroupPD.sub_timeShift`: the backward time difference of a bounded
  semigroup-group positive-definite function is semigroup-group positive definite.
* `TauCeti.IsSemigroupGroupPD.neg_one_pow_mul_fwdDiff_iter`: the alternating iterated forward
  differences in the time variable are semigroup-group positive definite.
* `TauCeti.IsSemigroupGroupPD.alternating_sum_nonneg`: the time axis `t ↦ F (t, 0)` is completely
  monotone in the finite-difference sense.
* `TauCeti.IsSemigroupGroupPD.timeAxis_sub_nonneg` and
  `TauCeti.IsSemigroupGroupPD.timeAxis_re_antitone`: the time axis is nonincreasing.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Theorem 4.1.13 and Chapter 4.
-/

public section

open scoped ComplexOrder NNReal fwdDiff

namespace TauCeti

namespace IsSemigroupGroupPD

section Difference

variable {V : Type*} [AddCommGroup V]

/-- Adding `(h, 0)` shifts the time coordinate only. -/
private theorem add_timeShift (h : ℝ≥0) (x : ℝ≥0 × V) : x + (h, 0) = (x.1 + h, x.2) := by
  simp [Prod.ext_iff]

/-- **The backward time difference of a bounded semigroup-group positive-definite function is
semigroup-group positive definite.** The Berg--Christensen--Ressel kernel
`(p, q) ↦ F (p.1 + q.1, p.2 - q.2)` sees the time shift `p ↦ (p.1 + h, p.2)` as a symmetric shift,
because the two time variables enter through their sum, so the bounded-kernel estimate
`TauCeti.posSemidef_sub_comp_shift` applies. Boundedness cannot be dropped: `(t, a) ↦ exp t` is
semigroup-group positive definite and *increases* in time. -/
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
/-- The backward time difference of a function bounded by `C` is bounded by `2 * C`. Only used to
propagate the bound through the induction in `neg_one_pow_mul_fwdDiff_iter`. -/
private theorem norm_sub_timeShift_le {F : ℝ≥0 × V → ℂ} {C : ℝ} (hbdd : ∀ x, ‖F x‖ ≤ C) (h : ℝ≥0)
    (x : ℝ≥0 × V) : ‖F x - F (x.1 + h, x.2)‖ ≤ 2 * C := by
  refine (norm_sub_le _ _).trans ?_
  have h₁ := hbdd x
  have h₂ := hbdd (x.1 + h, x.2)
  linarith

/-- The backward time difference is the negative of Mathlib's forward difference along `(h, 0)`. -/
theorem sub_timeShift_eq_neg_fwdDiff {F : ℝ≥0 × V → ℂ} (h : ℝ≥0) :
    (fun x : ℝ≥0 × V => F x - F (x.1 + h, x.2)) = -Δ_[((h, 0) : ℝ≥0 × V)] F := by
  funext x
  simp [fwdDiff, add_timeShift]

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
      rw [sub_timeShift_eq_neg_fwdDiff (F := F) h] at hG
      have hiter : Δ_[((h, 0) : ℝ≥0 × V)]^[n] (-Δ_[((h, 0) : ℝ≥0 × V)] F) =
          -Δ_[((h, 0) : ℝ≥0 × V)]^[n + 1] F := by
        rw [Function.iterate_succ_apply, ← neg_one_zsmul (Δ_[((h, 0) : ℝ≥0 × V)] F),
          fwdDiff_iter_const_smul, neg_one_zsmul]
      rw [hiter] at hG
      have heq : (fun x : ℝ≥0 × V => (-1 : ℂ) ^ n * (-Δ_[((h, 0) : ℝ≥0 × V)]^[n + 1] F) x) =
          fun x : ℝ≥0 × V => (-1 : ℂ) ^ (n + 1) * Δ_[((h, 0) : ℝ≥0 × V)]^[n + 1] F x := by
        funext x
        simp only [Pi.neg_apply, pow_succ]
        ring
      rw [heq] at hG
      exact hG

/-- The alternating iterated time difference of a bounded semigroup-group positive-definite
function is nonnegative along the zero-spatial axis. -/
theorem neg_one_pow_mul_fwdDiff_iter_apply_nonneg (n : ℕ) {F : ℝ≥0 × V → ℂ} {C : ℝ}
    (hF : IsSemigroupGroupPD F) (hbdd : ∀ x, ‖F x‖ ≤ C) (h t : ℝ≥0) :
    0 ≤ (-1 : ℂ) ^ n * Δ_[((h, 0) : ℝ≥0 × V)]^[n] F (t, 0) :=
  (neg_one_pow_mul_fwdDiff_iter n hF hbdd h).timeSlice_diagonal_nonneg t

/-- **The time axis of a bounded semigroup-group positive-definite function is completely monotone
in the finite-difference sense:** all alternating binomial sums of its values along an arithmetic
progression of times are nonnegative. This is the form in which the Laplace half of the
Berg--Christensen--Ressel representation consumes positive definiteness. -/
theorem alternating_sum_nonneg (n : ℕ) {F : ℝ≥0 × V → ℂ} {C : ℝ} (hF : IsSemigroupGroupPD F)
    (hbdd : ∀ x, ‖F x‖ ≤ C) (h t : ℝ≥0) :
    0 ≤ ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * (n.choose k) * F (t + k • h, 0) := by
  refine le_of_le_of_eq (neg_one_pow_mul_fwdDiff_iter_apply_nonneg n hF hbdd h t) ?_
  rw [fwdDiff_iter_eq_sum_shift, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hexp : n + (n - k) = 2 * (n - k) + k := by omega
  have hsign : (-1 : ℂ) ^ n * (-1 : ℂ) ^ (n - k) = (-1 : ℂ) ^ k := by
    rw [← pow_add, hexp, pow_add, pow_mul]
    simp
  have hpt : ((t, 0) : ℝ≥0 × V) + k • ((h, 0) : ℝ≥0 × V) = (t + k • h, 0) := by
    simp
  rw [hpt, zsmul_eq_mul]
  push_cast
  rw [← mul_assoc, ← mul_assoc, hsign]

/-- Along the zero-spatial axis, a later value of a bounded semigroup-group positive-definite
function is dominated by an earlier one, in the order of `ℂ`. -/
theorem timeAxis_sub_nonneg {F : ℝ≥0 × V → ℂ} {C : ℝ} (hF : IsSemigroupGroupPD F)
    (hbdd : ∀ x, ‖F x‖ ≤ C) (h t : ℝ≥0) : 0 ≤ F (t, (0 : V)) - F (t + h, 0) := by
  have hstep := neg_one_pow_mul_fwdDiff_iter_apply_nonneg 1 hF hbdd h t
  simpa [fwdDiff, add_timeShift] using hstep

/-- The time axis of a bounded semigroup-group positive-definite function is nonincreasing: its
real part is an antitone function of time. -/
theorem timeAxis_re_antitone {F : ℝ≥0 × V → ℂ} {C : ℝ} (hF : IsSemigroupGroupPD F)
    (hbdd : ∀ x, ‖F x‖ ≤ C) : Antitone fun t : ℝ≥0 => (F (t, (0 : V))).re := by
  intro t u hle
  obtain ⟨h, rfl⟩ : ∃ h : ℝ≥0, u = t + h := ⟨u - t, (add_tsub_cancel_of_le hle).symm⟩
  have hre := (Complex.nonneg_iff.mp (hF.timeAxis_sub_nonneg hbdd h t)).1
  simp only [Complex.sub_re] at hre
  linarith

end Difference

end IsSemigroupGroupPD

end TauCeti

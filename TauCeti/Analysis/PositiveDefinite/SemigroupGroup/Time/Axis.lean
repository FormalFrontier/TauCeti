/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PositiveDefinite.SemigroupGroup.Basic
public import TauCeti.Analysis.PositiveDefinite.SemigroupGroup.Time.Difference
public import Mathlib.Data.NNReal.Star
public import Mathlib.Topology.Constructions.SumProd

/-!
# The time axis of semigroup-group positive-definite functions

A Berg--Christensen--Ressel positive-definite function on `ℝ≥0 × V` restricts along the
zero-spatial axis to a positive-definite function of time. At the kernel level, this says that
`(t, u) ↦ F (t + u, 0)` is positive definite, obtained from the BCR kernel by pulling back along
`t ↦ (t, 0)`.

This is the companion to the fixed-time spatial-slice API. It is a small prerequisite for the BCR
semigroup--Bochner representation milestone in the `OneParameterSemigroups` roadmap: later proofs
can separate the spatial Bochner slices from the remaining one-dimensional time-axis structure.
When the spatial variable is trivial, this is the positive-definiteness statement left before the
Bernstein/Laplace component of BCR.

Reading the alternating time differences of `TauCeti.timeDifference` on the axis `v = 0` gives the
regularity of that one-dimensional function: it is antitone and all of its iterated forward
differences carry the sign `(-1)ⁿ`, which is complete monotonicity in the finite-difference sense.
Those statements are the generic `TauCeti.IsPositiveDefinite` theory of
`TauCeti/Analysis/PositiveDefinite/Function/Difference.lean`, applied to the positive-definite
function `t ↦ F (t, 0)` on `ℝ≥0` with its trivial involution and evaluated at the norm point
`t / 2 + star (t / 2) = t`. Accordingly they assume only that the *time axis* is bounded,
`‖F (t, 0)‖ ≤ C`, rather than that `F` is bounded on all of `ℝ≥0 × V`.

This advances `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part C, Milestone 2
("BCR semigroup--Bochner"), specifically the reduction of a positive-definite function on
`[0,∞) × V` to its zero-spatial time-axis kernel.

## Main declarations

* `TauCeti.IsSemigroupGroupPD.posSemidef_timeAxis`: the kernel
  `(t, u) ↦ F (t + u, 0)` is positive definite.
* `TauCeti.IsSemigroupGroupPD.timeAxis_conj_symm`: conjugate symmetry for the time-axis kernel.
  The existing fixed-time-slice diagonal lemmas give the real/nonnegative facts for `F (t, 0)`.
* `TauCeti.IsSemigroupGroupPD.timeAxis_sum_nonneg`: the finite quadratic-form restatement.
* `TauCeti.IsSemigroupGroupPD.timeAxis_isPositiveDefinite`: the one-variable predicate form for
  `t ↦ F (t, 0)` using the trivial involution on `ℝ≥0`.
* `TauCeti.IsSemigroupGroupPD.timeAxis_normSq_le`: the time-axis Cauchy--Schwarz estimate.
* `TauCeti.IsSemigroupGroupPD.posSemidef_timeAxis_and_continuous`: packages the
  kernel result with continuity of the zero-spatial slice.
* `TauCeti.iteratedTimeDifference_timeAxis_re`: the time-axis value of an iterated time difference
  of `F` is, up to the sign `(-1)ⁿ`, an iterated forward difference of `t ↦ (F (t, 0)).re`.
* `TauCeti.IsSemigroupGroupPD.timeAxis_alternating_sum_nonneg`,
  `TauCeti.IsSemigroupGroupPD.timeAxis_alternating_sum_re_nonneg`,
  `TauCeti.IsSemigroupGroupPD.timeAxis_iteratedTimeDifference_nonneg` and
  `TauCeti.IsSemigroupGroupPD.neg_one_pow_mul_fwdDiff_timeAxis_re_nonneg`: a bounded time axis
  `t ↦ F (t, 0)` is completely monotone in the finite-difference sense, in the order of `ℂ`, for
  real parts, and in binomial-sum and forward-difference form.
* `TauCeti.IsSemigroupGroupPD.timeAxis_sub_nonneg` and
  `TauCeti.IsSemigroupGroupPD.timeAxis_re_antitone`: a bounded time axis is nonincreasing.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 4.
-/

public section

open ComplexConjugate
open scoped ComplexOrder
open scoped NNReal

namespace TauCeti

section Zero

variable {V : Type*} [Zero V] {F : ℝ≥0 × V → ℂ}

/-- The `n`-th iterated forward difference of the time-axis function `t ↦ (F (t, 0)).re`, with
the sign `(-1)ⁿ`, is the time-axis value of the `n`-th iterated time difference of `F`. -/
theorem iteratedTimeDifference_timeAxis_re (n : ℕ) (h t : ℝ≥0) :
    (iteratedTimeDifference n h F (t, 0)).re
      = (-1) ^ n * (fwdDiff h)^[n] (fun s : ℝ≥0 => (F (s, 0)).re) t := by
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
      rw [iteratedTimeDifference_succ, timeDifference_apply, Function.iterate_succ_apply']
      simp only [Complex.sub_re, fwdDiff]
      rw [ih t, ih (t + h)]
      ring

end Zero

variable {V : Type*} [AddCommGroup V] {F : ℝ≥0 × V → ℂ} {C : ℝ}

namespace IsSemigroupGroupPD

/-- The zero-spatial time-axis kernel of a semigroup-group positive-definite function is positive
definite: `(t, u) ↦ F (t + u, 0)`. -/
theorem posSemidef_timeAxis (hF : IsSemigroupGroupPD F) :
    Matrix.PosSemidef fun t u : ℝ≥0 => F (t + u, 0) := by
  have h := hF.posSemidef.submatrix
    (fun t : ℝ≥0 => (t, (0 : V)))
  have heq : Matrix.submatrix
      (Matrix.of fun p q : ℝ≥0 × V => F (p.1 + q.1, p.2 - q.2))
      (fun t : ℝ≥0 => (t, (0 : V))) (fun t => (t, (0 : V))) =
      fun t u : ℝ≥0 => F (t + u, 0) := by
    ext t u
    rw [Matrix.submatrix_apply, Matrix.of_apply]
    simp
  exact heq ▸ h

/-- The zero-spatial time-axis kernel is conjugate symmetric:
`conj (F (t + u, 0)) = F (u + t, 0)`. -/
@[simp]
theorem timeAxis_conj_symm (hF : IsSemigroupGroupPD F) (t u : ℝ≥0) :
    conj (F (t + u, 0)) = F (u + t, 0) := by
  simpa only [starRingEnd_apply] using hF.posSemidef_timeAxis.isHermitian.apply u t

/-- The finite quadratic form of the zero-spatial time-axis kernel is nonnegative. -/
theorem timeAxis_sum_nonneg (hF : IsSemigroupGroupPD F) {ι : Type*} [Fintype ι]
    (t : ι → ℝ≥0) (x : ι → ℂ) :
    0 ≤ ∑ i, ∑ j, conj (x i) * x j * F (t i + t j, 0) :=
  by
    simpa only [RCLike.star_def, mul_comm, mul_left_comm, mul_assoc] using
      (posSemidef_iff_finite_sum.mp hF.posSemidef_timeAxis).2 t x

/-- The zero-spatial time-axis function `t ↦ F (t, 0)` is positive definite for the trivial
involution on `ℝ≥0`. -/
theorem timeAxis_isPositiveDefinite (hF : IsSemigroupGroupPD F) :
    IsPositiveDefinite fun t : ℝ≥0 => F (t, 0) := by
  rw [isPositiveDefinite_iff_posSemidef]
  simpa [star_trivial] using hF.posSemidef_timeAxis

/-- The time-axis Cauchy--Schwarz estimate for `F (t + u, 0)`. -/
theorem timeAxis_normSq_le (hF : IsSemigroupGroupPD F) (t u : ℝ≥0) :
    RCLike.normSq (F (t + u, 0))
      ≤ RCLike.re (F (t + t, 0)) * RCLike.re (F (u + u, 0)) :=
  hF.posSemidef_timeAxis.normSq_le t u

/-! ### Alternating differences along the time axis

Reading the alternating time differences of a BCR-positive-definite function on the time axis
`v = 0` leaves a statement about the real function `t ↦ (F (t, 0)).re` alone, the case with no
spatial variable. Only that axis has to be bounded for this: the statements below are the generic
one-variable theory applied to the positive-definite function `t ↦ F (t, 0)` on `ℝ≥0` with its
trivial involution, evaluated at the norm point `t / 2 + star (t / 2) = t`. -/

/-- **A semigroup-group positive-definite function with bounded time axis is completely monotone
along that axis, in the finite-difference sense:** all alternating binomial sums of its values
along an arithmetic progression of times are nonnegative. This is the form in which the Laplace
half of the Berg--Christensen--Ressel representation consumes positive definiteness. -/
theorem timeAxis_alternating_sum_nonneg (n : ℕ) (hF : IsSemigroupGroupPD F)
    (hbdd : ∀ t : ℝ≥0, ‖F (t, 0)‖ ≤ C) (h t : ℝ≥0) :
    0 ≤ ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * (n.choose k) * F (t + k • h, (0 : V)) := by
  have haxis := hF.timeAxis_isPositiveDefinite.alternating_sum_add_star_self_nonneg n (C := C)
    (fun a => hbdd _) (star_trivial h) (t / 2)
  simpa only [star_trivial, add_halves] using haxis

/-- The iterated time difference of a semigroup-group positive-definite function whose time axis is
bounded is nonnegative along the zero-spatial axis. Only the time axis has to be bounded, in
contrast with `IsSemigroupGroupPD.iteratedTimeDifference`. -/
theorem timeAxis_iteratedTimeDifference_nonneg (n : ℕ) (hF : IsSemigroupGroupPD F)
    (hbdd : ∀ t : ℝ≥0, ‖F (t, 0)‖ ≤ C) (h t : ℝ≥0) :
    0 ≤ TauCeti.iteratedTimeDifference n h F (t, (0 : V)) := by
  rw [TauCeti.iteratedTimeDifference_eq_alternating_sum]
  exact hF.timeAxis_alternating_sum_nonneg n hbdd h t

/-- The real-part form of `IsSemigroupGroupPD.timeAxis_alternating_sum_nonneg`: the alternating
binomial sums of `t ↦ (F (t, 0)).re` are nonnegative. This is the shape consumed by the
real-valued complete-monotonicity API. -/
theorem timeAxis_alternating_sum_re_nonneg (n : ℕ) (hF : IsSemigroupGroupPD F)
    (hbdd : ∀ t : ℝ≥0, ‖F (t, 0)‖ ≤ C) (h t : ℝ≥0) :
    0 ≤ ∑ k ∈ Finset.range (n + 1), (-1 : ℝ) ^ k * n.choose k * (F (t + k • h, (0 : V))).re := by
  have hre := (Complex.nonneg_iff.mp (hF.timeAxis_alternating_sum_nonneg n hbdd h t)).1
  rw [Complex.re_sum] at hre
  refine le_of_le_of_eq hre (Finset.sum_congr rfl fun k _ => ?_)
  have hcast : ((-1 : ℂ) ^ k * (n.choose k) : ℂ) = (((-1 : ℝ) ^ k * n.choose k : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcast, Complex.re_ofReal_mul]

/-- **The time-axis function of a BCR-positive-definite function with bounded time axis has
alternating forward differences.** Its `n`-th forward difference with any step has the sign
`(-1)ⁿ`, which is complete monotonicity in the finite-difference sense. -/
theorem neg_one_pow_mul_fwdDiff_timeAxis_re_nonneg (n : ℕ) (hF : IsSemigroupGroupPD F)
    (hbdd : ∀ t : ℝ≥0, ‖F (t, 0)‖ ≤ C) (h t : ℝ≥0) :
    0 ≤ (-1) ^ n * (fwdDiff h)^[n] (fun s : ℝ≥0 => (F (s, (0 : V))).re) t := by
  rw [← TauCeti.iteratedTimeDifference_timeAxis_re n h t]
  exact (Complex.nonneg_iff.mp (hF.timeAxis_iteratedTimeDifference_nonneg n hbdd h t)).1

/-- Along the zero-spatial axis, a later value of a semigroup-group positive-definite function with
bounded time axis is dominated by an earlier one, in the order of `ℂ`. -/
theorem timeAxis_sub_nonneg (hF : IsSemigroupGroupPD F) (hbdd : ∀ t : ℝ≥0, ‖F (t, 0)‖ ≤ C)
    (h t : ℝ≥0) : 0 ≤ F (t, (0 : V)) - F (t + h, 0) := by
  have haxis := hF.timeAxis_isPositiveDefinite.sub_shift_add_star_self_nonneg (C := C)
    (fun a => hbdd _) (star_trivial h) (t / 2)
  simpa only [star_trivial, add_halves] using haxis

/-- **The time-axis function of a BCR-positive-definite function with bounded time axis
decreases:** its real part is an antitone function of time. -/
theorem timeAxis_re_antitone (hF : IsSemigroupGroupPD F) (hbdd : ∀ t : ℝ≥0, ‖F (t, 0)‖ ≤ C) :
    Antitone fun t : ℝ≥0 => (F (t, (0 : V))).re := by
  intro t u hle
  obtain ⟨h, rfl⟩ : ∃ h : ℝ≥0, u = t + h := ⟨u - t, (add_tsub_cancel_of_le hle).symm⟩
  have hre := (Complex.nonneg_iff.mp (hF.timeAxis_sub_nonneg hbdd h t)).1
  simp only [Complex.sub_re] at hre
  linarith

end IsSemigroupGroupPD

section Topology

variable [TopologicalSpace V] {F : ℝ≥0 × V → ℂ}

/-- Package the positive-definite zero-spatial time-axis kernel with continuity of the
one-variable time-axis slice. -/
theorem IsSemigroupGroupPD.posSemidef_timeAxis_and_continuous
    (hFpd : IsSemigroupGroupPD F) (hFcont : Continuous F) :
    Matrix.PosSemidef (fun t u : ℝ≥0 => F (t + u, 0)) ∧
      Continuous (fun t : ℝ≥0 => F (t, 0)) :=
  ⟨hFpd.posSemidef_timeAxis, hFcont.comp (.prodMk_left 0)⟩

end Topology

end TauCeti

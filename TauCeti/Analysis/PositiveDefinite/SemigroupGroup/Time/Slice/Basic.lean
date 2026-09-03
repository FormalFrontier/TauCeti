/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PositiveDefinite.AddGroup
public import TauCeti.Analysis.PositiveDefinite.SemigroupGroup.Basic
public import Mathlib.Topology.Constructions.SumProd

/-!
# Time slices of semigroup-group positive-definite functions

A Berg--Christensen--Ressel positive-definite function on `ℝ≥0 × V` is positive definite in the
spatial variable at every fixed time. Indeed, to test the kernel
`(v, w) ↦ F (t, v - w)`, apply the BCR kernel to the family of points `(t / 2, v)`.

This file records that fixed-time-slice API in kernel form, together with the predicate form for
the fixed-time slice. These lemmas are prerequisites for the BCR representation milestone in the
`OneParameterSemigroups` roadmap: later proofs can apply the spatial Bochner theorem to each time
slice before handling the remaining Laplace/semigroup structure.

This advances `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part C, Milestone 2
("BCR semigroup--Bochner"), specifically the reduction of a bounded continuous
positive-definite function on `[0,∞) × V` to spatial positive-definite functions.

## Main declarations

* `TauCeti.IsSemigroupGroupPD.posSemidef_timeSlice`: the fixed-time spatial
  kernel is positive definite.
* `TauCeti.IsSemigroupGroupPD.timeSlice_conj_symm` and diagonal lemmas: basic symmetry and
  real-nonnegative diagonal facts for fixed-time slices.
* `TauCeti.IsSemigroupGroupPD.timeSlice_sum_nonneg`: the fixed-time spatial quadratic form is
  nonnegative for arbitrary finite families.
* `TauCeti.IsSemigroupGroupPD.timeSlice_normSq_le`: the fixed-time spatial Cauchy--Schwarz
  estimate.
* `TauCeti.IsSemigroupGroupPD.norm_apply_le_timeSlice_diagonal_re`: the direct fixed-time bound
  `‖F (t, v)‖ ≤ (F (t, 0)).re`.
* `TauCeti.IsSemigroupGroupPD.timeSlice_eq_zero_of_timeSlice_diagonal_eq_zero`: a zero
  fixed-time diagonal value kills the whole fixed-time spatial slice.
* `TauCeti.IsSemigroupGroupPD.timeSlice_isPositiveDefinite` and
  `TauCeti.IsSemigroupGroupPD.isPositiveDefiniteSub_timeSlice`: the predicate forms, for the
  negation involution and in the subtraction form Bochner's theorem uses.
* `TauCeti.IsSemigroupGroupPD.posSemidef_timeSlice_and_continuous`: packages
  the fixed-time positive-definite kernel with continuity of the fixed-time slice.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 4.
-/

public section

open ComplexConjugate
open scoped ComplexOrder
open scoped NNReal

namespace TauCeti

variable {V : Type*} [AddCommGroup V] {F : ℝ≥0 × V → ℂ}

namespace IsSemigroupGroupPD

/-- At every fixed time `t`, a semigroup-group positive-definite function gives the spatial
positive-definite kernel `(v, w) ↦ F (t, v - w)`. -/
theorem posSemidef_timeSlice (hF : IsSemigroupGroupPD F) (t : ℝ≥0) :
    Matrix.PosSemidef fun v w : V => F (t, v - w) := by
  have h := hF.posSemidef.submatrix
    (fun v : V => (t / 2, v))
  have heq : Matrix.submatrix
      (Matrix.of fun p q : ℝ≥0 × V => F (p.1 + q.1, p.2 - q.2))
      (fun v : V => (t / 2, v)) (fun v => (t / 2, v)) =
      fun v w : V => F (t, v - w) := by
    ext v w
    rw [Matrix.submatrix_apply, Matrix.of_apply]
    rw [add_halves]
  exact heq ▸ h

/-- Fixed-time slices are conjugate-symmetric in the spatial variable:
`conj (F (t, v - w)) = F (t, w - v)`. -/
@[simp]
theorem timeSlice_conj_symm (hF : IsSemigroupGroupPD F) (t : ℝ≥0) (v w : V) :
    conj (F (t, v - w)) = F (t, w - v) := by
  simpa only [starRingEnd_apply] using
    (hF.posSemidef_timeSlice t).isHermitian.apply w v

/-- The diagonal value `F (t, 0)` of a fixed-time slice is real and nonnegative. -/
theorem timeSlice_diagonal_nonneg (hF : IsSemigroupGroupPD F) (t : ℝ≥0) : 0 ≤ F (t, 0) := by
  simpa using (hF.posSemidef_timeSlice t).diag_nonneg (i := (0 : V))

/-- The diagonal value `F (t, 0)` of a fixed-time slice has zero imaginary part. -/
@[simp]
theorem timeSlice_diagonal_im (hF : IsSemigroupGroupPD F) (t : ℝ≥0) : (F (t, 0)).im = 0 :=
  ((Complex.nonneg_iff.mp (hF.timeSlice_diagonal_nonneg t)).2).symm

/-- The real part of the diagonal value `F (t, 0)` of a fixed-time slice is nonnegative. -/
theorem timeSlice_diagonal_re_nonneg (hF : IsSemigroupGroupPD F) (t : ℝ≥0) :
    0 ≤ (F (t, 0)).re :=
  (Complex.nonneg_iff.mp (hF.timeSlice_diagonal_nonneg t)).1

/-- The diagonal value `F (t, 0)` of a fixed-time slice is equal to its real part, viewed as a
complex number. -/
theorem timeSlice_diagonal_eq_ofReal_re (hF : IsSemigroupGroupPD F) (t : ℝ≥0) :
    F (t, 0) = ((F (t, 0)).re : ℂ) := by
  apply Complex.ext
  · simp
  · simpa using hF.timeSlice_diagonal_im t

/-- The fixed-time spatial quadratic form is nonnegative for arbitrary finite families. -/
theorem timeSlice_sum_nonneg (hF : IsSemigroupGroupPD F) (t : ℝ≥0) {ι : Type*} [Fintype ι]
    (v : ι → V) (x : ι → ℂ) :
    0 ≤ ∑ i, ∑ j, conj (x i) * x j * F (t, v i - v j) :=
  by
    simpa only [RCLike.star_def, mul_comm, mul_left_comm, mul_assoc] using
      (posSemidef_iff_finite_sum.mp (hF.posSemidef_timeSlice t)).2 v x

/-- The fixed-time spatial Cauchy--Schwarz bound for the kernel entry `F (t, v - w)`. -/
theorem timeSlice_normSq_le (hF : IsSemigroupGroupPD F) (t : ℝ≥0) (v w : V) :
    RCLike.normSq (F (t, v - w)) ≤ RCLike.re (F (t, 0)) * RCLike.re (F (t, 0)) := by
  simpa using (hF.posSemidef_timeSlice t).normSq_le v w

/-- At a fixed time, a semigroup-group positive-definite function is bounded by the real part of
its zero-spatial value. -/
theorem norm_apply_le_timeSlice_diagonal_re (hF : IsSemigroupGroupPD F) (t : ℝ≥0) (v : V) :
    ‖F (t, v)‖ ≤ (F (t, 0)).re := by
  refine le_of_sq_le_sq ?_ (hF.timeSlice_diagonal_re_nonneg t)
  have hsq := hF.timeSlice_normSq_le t v 0
  simpa [Complex.normSq_eq_norm_sq, pow_two] using hsq

/-- If the fixed-time diagonal value is zero, then the whole fixed-time spatial slice is zero. -/
theorem timeSlice_eq_zero_of_timeSlice_diagonal_eq_zero (hF : IsSemigroupGroupPD F)
    {t : ℝ≥0} (ht : F (t, 0) = 0) (v : V) : F (t, v) = 0 := by
  simpa using (hF.posSemidef_timeSlice t).eq_zero_of_apply_self_eq_zero_left
    (a := v) (b := 0) (by simpa using ht)

/-- Normalized fixed-time slices are bounded by `1`. -/
theorem norm_apply_le_one_of_timeSlice_diagonal_eq_one (hF : IsSemigroupGroupPD F)
    {t : ℝ≥0} (ht : F (t, 0) = 1) (v : V) : ‖F (t, v)‖ ≤ 1 := by
  have hbound := hF.norm_apply_le_timeSlice_diagonal_re t v
  simpa [ht] using hbound

/-- If the spatial type is equipped with the negation involution, then each fixed-time slice is a
positive-definite function in the generic `IsPositiveDefinite` sense. -/
theorem timeSlice_isPositiveDefinite [StarAddMonoid V]
    (hF : IsSemigroupGroupPD F) (hstar : ∀ v : V, star v = -v) (t : ℝ≥0) :
    IsPositiveDefinite fun v : V => F (t, v) :=
  (isPositiveDefinite_iff_posSemidef_sub hstar).mpr
    (hF.posSemidef_timeSlice t)

/-- Each fixed-time slice is positive definite in the subtraction form, the predicate that
Bochner's theorem on a finite-dimensional real inner-product space takes as its hypothesis. -/
theorem isPositiveDefiniteSub_timeSlice (hF : IsSemigroupGroupPD F) (t : ℝ≥0) :
    IsPositiveDefiniteSub fun v : V => F (t, v) :=
  .of_posSemidef (hF.posSemidef_timeSlice t)

end IsSemigroupGroupPD

section Topology

variable [TopologicalSpace V] {F : ℝ≥0 × V → ℂ}

/-- Package the positive-definite kernel on a fixed-time slice with continuity of the
one-variable fixed-time slice. -/
theorem IsSemigroupGroupPD.posSemidef_timeSlice_and_continuous
    (hFpd : IsSemigroupGroupPD F) (hFcont : Continuous F) (t : ℝ≥0) :
    Matrix.PosSemidef (fun v w : V => F (t, v - w)) ∧ Continuous (fun v : V => F (t, v)) :=
  ⟨hFpd.posSemidef_timeSlice t, hFcont.comp (.prodMk_right t)⟩

end Topology

end TauCeti

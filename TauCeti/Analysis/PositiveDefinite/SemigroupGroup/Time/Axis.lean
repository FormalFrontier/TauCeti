/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PositiveDefinite.SemigroupGroup.Basic
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

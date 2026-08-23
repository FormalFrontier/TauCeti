/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PositiveDefinite.SemigroupGroup.Basic

/-!
# Bounds for semigroup-group positive-definite functions

This file records the Cauchy--Schwarz consumer API for Berg--Christensen--Ressel
positive-definite functions on `ℝ≥0 × V`. The associated kernel is
`K(p, q) = F (p.1 + q.1, p.2 - q.2)`, so the generic positive-definite-kernel estimates give
bounds on every BCR kernel entry in terms of the two time-diagonal values
`F (p.1 + p.1, 0)` and `F (q.1 + q.1, 0)`.

These estimates are a small prerequisite for the BCR semigroup--Bochner representation milestone
in `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part C, Milestone 2: later arguments need to
control normalized BCR kernels and detect zero diagonal slices without unfolding
`IsSemigroupGroupPD`.

## Main declarations

In the namespace `TauCeti.IsSemigroupGroupPD`:

* `normSq_le`: the BCR Cauchy--Schwarz estimate for product points.
* `normSq_apply_le`: the same estimate in coordinates.
* `eq_zero_of_diagonal_eq_zero_left` and `eq_zero_of_diagonal_eq_zero_right`: a zero time-diagonal
  value kills the corresponding row or column of the BCR kernel.
* `norm_le_one_of_diagonal_eq_one` and `norm_apply_le_one_of_diagonal_eq_one`: normalized diagonal
  entries bound the BCR kernel entry by `1`.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapters 3 and 4.
-/

public section

open ComplexConjugate
open scoped ComplexOrder
open scoped NNReal

namespace TauCeti

variable {V : Type*} [AddCommGroup V] {F : ℝ≥0 × V → ℂ}

namespace IsSemigroupGroupPD

/-- The BCR Cauchy--Schwarz estimate. For a semigroup-group positive-definite function, the
kernel entry `F (p.1 + q.1, p.2 - q.2)` has squared norm bounded by the product of the two
time-diagonal real parts. -/
theorem normSq_le (hF : IsSemigroupGroupPD F) (p q : ℝ≥0 × V) :
    RCLike.normSq (F (p.1 + q.1, p.2 - q.2))
      ≤ RCLike.re (F (p.1 + p.1, 0)) * RCLike.re (F (q.1 + q.1, 0)) := by
  simpa using hF.posSemidef.normSq_le p q

/-- Coordinate form of the BCR Cauchy--Schwarz estimate. -/
theorem normSq_apply_le (hF : IsSemigroupGroupPD F) (t u : ℝ≥0) (v w : V) :
    RCLike.normSq (F (t + u, v - w))
      ≤ RCLike.re (F (t + t, 0)) * RCLike.re (F (u + u, 0)) := by
  simpa using hF.normSq_le (t, v) (u, w)

/-- If the left time-diagonal value is zero, then the corresponding BCR-kernel row entry is
zero. -/
theorem eq_zero_of_diagonal_eq_zero_left (hF : IsSemigroupGroupPD F) {p q : ℝ≥0 × V}
    (hp : F (p.1 + p.1, 0) = 0) : F (p.1 + q.1, p.2 - q.2) = 0 := by
  simpa using hF.posSemidef.eq_zero_of_apply_self_eq_zero_left
    (a := p) (b := q) (by simpa using hp)

/-- Coordinate form of `eq_zero_of_diagonal_eq_zero_left`. -/
theorem apply_eq_zero_of_diagonal_eq_zero_left (hF : IsSemigroupGroupPD F)
    {t u : ℝ≥0} {v w : V} (ht : F (t + t, 0) = 0) : F (t + u, v - w) = 0 := by
  simpa using hF.eq_zero_of_diagonal_eq_zero_left (p := (t, v)) (q := (u, w)) ht

/-- If the right time-diagonal value is zero, then the corresponding BCR-kernel column entry is
zero. -/
theorem eq_zero_of_diagonal_eq_zero_right (hF : IsSemigroupGroupPD F) {p q : ℝ≥0 × V}
    (hq : F (q.1 + q.1, 0) = 0) : F (p.1 + q.1, p.2 - q.2) = 0 := by
  simpa using hF.posSemidef.eq_zero_of_apply_self_eq_zero_right
    (a := p) (b := q) (by simpa using hq)

/-- Coordinate form of `eq_zero_of_diagonal_eq_zero_right`. -/
theorem apply_eq_zero_of_diagonal_eq_zero_right (hF : IsSemigroupGroupPD F)
    {t u : ℝ≥0} {v w : V} (hu : F (u + u, 0) = 0) : F (t + u, v - w) = 0 := by
  simpa using hF.eq_zero_of_diagonal_eq_zero_right (p := (t, v)) (q := (u, w)) hu

/-- If both time-diagonal entries are normalized to `1`, then the corresponding BCR-kernel entry
has norm at most `1`. -/
theorem norm_le_one_of_diagonal_eq_one (hF : IsSemigroupGroupPD F) {p q : ℝ≥0 × V}
    (hp : F (p.1 + p.1, 0) = 1) (hq : F (q.1 + q.1, 0) = 1) :
    ‖F (p.1 + q.1, p.2 - q.2)‖ ≤ 1 := by
  simpa using hF.posSemidef.norm_le_one_of_apply_self_eq_one
    (a := p) (b := q) (by simpa using hp) (by simpa using hq)

/-- Coordinate form of the normalized BCR-kernel bound. -/
theorem norm_apply_le_one_of_diagonal_eq_one (hF : IsSemigroupGroupPD F)
    {t u : ℝ≥0} {v w : V} (ht : F (t + t, 0) = 1) (hu : F (u + u, 0) = 1) :
    ‖F (t + u, v - w)‖ ≤ 1 := by
  simpa using hF.norm_le_one_of_diagonal_eq_one (p := (t, v)) (q := (u, w)) ht hu

end IsSemigroupGroupPD

end TauCeti

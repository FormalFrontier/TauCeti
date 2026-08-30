/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.Generation
import Mathlib.Topology.Algebra.Group.Matrix

/-!
# Field-valued points of the type A full-weight carrier

This file proves that over a field the matrix points of the full-weight type `A_r` carrier are
exactly `SL_{r+1}`. The ring-general transvection generation step is proved in
`TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.Generation`; Mathlib's generation of special
linear groups by transvections then gives the result.

The result is the reverse, on field-valued points, of the determinant-one containment proved in
`TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.DeterminantOne`. It is a pointwise generation
step toward identifying the integral carrier group scheme with the special linear group scheme;
the equality of their defining Hopf ideals over `ℤ` is not asserted here.

## Main results

* `TauCeti.SlStd.toGL_mem_points`: every determinant-one matrix over a field is a point of the
  carrier.
* `TauCeti.SlStd.mem_points_iff_det_eq_one`: over a field, carrier-point membership is equivalent
  to having determinant one.
* `TauCeti.SlStd.points_eq_range_toGL`: over a field, the carrier points are exactly the image of
  `SL_{r+1}` in `GL_{r+1}`.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §§26--27.
* R. Steinberg, *Lectures on Chevalley Groups*, §§3--4.

This advances Layer 9, "The Chevalley--Demazure construction", of
`TauCetiRoadmap/ReductiveGroups/README.md`: it proves the missing generation statement for the
explicit full-weight type `A` carrier on points over fields.
-/

public section

namespace TauCeti.SlStd

universe u

variable (r : ℕ)
variable {K : Type u} [Field K]

/-- **Over a field, the matrix points of the full-weight type `A_r` carrier are exactly the range
of the canonical inclusion of `SL_{r+1}` into `GL_{r+1}`.** -/
theorem points_eq_range_toGL :
    points r K =
      (Matrix.SpecialLinearGroup.toGL (n := Fin (r + 1)) (R := K)).range :=
  points_eq_range_toGL_of_transvection_generation r
    Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field

/-- The canonical inclusion of every determinant-one matrix over a field is a point of the
full-weight type `A_r` carrier. -/
theorem toGL_mem_points (g : Matrix.SpecialLinearGroup (Fin (r + 1)) K) :
    Matrix.SpecialLinearGroup.toGL g ∈ points r K := by
  rw [points_eq_range_toGL r]
  exact ⟨g, rfl⟩

/-- Over a field, a general linear matrix is a point of the full-weight type `A_r` carrier if and
only if its determinant is one. -/
theorem mem_points_iff_det_eq_one (g : Matrix.GeneralLinearGroup (Fin (r + 1)) K) :
    g ∈ points r K ↔ Matrix.GeneralLinearGroup.det g = 1 := by
  rw [points_eq_range_toGL r]
  have h := Set.ext_iff.mp
    (Matrix.SpecialLinearGroup.range_toGL (n := Fin (r + 1)) (A := K)) g
  simpa only [MonoidHom.mem_range, Set.mem_range, Set.mem_preimage, Set.mem_singleton_iff] using h

end TauCeti.SlStd

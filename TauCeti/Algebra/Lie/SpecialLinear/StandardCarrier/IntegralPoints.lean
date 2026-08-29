/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.Generation
import Mathlib.Topology.Algebra.Group.Matrix

/-!
# Integral points of the type A full-weight carrier

This file identifies the integral matrix points of the full-weight type `A_r` carrier with the
image of `SL_{r+1}(ℤ)`. It applies the ring-general carrier generation theorem to the existing
generation of the integral special linear group by transvections.

## Main results

* `TauCeti.SlStd.points_int_eq_range_toGL`: the integral carrier points are exactly the image of
  `SL_{r+1}(ℤ)` in `GL_{r+1}(ℤ)`.
* `TauCeti.SlStd.mem_points_int_iff_det_eq_one`: integral carrier-point membership is equivalent
  to having determinant one.

This advances Layer 9, "The Chevalley--Demazure construction", of
`TauCetiRoadmap/ReductiveGroups/README.md`: it records the integral-points consequence of the
ring-general generation statement for the explicit full-weight type `A` carrier.
-/

public section

namespace TauCeti.SlStd

variable (r : ℕ)

/-- Over the integers, the matrix points of the full-weight type `A_r` carrier are exactly the
range of the canonical inclusion of `SL_{r+1}` into `GL_{r+1}`. -/
theorem points_int_eq_range_toGL :
    points r ℤ =
      (Matrix.SpecialLinearGroup.toGL (n := Fin (r + 1)) (R := ℤ)).range :=
  points_eq_range_toGL_of_transvection_generation r
    Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top

/-- Over the integers, a general linear matrix is a point of the full-weight type `A_r` carrier
if and only if its determinant is one. -/
theorem mem_points_int_iff_det_eq_one (g : Matrix.GeneralLinearGroup (Fin (r + 1)) ℤ) :
    g ∈ points r ℤ ↔ Matrix.GeneralLinearGroup.det g = 1 := by
  rw [points_int_eq_range_toGL r]
  have h := Set.ext_iff.mp
    (Matrix.SpecialLinearGroup.range_toGL (n := Fin (r + 1)) (A := ℤ)) g
  simpa only [MonoidHom.mem_range, Set.mem_range, Set.mem_preimage, Set.mem_singleton_iff] using h

end TauCeti.SlStd

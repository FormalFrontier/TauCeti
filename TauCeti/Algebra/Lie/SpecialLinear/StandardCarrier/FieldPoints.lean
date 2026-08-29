/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.DeterminantOne
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection

/-!
# Field-valued points of the type A full-weight carrier

This file proves that over a field the matrix points of the full-weight type `A_r` carrier are
exactly `SL_{r+1}`. The key generation statement is that the elementary transvections attached to
the positive and negative simple roots generate every determinant-one matrix. Arbitrary root
transvections are obtained from adjacent ones by the type-A commutator relation, and Mathlib's
diagonal--transvection induction then reaches all of `SL`.

The result is the reverse, on field-valued points, of the determinant-one containment proved in
`TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.DeterminantOne`. It is a pointwise generation
step toward identifying the integral carrier group scheme with the special linear group scheme;
the equality of their defining Hopf ideals over `ℤ` is not asserted here.

## Main results

* `TauCeti.SlStd.transvectionUnit_mem_points`: every elementary transvection over a commutative
  ring is a point of the carrier.
* `TauCeti.SlStd.toGL_mem_points`: every determinant-one matrix over a field is a point of the
  carrier.
* `TauCeti.SlStd.mem_points_iff_det_eq_one`: over a field, carrier-point membership is equivalent
  to having determinant one.
* `TauCeti.SlStd.points_eq_range_toGL`: over a field, the carrier points are exactly the image of
  `SL_{r+1}` in `GL_{r+1}`.
* `TauCeti.SlStd.points_int_eq_range_toGL`: over the integers, the carrier points are exactly the
  image of `SL_{r+1}` in `GL_{r+1}`.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §§26--27.
* R. Steinberg, *Lectures on Chevalley Groups*, §§3--4.
* The arbitrary-index diagonal factorization used below generalizes and is adapted from Mathlib's
  `Matrix.SpecialLinearGroup.diag2_decompose`.

This advances Layer 9, "The Chevalley--Demazure construction", of
`TauCetiRoadmap/ReductiveGroups/README.md`: it proves the missing generation statement for the
explicit full-weight type `A` carrier on points over fields.
-/

public section

namespace TauCeti.SlStd

universe u

variable (r : ℕ)

/-! ## Generation by the numbered root subgroups -/

variable {A : Type u} [CommRing A]

private theorem rootTransvection_mem_points (k : Fin r ⊕ Fin r) (c : A) :
    TauCeti.transvectionUnit (rootTarget_ne_rootSource r k) c ∈ points r A := by
  have h := (rootSubgroupPoints r k A (Multiplicative.ofAdd c)).property
  rw [coe_rootSubgroupPoints, kostantRootSubgroupMatrix_eq_transvection] at h
  simpa only [MulEquiv.apply_symm_apply, toAdd_ofAdd] using h

/-- Every elementary transvection over a commutative ring is a point of the type `A_r` carrier. -/
theorem transvectionUnit_mem_points {i j : Fin (r + 1)} (hij : i ≠ j) (c : A) :
    TauCeti.transvectionUnit hij c ∈ points r A := by
  apply TauCeti.transvectionUnit_mem_of_adjacent (points r A)
    (fun {i j} hij c hadjacent => ?_) hij c
  rcases hadjacent with hforward | hbackward
  · let k : Fin r := ⟨i.val, by omega⟩
    have hi : k.castSucc = i := Fin.ext rfl
    have hj : k.succ = j := Fin.ext (by simp only [k, Fin.val_succ]; omega)
    simpa only [rootTarget_inl, rootSource_inl, hi, hj] using
      rootTransvection_mem_points (A := A) r (.inl k) c
  · let k : Fin r := ⟨j.val, by omega⟩
    have hi : k.succ = i := Fin.ext (by simp only [k, Fin.val_succ]; omega)
    have hj : k.castSucc = j := Fin.ext rfl
    simpa only [rootTarget_inr, rootSource_inr, hi, hj] using
      rootTransvection_mem_points (A := A) r (.inr k) c

/-! ## All points when transvections generate the special linear group -/

private theorem mem_range_toGL_iff_det_eq_one {R : Type u} [CommRing R]
    (g : Matrix.GeneralLinearGroup (Fin (r + 1)) R) :
    g ∈ (Matrix.SpecialLinearGroup.toGL (n := Fin (r + 1)) (R := R)).range ↔
      Matrix.GeneralLinearGroup.det g = 1 := by
  constructor
  · rintro ⟨s, rfl⟩
    apply Units.ext
    change Matrix.det s.val = 1
    exact s.property
  · intro hg
    let s : Matrix.SpecialLinearGroup (Fin (r + 1)) R := ⟨g.val, by
      rw [← Matrix.GeneralLinearGroup.val_det_apply, hg, Units.val_one]⟩
    exact ⟨s, Units.ext rfl⟩

private theorem toGL_mem_points_of_transvection_generation {R : Type u} [CommRing R]
    (hgen : Subgroup.closure (Set.range (Matrix.TransvectionStruct.toSpecialLinearGroup :
      Matrix.TransvectionStruct (Fin (r + 1)) R →
        Matrix.SpecialLinearGroup (Fin (r + 1)) R)) = ⊤)
    (g : Matrix.SpecialLinearGroup (Fin (r + 1)) R) :
    Matrix.SpecialLinearGroup.toGL g ∈ points r R := by
  let H : Subgroup (Matrix.SpecialLinearGroup (Fin (r + 1)) R) :=
    (points r R).comap Matrix.SpecialLinearGroup.toGL
  have hclosure : Subgroup.closure (Set.range (Matrix.TransvectionStruct.toSpecialLinearGroup :
      Matrix.TransvectionStruct (Fin (r + 1)) R →
        Matrix.SpecialLinearGroup (Fin (r + 1)) R)) ≤ H := by
    apply (Subgroup.closure_le H).2
    rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
    change Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij c) ∈
      points r R
    simpa only [TauCeti.toGL_transvection_eq_transvectionUnit] using
      transvectionUnit_mem_points (A := R) r hij c
  rw [hgen] at hclosure
  exact hclosure (Subgroup.mem_top g)

/-- If elementary transvections generate `SL_{r+1}(R)`, then the matrix points of the full-weight
type `A_r` carrier over `R` are exactly the range of `SL_{r+1}(R)` in `GL_{r+1}(R)`. -/
theorem points_eq_range_toGL_of_transvection_generation {R : Type u} [CommRing R]
    (hgen : Subgroup.closure (Set.range (Matrix.TransvectionStruct.toSpecialLinearGroup :
      Matrix.TransvectionStruct (Fin (r + 1)) R →
        Matrix.SpecialLinearGroup (Fin (r + 1)) R)) = ⊤) :
    points r R =
      (Matrix.SpecialLinearGroup.toGL (n := Fin (r + 1)) (R := R)).range := by
  apply le_antisymm
  · intro g hg
    exact (mem_range_toGL_iff_det_eq_one r g).2 (det_eq_one_of_mem_points r hg)
  · rintro _ ⟨g, rfl⟩
    exact toGL_mem_points_of_transvection_generation r hgen g

/-! ### Fields -/

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
  exact mem_range_toGL_iff_det_eq_one r g

/-! ### Integers -/

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
  exact mem_range_toGL_iff_det_eq_one r g

end TauCeti.SlStd

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.DeterminantOne
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection
import Mathlib.Topology.Algebra.Group.Matrix

/-!
# Generation of type A full-weight carrier points

This file proves that every elementary transvection over a commutative ring is a matrix point of
the full-weight type `A_r` carrier. Consequently, whenever elementary transvections generate the
special linear group over a ring, the carrier points are exactly the image of that special linear
group in the general linear group.

## Main results

* `TauCeti.SlStd.transvectionUnit_mem_points`: every elementary transvection over a commutative
  ring is a point of the carrier.
* `TauCeti.SlStd.points_eq_range_toGL_of_transvection_generation`: transvection generation of
  `SL_{r+1}(R)` identifies its image with the carrier points over `R`.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §§26--27.
* R. Steinberg, *Lectures on Chevalley Groups*, §§3--4.

This advances Layer 9, "The Chevalley--Demazure construction", of
`TauCetiRoadmap/ReductiveGroups/README.md`: it supplies the ring-general generation step used to
identify the explicit full-weight type `A` carrier on field and integral points.
-/

public section

namespace TauCeti.SlStd

universe u

variable (r : ℕ)
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

private theorem toGL_mem_points_of_transvection_generation {R : Type u} [CommRing R]
    (hgen : Subgroup.closure (Set.range (Matrix.TransvectionStruct.toSpecialLinearGroup :
      Matrix.TransvectionStruct (Fin (r + 1)) R →
        Matrix.SpecialLinearGroup (Fin (r + 1)) R)) = ⊤)
    (g : Matrix.SpecialLinearGroup (Fin (r + 1)) R) :
    Matrix.SpecialLinearGroup.toGL g ∈ points r R := by
  have hclosure : Subgroup.closure (Set.range (Matrix.TransvectionStruct.toSpecialLinearGroup :
      Matrix.TransvectionStruct (Fin (r + 1)) R →
        Matrix.SpecialLinearGroup (Fin (r + 1)) R)) ≤
      (points r R).comap Matrix.SpecialLinearGroup.toGL := by
    apply (Subgroup.closure_le _).2
    rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
    apply (Subgroup.mem_comap).2
    rw [Matrix.TransvectionStruct.toSpecialLinearGroup_mk,
      TauCeti.toGL_transvection_eq_transvectionUnit]
    exact transvectionUnit_mem_points (A := R) r hij c
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
    have hdet : Matrix.GeneralLinearGroup.det g = 1 := det_eq_one_of_mem_points r hg
    have hmem : g ∈ Matrix.GeneralLinearGroup.det ⁻¹' ({1} : Set Rˣ) := by
      simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hdet
    rw [← Matrix.SpecialLinearGroup.range_toGL] at hmem
    exact hmem
  · rintro _ ⟨g, rfl⟩
    exact toGL_mem_points_of_transvection_generation r hgen g

end TauCeti.SlStd

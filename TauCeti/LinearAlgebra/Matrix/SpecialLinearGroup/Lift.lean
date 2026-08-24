/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Lifting special-linear matrices

A special-linear matrix lifts across a quotient by a nilpotent ideal. Lift its entries
arbitrarily; its determinant is then a unit because it is one modulo the ideal. Scaling one row
by the inverse determinant corrects the lift without changing its image.

## Main declaration

* `Matrix.SpecialLinearGroup.map_quotient_mk_surjective_of_isNilpotent`: entrywise reduction
  modulo a nilpotent ideal is surjective on special-linear groups.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 2.
-/

public section

namespace Matrix.SpecialLinearGroup

universe u

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type u} [CommRing R]

/-- Every determinant-one matrix modulo a nilpotent ideal lifts to a determinant-one matrix.

The statement includes the empty index type, where both special-linear groups are trivial. -/
theorem map_quotient_mk_surjective_of_isNilpotent (I : Ideal R) (hI : IsNilpotent I) :
    Function.Surjective
      (Matrix.SpecialLinearGroup.map (n := n) (Ideal.Quotient.mk I)) := by
  intro A
  cases isEmpty_or_nonempty n with
  | inl _ =>
      exact ⟨1, Subsingleton.elim _ _⟩
  | inr _ =>
      choose m hm using fun i j => Ideal.Quotient.mk_surjective (A.1 i j)
      let M : Matrix n n R := m
      have hM (i j) : Ideal.Quotient.mk I (M i j) = A.1 i j := hm i j
      have hM_map : M.map (Ideal.Quotient.mk I) = A.1 := by
        ext i j
        exact hM i j
      have hdet_map : Ideal.Quotient.mk I M.det = 1 := by
        rw [RingHom.map_det, RingHom.mapMatrix_apply, hM_map, A.prop]
      have hdet_unit : IsUnit M.det := (IsNilpotent.isUnit_quotient_mk_iff hI).mp (by
        rw [hdet_map]
        exact isUnit_one)
      let u : Rˣ := hdet_unit.unit
      have hu : (u : R) = M.det := hdet_unit.unit_spec
      have hu_map : Ideal.Quotient.mk I (u : R) = 1 := by
        rw [hu]
        exact hdet_map
      have hu_inv_map : Ideal.Quotient.mk I (↑(u⁻¹) : R) = 1 := by
        have h := congrArg (Ideal.Quotient.mk I) u.inv_mul
        rw [map_mul, hu_map, mul_one, map_one] at h
        exact h
      let i₀ : n := Classical.choice inferInstance
      let N : Matrix n n R := M.updateRow i₀ ((↑(u⁻¹) : R) • M i₀)
      have hNdet : N.det = 1 := by
        dsimp only [N]
        rw [Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]
        simpa only [hu] using Units.inv_mul u
      have hN_map : N.map (Ideal.Quotient.mk I) = A.1 := by
        ext i j
        simp only [Matrix.map_apply]
        dsimp only [N]
        by_cases hi : i = i₀
        · subst i
          rw [Matrix.updateRow_self, Pi.smul_apply, smul_eq_mul, map_mul, hu_inv_map, one_mul]
          exact hM i₀ j
        · rw [Matrix.updateRow_apply, ite_eq_right hi]
          exact hM i j
      refine ⟨⟨N, hNdet⟩, ?_⟩
      apply Subtype.ext
      exact (Matrix.SpecialLinearGroup.map_apply_coe (Ideal.Quotient.mk I) ⟨N, hNdet⟩).trans
        (by simpa only [RingHom.mapMatrix_apply] using hN_map)

end Matrix.SpecialLinearGroup

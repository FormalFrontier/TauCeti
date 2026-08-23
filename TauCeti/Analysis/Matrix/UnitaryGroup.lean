/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# `U(n) = Circle · SU(n)`

The determinant of a complex unitary matrix has modulus one, and every point of the circle has a
`card n`-th root there, so a unitary matrix can be rescaled by a scalar of modulus one until its
determinant is one: the unitary group is the product of the scalars of modulus one with the special
unitary group. Rescaling by a scalar of modulus one keeps a matrix unitary, so nothing is lost.

## Main results

* `TauCeti.Matrix.exists_circle_smul_mem_specialUnitaryGroup`: every complex unitary matrix becomes
  special unitary after multiplication by a suitable scalar of modulus one.
-/

public section

namespace TauCeti

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `U(n) = Circle · SU(n)`: every complex unitary matrix becomes special unitary after
multiplication by a suitable scalar of modulus one. The scalar is a `card n`-th root of the inverse
of the determinant, which has modulus one; the root is taken through `Circle.exp`. -/
theorem exists_circle_smul_mem_specialUnitaryGroup (U : Matrix.unitaryGroup n ℂ) :
    ∃ c : Circle, ((c : ℂ) • (U : Matrix n n ℂ)) ∈ Matrix.specialUnitaryGroup n ℂ := by
  have hcc : ∀ z : Circle, (z : ℂ) ∈ unitary ℂ := fun z =>
    Unitary.mem_iff_star_mul_self.mpr <| by
      rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Circle.normSq_coe,
        Complex.ofReal_one]
  -- Rescaling by a scalar of modulus one keeps the matrix unitary, whatever the scalar.
  have hunit : ∀ c : Circle, ((c : ℂ) • (U : Matrix n n ℂ)) ∈ Matrix.unitaryGroup n ℂ := fun c =>
    Unitary.smul_mem_of_mem (hcc c) U.2
  rcases isEmpty_or_nonempty n with hn | hn
  · -- With no indices at all every determinant is one and there is nothing to rescale.
    exact ⟨1, Matrix.mem_specialUnitaryGroup_iff.mpr ⟨hunit 1, Matrix.det_isEmpty⟩⟩
  · have hcard : (Fintype.card n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hnorm : ‖(U : Matrix n n ℂ).det‖ = 1 :=
      CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary U.2)
    obtain ⟨θ, hθ⟩ := Circle.exp_surjective
      (⟨(U : Matrix n n ℂ).det, mem_sphere_zero_iff_norm.mpr hnorm⟩ : Circle)
    have hdetU : (U : Matrix n n ℂ).det = Complex.exp ((θ : ℂ) * Complex.I) := by
      have := congrArg (fun z : Circle => (z : ℂ)) hθ
      rw [Circle.coe_exp] at this
      exact this.symm
    refine ⟨Circle.exp (-(θ / Fintype.card n)), Matrix.mem_specialUnitaryGroup_iff.mpr
      ⟨hunit _, ?_⟩⟩
    rw [Matrix.det_smul, Circle.coe_exp, hdetU, ← Complex.exp_nat_mul, ← Complex.exp_add,
      ← Complex.exp_zero]
    congr 1
    push_cast
    field_simp
    ring

end Matrix

end TauCeti

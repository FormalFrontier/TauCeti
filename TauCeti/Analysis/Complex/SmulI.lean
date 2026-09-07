/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.Module.Equiv

/-!
# Multiplication by `i` on a complex normed space

Multiplication by `i` is a real continuous linear automorphism of any complex normed space, with
inverse multiplication by `-i`.  It is the conjugating operator by which complex linearity of a
real-linear map is tested.

## Main definitions and results

* `Complex.I_smul_neg_I_smul` and `Complex.neg_I_smul_I_smul`: multiplication by `i` and by `-i`
  are mutually inverse on a complex module.
* `Complex.smulIEquiv`: multiplication by `i` as a real continuous linear equivalence, with
  `smulIEquiv_apply` and `smulIEquiv_symm_apply`.
-/

public section

namespace Complex

section Module

variable {X : Type*} [AddCommGroup X] [Module ℂ X]

theorem I_smul_neg_I_smul (x : X) : I • (-I • x) = x := by
  rw [smul_smul, mul_neg, I_mul_I, neg_neg, one_smul]

theorem neg_I_smul_I_smul (x : X) : -I • (I • x) = x := by
  rw [smul_smul, neg_mul, I_mul_I, neg_neg, one_smul]

end Module

section Normed

variable (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Multiplication by `i` as a real continuous linear equivalence of a complex normed space. -/
noncomputable def smulIEquiv : X ≃L[ℝ] X :=
  ContinuousLinearEquiv.smulLeft (Units.mk0 I I_ne_zero)

variable {X}

@[simp]
theorem smulIEquiv_apply (x : X) : smulIEquiv X x = I • x := by
  simp [smulIEquiv, Units.smul_def]

@[simp]
theorem smulIEquiv_symm_apply (x : X) : (smulIEquiv X).symm x = -I • x := by
  rw [ContinuousLinearEquiv.symm_apply_eq, smulIEquiv_apply, I_smul_neg_I_smul]

end Normed

end Complex

end

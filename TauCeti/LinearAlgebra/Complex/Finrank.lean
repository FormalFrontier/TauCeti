/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Real finrank of a compatible complex module

This file records the tower-law dimension formula for a complex module whose real scalar
structure is the ambient one. It is the linear-algebra input for almost-complex even-dimensionality
results, but has no symplectic hypotheses.
-/

public section

namespace TauCeti

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A compatible complex module structure forces the real dimension to be twice the complex
dimension. This is the ambient-real-structure form of Mathlib's `finrank_real_of_complex`: that
lemma fixes the real structure to be the one induced by restricting scalars
(`Module.complexToReal`), whereas here `V` already carries an ambient `Module ℝ V` made compatible
via `IsScalarTower ℝ ℂ V` (the situation produced by an almost complex structure). -/
theorem finrank_real_eq_two_mul_finrank_complex [Module ℂ V] [IsScalarTower ℝ ℂ V] :
    Module.finrank ℝ V = 2 * Module.finrank ℂ V := by
  -- The ambient `Module ℝ V` agrees with the restrict-scalars structure `Module.complexToReal V`,
  -- so the identity follows from Mathlib's `finrank_real_of_complex` for the latter.
  have h : Module.complexToReal V = (inferInstance : Module ℝ V) := by
    apply Module.ext
    funext r v
    exact IsScalarTower.algebraMap_smul ℂ r v
  have hV := finrank_real_of_complex (E := V)
  rw [h] at hV
  exact hV

end TauCeti

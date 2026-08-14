/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

-- `Matrix.IsSymm` occurs in the statements below.
public import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic.Ring

public section

/-!
# Gram forms and matrix reflection

This file records the basic symmetry and quadratic-form preservation identities for the bilinear
and quadratic forms attached to a symmetric matrix.

## Main results

* `TauCeti.vecMul_dotProduct_comm`: the bilinear form `(v, w) ↦ (v ᵥ* M) ⬝ᵥ w` of a symmetric matrix
  `M` is symmetric.
* `TauCeti.reflect_vecMul_dotProduct_self`: reflection in a vector of norm two preserves the value
  `(v ᵥ* M) ⬝ᵥ v` of the form at every vector.
-/

namespace TauCeti

open _root_.Matrix

variable {n : Type*} [Fintype n]

/-- The bilinear form carried by a symmetric matrix is symmetric. -/
theorem vecMul_dotProduct_comm {R : Type*} [NonUnitalCommSemiring R] {M : Matrix n n R}
    (hM : M.IsSymm) (v w : n → R) :
    (v ᵥ* M) ⬝ᵥ w = (w ᵥ* M) ⬝ᵥ v := by
  rw [← dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose, hM.eq]

variable {R : Type*} [CommRing R] {M : Matrix n n R}

/-- **Reflection in a vector of norm two preserves the value of the quadratic form.** For a
symmetric matrix `M` and a vector `u` with `(u ᵥ* M) ⬝ᵥ u = 2`, reflection in `u` preserves the
value `(v ᵥ* M) ⬝ᵥ v` of the form at every vector `v`. This is what makes a family of norm-two
vectors stable under its own reflections once the family exhausts the norm-two vectors. -/
theorem reflect_vecMul_dotProduct_self (hM : M.IsSymm) {u : n → R} (hu : (u ᵥ* M) ⬝ᵥ u = 2)
    (v : n → R) :
    ((v - ((v ᵥ* M) ⬝ᵥ u) • u) ᵥ* M) ⬝ᵥ (v - ((v ᵥ* M) ⬝ᵥ u) • u) = (v ᵥ* M) ⬝ᵥ v := by
  simp only [sub_vecMul, smul_vecMul, sub_dotProduct, dotProduct_sub, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, hu, vecMul_dotProduct_comm hM u v]
  ring

end TauCeti

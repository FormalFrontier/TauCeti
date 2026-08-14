/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

-- `dotProductBilin` and `dotProductEquiv` occur in the statement and the body below.
public import Mathlib.LinearAlgebra.Matrix.Dual
-- `Matrix.IsSymm` occurs in the statements below.
public import Mathlib.LinearAlgebra.Matrix.Symmetric
-- `LinearMap.IsPerfPair` occurs in the statement below.
public import Mathlib.LinearAlgebra.PerfectPairing.Basic

public section

/-!
# The dot product on `ι → R` is a perfect pairing

Mathlib's `dotProductEquiv` identifies `ι → R`, for `ι` finite, with its own dual under the dot
product. This file records the same fact in the form asked for by `LinearMap.IsPerfPair`, so that
the dot product may be used directly as the pairing of a `RootPairing` or a `RootDatum` on `ι → R`.
It also records the basic symmetry and reflection-isometry identities for the bilinear form
associated to a symmetric matrix.

## Main results

* `TauCeti.dotProductBilin_isPerfPair`: the dot product `dotProductBilin R R` on `ι → R` is a
  perfect pairing of that module with itself.
* `TauCeti.vecMul_dotProduct_comm`: the bilinear form `(v, w) ↦ (v ᵥ* M) ⬝ᵥ w` of a symmetric matrix
  `M` is symmetric.
* `TauCeti.reflect_vecMul_dotProduct_self`: reflection in a vector of norm two preserves the
  bilinear form of a symmetric matrix.
-/

namespace TauCeti

open _root_.Matrix

/-- The dot product on `ι → R` is a perfect pairing of that module with itself: it is Mathlib's
`dotProductEquiv` read as a bilinear map. -/
instance dotProductBilin_isPerfPair (R ι : Type*) [CommRing R] [Fintype ι] :
    (dotProductBilin R R : (ι → R) →ₗ[R] (ι → R) →ₗ[R] R).IsPerfPair := by
  classical
  have h : (dotProductBilin R R : (ι → R) →ₗ[R] (ι → R) →ₗ[R] R) =
      (dotProductEquiv R ι).toLinearMap := by
    ext x y
    simp
  rw [h]
  infer_instance

section Gram

variable {n R : Type*} [Fintype n] [CommRing R] {M : Matrix n n R}

/-- The bilinear form carried by a symmetric matrix is symmetric. -/
theorem vecMul_dotProduct_comm (hM : M.IsSymm) (v w : n → R) :
    (v ᵥ* M) ⬝ᵥ w = (w ᵥ* M) ⬝ᵥ v := by
  rw [← dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose, hM.eq]

/-- **Reflection in a vector of norm two preserves the form.** For a symmetric matrix `M` and a
vector `u` with `⟨u, u⟩ = 2`, the reflection `v ↦ v - ⟨v, u⟩ • u` is an isometry of the form
carried by `M`. This is what makes a family of norm-two vectors stable under its own reflections
once the family exhausts the norm-two vectors. -/
theorem reflect_vecMul_dotProduct_self (hM : M.IsSymm) {u : n → R} (hu : (u ᵥ* M) ⬝ᵥ u = 2)
    (v : n → R) :
    ((v - ((v ᵥ* M) ⬝ᵥ u) • u) ᵥ* M) ⬝ᵥ (v - ((v ᵥ* M) ⬝ᵥ u) • u) = (v ᵥ* M) ⬝ᵥ v := by
  simp only [sub_vecMul, smul_vecMul, sub_dotProduct, dotProduct_sub, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, hu, vecMul_dotProduct_comm hM u v]
  ring

end Gram

end TauCeti

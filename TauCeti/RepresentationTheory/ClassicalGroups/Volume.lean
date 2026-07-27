/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import TauCeti.RepresentationTheory.ClassicalGroups.Standard

public section

/-!
# The volume form preserved by the special linear group

This file defines the coordinate volume form on `Fin n → k` and proves its transformation law
under the standard action of the general linear group.  Restricting to matrices of determinant one
gives the invariant alternating form required for the standard representation of `SL(n, k)`.

## Main definitions

* `TauCeti.volumeForm` is the top-dimensional alternating form determined by the standard basis.

## References

* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md),
  Layer 0, “The subgroups and the extra invariants”.
-/

namespace TauCeti

open Matrix

universe u

variable (k : Type u) (n : ℕ)

section CommRing

variable [CommRing k]

/-- The coordinate volume form on `kⁿ`, normalized to take value `1` on the standard basis. -/
noncomputable def volumeForm : (Fin n → k) [⋀^Fin n]→ₗ[k] k :=
  (Pi.basisFun k (Fin n)).det

/-- The coordinate volume form evaluates a family of vectors by its matrix determinant. -/
theorem volumeForm_apply (v : Fin n → Fin n → k) :
    volumeForm k n v = Matrix.det (Matrix.of v) := by
  exact Pi.basisFun_det_apply v

/-- The coordinate volume form is normalized on the standard basis. -/
@[simp]
theorem volumeForm_basis : volumeForm k n (Pi.basisFun k (Fin n)) = 1 :=
  (Pi.basisFun k (Fin n)).det_self

/-- The coordinate volume form is nonzero over a nontrivial coefficient ring. -/
theorem volumeForm_ne_zero [Nontrivial k] : volumeForm k n ≠ 0 :=
  (Pi.basisFun k (Fin n)).det_ne_zero

/-- The standard action of `GL(n, k)` scales the volume form by the matrix determinant. -/
theorem volumeForm_stdRep (g : GL (Fin n) k) (v : Fin n → Fin n → k) :
    volumeForm k n (fun i => stdRep k n g (v i)) =
      Matrix.det (g : Matrix (Fin n) (Fin n) k) * volumeForm k n v := by
  simpa [volumeForm, stdRep_apply, Function.comp_def, LinearMap.det_toLin'] using
    (Module.Basis.det_comp (Pi.basisFun k (Fin n))
      (Matrix.toLin' (g : Matrix (Fin n) (Fin n) k)) v)

/-- The standard action of `SL(n, k)` preserves the coordinate volume form. -/
@[simp]
theorem volumeForm_stdRep_SL (g : Matrix.SpecialLinearGroup (Fin n) k)
    (v : Fin n → Fin n → k) :
    volumeForm k n (fun i => stdRep k n (g : GL (Fin n) k) (v i)) = volumeForm k n v := by
  rw [volumeForm_stdRep, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, g.det_coe, one_mul]

/-- The standard action of `SL(n, k)` preserves the coordinate volume form on the standard basis. -/
@[simp]
theorem volumeForm_stdRep_SL_basis (g : Matrix.SpecialLinearGroup (Fin n) k) :
    volumeForm k n (fun i => stdRep k n (g : GL (Fin n) k) (Pi.basisFun k (Fin n) i)) = 1 := by
  rw [volumeForm_stdRep_SL, volumeForm_basis]

end CommRing

end TauCeti

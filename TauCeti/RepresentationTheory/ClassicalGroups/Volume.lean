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
# The determinant form preserved by the special linear group

This file proves the transformation law for Mathlib's standard-basis determinant form under the
standard action of the general linear group. Restricting to matrices of determinant one gives the
invariant alternating form required for the standard representation of `SL(n, k)`.

## Main results

* `TauCeti.basisFun_det_stdRep` gives the determinant transformation law for the standard
  representation.
* `TauCeti.basisFun_det_stdRep_SL` states its specialization to the special linear group.

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

/-- The standard action of `GL(n, k)` scales the standard-basis determinant form by the matrix
determinant. -/
theorem basisFun_det_stdRep (g : GL (Fin n) k) (v : Fin n → Fin n → k) :
    (Pi.basisFun k (Fin n)).det (fun i => stdRep k n g (v i)) =
      Matrix.det (g : Matrix (Fin n) (Fin n) k) * (Pi.basisFun k (Fin n)).det v := by
  simpa [stdRep_apply, Function.comp_def, LinearMap.det_toLin'] using
    (Module.Basis.det_comp (Pi.basisFun k (Fin n))
      (Matrix.toLin' (g : Matrix (Fin n) (Fin n) k)) v)

/-- The standard action of `SL(n, k)` preserves the standard-basis determinant form. -/
theorem basisFun_det_stdRep_SL (g : Matrix.SpecialLinearGroup (Fin n) k)
    (v : Fin n → Fin n → k) :
    (Pi.basisFun k (Fin n)).det (fun i => (g : Matrix (Fin n) (Fin n) k).mulVec (v i)) =
      (Pi.basisFun k (Fin n)).det v := by
  simpa only [stdRep_apply, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.mulVecBilin_apply,
    g.det_coe, one_mul] using basisFun_det_stdRep k n (g : GL (Fin n) k) v

end CommRing

end TauCeti

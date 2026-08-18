/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Trace

/-!
# Nondegeneracy of the trace pairing

This file records that the trace pairing on the endomorphisms of a finite free module is
nondegenerate.

## Main result

* `TauCeti.LinearMap.eq_zero_of_trace_mul_eq_zero`: an endomorphism whose product with every
  endomorphism has zero trace is zero.
-/

public section

namespace TauCeti.LinearMap

variable {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V]

/-- The trace pairing on the endomorphisms of a finite-dimensional vector space is nondegenerate:
an endomorphism whose product with every endomorphism has zero trace is zero. -/
theorem eq_zero_of_trace_mul_eq_zero [Module.Free K V] [Module.Finite K V]
    (f : Module.End K V)
    (h : ∀ g : Module.End K V, _root_.LinearMap.trace K V (f * g) = 0) : f = 0 := by
  let b := Module.Free.chooseBasis K V
  apply (_root_.LinearMap.toMatrixAlgEquiv b).injective
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro Y
  have hY := h ((_root_.LinearMap.toMatrixAlgEquiv b).symm Y)
  rw [_root_.LinearMap.trace_eq_matrix_trace K b] at hY
  -- `trace_eq_matrix_trace` leaves the product expressed before applying `toMatrixAlgEquiv`;
  -- expose its definitionally equal matrix form so the algebra-equivalence laws can rewrite it.
  change (((_root_.LinearMap.toMatrixAlgEquiv b)
    (f * (_root_.LinearMap.toMatrixAlgEquiv b).symm Y)).trace = 0) at hY
  simpa only [map_mul, AlgEquiv.apply_symm_apply, map_zero, zero_mul, Matrix.trace_zero] using hY

end TauCeti.LinearMap

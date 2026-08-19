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

* `TauCeti.LinearMap.ext_iff_trace_mul_right`: two endomorphisms are equal exactly when their
  products with every endomorphism have equal trace.
* `TauCeti.LinearMap.eq_zero_of_trace_mul_eq_zero`: the corresponding zero criterion.
-/

public section

namespace TauCeti.LinearMap

variable {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V]

/-- The trace pairing on the endomorphisms of a finite free module over a commutative ring is
nondegenerate. -/
theorem ext_iff_trace_mul_right [Module.Free K V] [Module.Finite K V]
    (f g : Module.End K V) :
    f = g ↔ ∀ h : Module.End K V,
      _root_.LinearMap.trace K V (f * h) = _root_.LinearMap.trace K V (g * h) := by
  constructor
  · rintro rfl
    exact fun _ ↦ rfl
  · intro h
    let b := Module.Free.chooseBasis K V
    apply (_root_.LinearMap.toMatrix b b).injective
    apply Matrix.ext_iff_trace_mul_right.mpr
    intro Y
    have hY := h (Matrix.toLin b b Y)
    rw [_root_.LinearMap.trace_eq_matrix_trace K b,
      _root_.LinearMap.trace_eq_matrix_trace K b] at hY
    simpa only [_root_.LinearMap.toMatrix_mul, _root_.LinearMap.toMatrix_toLin] using hY

/-- An endomorphism whose product with every endomorphism has zero trace is zero. -/
theorem eq_zero_of_trace_mul_eq_zero [Module.Free K V] [Module.Finite K V]
    (f : Module.End K V)
    (h : ∀ g : Module.End K V, _root_.LinearMap.trace K V (f * g) = 0) : f = 0 := by
  rw [ext_iff_trace_mul_right]
  simpa using h

end TauCeti.LinearMap

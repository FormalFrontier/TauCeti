/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.Trace

/-!
# Traces of coordinate-reindexing maps

This file computes the trace of an endomorphism of a finite product that selects an input
coordinate for each output coordinate and applies a linear endomorphism there. Only fixed
coordinates contribute to the trace.

The result is the linear-algebra input for character formulas of induced representations.
-/

public section

namespace TauCeti

universe u v w

variable {k : Type u} {ι : Type v} {M : Type w}
  [Field k] [Fintype ι]
  [AddCommGroup M] [Module k M] [FiniteDimensional k M]

open scoped Classical in
/-- The trace of a coordinate-reindexing endomorphism of a finite product is the sum of the
traces on its fixed coordinates. -/
theorem LinearMap.trace_pi_of_apply_eq (T : (ι → M) →ₗ[k] (ι → M)) (σ : ι → ι)
    (f : ι → M →ₗ[k] M) (hT : ∀ x i, T x i = f i (x (σ i))) :
    LinearMap.trace k (ι → M) T =
      ∑ i : ι, if σ i = i then LinearMap.trace k M (f i) else 0 := by
  let b := Module.Free.chooseBasis k M
  letI := Fintype.ofFinite (Module.Free.ChooseBasisIndex k M)
  let B := Pi.basis fun _ : ι => b
  rw [LinearMap.trace_eq_matrix_trace k B, Matrix.trace]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : σ i = i
  · simp only [hi, ↓reduceIte]
    rw [LinearMap.trace_eq_matrix_trace k b, Matrix.trace]
    apply Finset.sum_congr rfl
    intro j _
    simp [LinearMap.toMatrix_apply, B, b, hT, hi]
  · simp only [hi, ↓reduceIte]
    apply Finset.sum_eq_zero
    intro j _
    simp [LinearMap.toMatrix_apply, B, b, hT, hi]

end TauCeti

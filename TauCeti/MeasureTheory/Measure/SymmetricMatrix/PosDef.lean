/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Analysis.Matrix.PosDef
public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# The positive-definite cone is open and measurable

On the symmetric subspace, positive definiteness cuts out an open subset: the Hermitian
condition holds identically there, so the cone is the preimage of the open set of matrices with
positive quadratic form, `TauCeti.isOpen_setOfPred_dotProduct_mulVec_pos`.

The Wishart densities of the standard-distributions roadmap are supported on this cone, so its
measurability is part of the carrier API.

## Main declarations

* `TauCeti.isOpen_setOfPred_posDefMatrix` — the positive-definite cone is open in the symmetric
  subspace.
* `TauCeti.measurableSet_posDefMatrix` — the positive-definite cone is measurable.

## References

* Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 6, item 1,
  **Symmetric matrices and their Lebesgue measure**.
-/

public section

noncomputable section

open scoped Matrix

namespace TauCeti

/-- The positive-definite cone is open in the symmetric subspace. -/
theorem isOpen_setOfPred_posDefMatrix (p : ℕ) :
    IsOpen {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
      (A : Matrix (Fin p) (Fin p) ℝ).PosDef} := by
  have hpre : {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
      (A : Matrix (Fin p) (Fin p) ℝ).PosDef} =
      Subtype.val ⁻¹'
        {M : Matrix (Fin p) (Fin p) ℝ | ∀ x : Fin p → ℝ, x ≠ 0 → 0 < x ⬝ᵥ M *ᵥ x} := by
    ext A
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Matrix.posDef_iff_dotProduct_mulVec]
    exact ⟨fun h x hx => by simpa using h.2 hx,
      fun h => ⟨isHermitian_coe A, fun x hx => by simpa using h x hx⟩⟩
  rw [hpre]
  exact (isOpen_setOfPred_dotProduct_mulVec_pos p).preimage continuous_subtype_val

/-- The positive-definite cone is measurable in the symmetric subspace. -/
theorem measurableSet_posDefMatrix (p : ℕ) :
    MeasurableSet {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
      (A : Matrix (Fin p) (Fin p) ℝ).PosDef} :=
  (isOpen_setOfPred_posDefMatrix p).measurableSet

end TauCeti

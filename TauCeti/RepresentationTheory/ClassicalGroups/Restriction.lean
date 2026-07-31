/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.Standard
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# The standard representation restricted to the special linear group

This file restricts the standard representation of `GL n k` along the canonical inclusion of
`SL n k`.  It records the action and character formulas in the special-linear presentation,
which are the input for the volume-preserving part of the classical-groups roadmap.

## Main definitions

* `TauCeti.stdSLRep` is the standard representation of `SL n k`.
* `TauCeti.stdSLFDRep` is its finite-dimensional bundled form.
* `TauCeti.stdSLDualRep` is its contragredient.

## References

* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md)
-/

public section

open Matrix

universe u

namespace TauCeti

variable (k : Type u) (n : ℕ)

section CommRing

variable [CommRing k]

/-- The standard representation of `SL n k`, restricting `stdRep` along its inclusion. -/
def stdSLRep : Representation k (Matrix.SpecialLinearGroup (Fin n) k) (Fin n → k) :=
  (stdRep k n).comp Matrix.SpecialLinearGroup.toGL

/-- The standard special-linear action is multiplication by the underlying matrix. -/
@[simp]
theorem stdSLRep_apply (g : Matrix.SpecialLinearGroup (Fin n) k) :
    stdSLRep k n g = Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k) := by
  simpa only [stdSLRep, MonoidHom.comp_apply, Matrix.SpecialLinearGroup.coe_GL_coe_matrix] using
    stdRep_apply k n (Matrix.SpecialLinearGroup.toGL g)

/-- Evaluation of the standard special-linear action is matrix-vector multiplication. -/
theorem stdSLRep_apply_apply (g : Matrix.SpecialLinearGroup (Fin n) k) (v : Fin n → k) :
    stdSLRep k n g v = (g : Matrix (Fin n) (Fin n) k) *ᵥ v := by
  rw [stdSLRep_apply, Matrix.mulVecLin_apply]

/-- The standard representation of `SL n k` is faithful. -/
theorem stdSLRep_injective : Function.Injective (stdSLRep k n) := by
  intro g h gh
  apply Matrix.SpecialLinearGroup.toGL_injective
  apply stdRep_injective k n
  simpa only [stdSLRep, MonoidHom.comp_apply] using gh

/-- The standard representation of `SL n k`, bundled as an object of `FDRep`. -/
noncomputable abbrev stdSLFDRep : FDRep k (Matrix.SpecialLinearGroup (Fin n) k) :=
  FDRep.of (stdSLRep k n)

/-- The dual, or contragredient, of the standard representation of `SL n k`. -/
noncomputable def stdSLDualRep :
    Representation k (Matrix.SpecialLinearGroup (Fin n) k) (Module.Dual k (Fin n → k)) :=
  (stdSLRep k n).dual

/-- The dual special-linear action is the transpose of the inverse matrix action. -/
@[simp]
theorem stdSLDualRep_apply (g : Matrix.SpecialLinearGroup (Fin n) k) :
    stdSLDualRep k n g =
      Module.Dual.transpose (R := k)
        (Matrix.mulVecLin
          ((g⁻¹ : Matrix.SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k)) := by
  rw [stdSLDualRep, Representation.dual_apply, stdSLRep_apply]

/-- The dual standard representation of `SL n k`, bundled as an object of `FDRep`. -/
noncomputable abbrev stdSLDualFDRep : FDRep k (Matrix.SpecialLinearGroup (Fin n) k) :=
  FDRep.of (stdSLDualRep k n)

end CommRing

section Field

variable [Field k]

/-- The character of the standard representation of `SL n k` is the matrix trace. -/
@[simp]
theorem char_stdSLRep (g : Matrix.SpecialLinearGroup (Fin n) k) :
    (stdSLRep k n).character g = Matrix.trace (g : Matrix (Fin n) (Fin n) k) := by
  simpa only [stdSLRep, Representation.character, MonoidHom.comp_apply,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix] using
    char_stdRep k n (Matrix.SpecialLinearGroup.toGL g)

/-- The character of the bundled standard representation of `SL n k` is the matrix trace. -/
@[simp]
theorem char_stdSLFDRep (g : Matrix.SpecialLinearGroup (Fin n) k) :
    (stdSLFDRep k n).character g = Matrix.trace (g : Matrix (Fin n) (Fin n) k) := by
  simpa only [FDRep.character, FDRep.of_ρ', Representation.character] using char_stdSLRep k n g

/-- The character of the dual standard representation of `SL n k` is the inverse matrix trace. -/
@[simp]
theorem char_stdSLDualRep (g : Matrix.SpecialLinearGroup (Fin n) k) :
    (stdSLDualRep k n).character g =
      Matrix.trace ((g⁻¹ : Matrix.SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  rw [stdSLDualRep, Representation.char_dual, char_stdSLRep]

/-- The bundled dual standard character of `SL n k` is the inverse matrix trace. -/
@[simp]
theorem char_stdSLDualFDRep (g : Matrix.SpecialLinearGroup (Fin n) k) :
    (stdSLDualFDRep k n).character g =
      Matrix.trace ((g⁻¹ : Matrix.SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  simpa only [FDRep.character, FDRep.of_ρ', Representation.character] using char_stdSLDualRep k n g

end Field

end TauCeti

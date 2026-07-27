/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RepresentationTheory.Character
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# The standard representation of the general linear group

This file defines the tautological representation of `GL n k` on column vectors, together with
its finite-dimensional and dual forms.  Its action and character are identified with matrix-vector
multiplication and the matrix trace.

## Main definitions

* `TauCeti.stdRep`: the standard representation of `GL n k`.
* `TauCeti.stdFDRep`: the standard representation as a finite-dimensional representation.
* `TauCeti.stdDualRep`: the contragredient of the standard representation.
-/

public section

open Matrix

universe u

namespace TauCeti

variable (k : Type u) (n : ℕ)

section CommRing

variable [CommRing k]

/-- The standard representation of `GL n k` on column vectors. -/
def stdRep : Representation k (GL (Fin n) k) (Fin n → k) :=
  (Units.coeHom ((Fin n → k) →ₗ[k] (Fin n → k))).comp
    Matrix.GeneralLinearGroup.toLin.toMonoidHom

/-- The standard representation acts by matrix-vector multiplication. -/
@[simp]
theorem stdRep_apply (g : GL (Fin n) k) :
    stdRep k n g = Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k) :=
  Matrix.GeneralLinearGroup.coe_toLin g

/-- Evaluation of the standard action is matrix-vector multiplication. -/
theorem stdRep_apply_apply (g : GL (Fin n) k) (v : Fin n → k) :
    stdRep k n g v = (g : Matrix (Fin n) (Fin n) k) *ᵥ v := by
  rw [stdRep_apply, Matrix.mulVecLin_apply]

/-- The standard representation is faithful. -/
theorem stdRep_injective : Function.Injective (stdRep k n) := by
  simpa [stdRep] using
    Units.coeHom_injective.comp Matrix.GeneralLinearGroup.toLin.injective

/-- The standard representation of `GL n k`, bundled as an object of `FDRep`. -/
noncomputable abbrev stdFDRep : FDRep k (GL (Fin n) k) :=
  FDRep.of (stdRep k n)

/-- The representation underlying the bundled standard representation. -/
@[simp]
theorem stdFDRep_ρ : (stdFDRep k n).ρ = stdRep k n := rfl

end CommRing

section Field

variable [Field k]

/-- The character of the standard representation is the matrix trace. -/
@[simp]
theorem stdRep_character (g : GL (Fin n) k) :
    (stdRep k n).character g = Matrix.trace (g : Matrix (Fin n) (Fin n) k) := by
  rw [Representation.character, stdRep_apply]
  exact Matrix.trace_toLin'_eq (g : Matrix (Fin n) (Fin n) k)

/-- The character of the bundled standard representation is the matrix trace. -/
@[simp]
theorem stdFDRep_character (g : GL (Fin n) k) :
    (stdFDRep k n).character g = Matrix.trace (g : Matrix (Fin n) (Fin n) k) := by
  simpa only [FDRep.character, stdFDRep_ρ, Representation.character] using
    stdRep_character k n g

end Field

section CommRing

variable [CommRing k]

/-- The dual, or contragredient, of the standard representation. -/
noncomputable def stdDualRep :
    Representation k (GL (Fin n) k) (Module.Dual k (Fin n → k)) :=
  (stdRep k n).dual

/-- The dual standard action is the transpose of the inverse standard action. -/
@[simp]
theorem stdDualRep_apply (g : GL (Fin n) k) :
    stdDualRep k n g =
      Module.Dual.transpose (R := k)
        (Matrix.mulVecLin ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) := by
  rw [stdDualRep, Representation.dual_apply, stdRep_apply]

/-- The dual standard representation, bundled as an object of `FDRep`. -/
noncomputable abbrev stdDualFDRep : FDRep k (GL (Fin n) k) :=
  FDRep.of (stdDualRep k n)

/-- The representation underlying the bundled dual standard representation. -/
@[simp]
theorem stdDualFDRep_ρ : (stdDualFDRep k n).ρ = stdDualRep k n := rfl

end CommRing

section Field

variable [Field k]

/-- The character of the dual standard representation is the trace at the inverse matrix. -/
@[simp]
theorem stdDualRep_character (g : GL (Fin n) k) :
    (stdDualRep k n).character g =
      Matrix.trace ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  rw [stdDualRep, Representation.char_dual, stdRep_character]

/-- The character of the bundled dual standard representation is the inverse matrix trace. -/
@[simp]
theorem stdDualFDRep_character (g : GL (Fin n) k) :
    (stdDualFDRep k n).character g =
      Matrix.trace ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  simpa only [FDRep.character, stdDualFDRep_ρ, Representation.character] using
    stdDualRep_character k n g

end Field

end TauCeti

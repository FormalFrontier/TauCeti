/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.Standard
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# The standard representation of the orthogonal group

This file restricts the standard representation of the general linear group to the orthogonal
group. It records the matrix action, its faithfulness, preservation of the standard symmetric
bilinear pairing, and the corresponding character formulas.

## Main definitions

* `TauCeti.stdOrthogonalRep` is the standard representation of `Matrix.orthogonalGroup`.
* `TauCeti.stdOrthogonalFDRep` is its finite-dimensional bundled form.
* `TauCeti.stdOrthogonalDualRep` is its contragredient.

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

attribute [local instance] starRingOfComm

/-- The standard representation of the orthogonal group on column vectors. -/
def stdOrthogonalRep : Representation k (Matrix.orthogonalGroup (Fin n) k) (Fin n → k) :=
  Units.coeHom ((Fin n → k) →ₗ[k] (Fin n → k)) |>.comp Matrix.UnitaryGroup.embeddingGL

/-- The standard orthogonal action is multiplication by the underlying matrix. -/
@[simp]
theorem stdOrthogonalRep_apply (g : Matrix.orthogonalGroup (Fin n) k) :
    stdOrthogonalRep k n g = Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k) :=
  Matrix.UnitaryGroup.coe_toGL g

/-- Evaluation of the standard orthogonal action is matrix-vector multiplication. -/
theorem stdOrthogonalRep_apply_apply (g : Matrix.orthogonalGroup (Fin n) k) (v : Fin n → k) :
    stdOrthogonalRep k n g v = (g : Matrix (Fin n) (Fin n) k) *ᵥ v :=
  LinearMap.congr_fun (stdOrthogonalRep_apply k n g) v

/-- The standard orthogonal action preserves the coordinate dot product. -/
theorem stdOrthogonalRep_dotProduct (g : Matrix.orthogonalGroup (Fin n) k) (v w : Fin n → k) :
    (stdOrthogonalRep k n g v) ⬝ᵥ (stdOrthogonalRep k n g w) = v ⬝ᵥ w := by
  rw [stdOrthogonalRep_apply_apply, stdOrthogonalRep_apply_apply]
  calc
    ((g : Matrix (Fin n) (Fin n) k) *ᵥ v) ⬝ᵥ ((g : Matrix (Fin n) (Fin n) k) *ᵥ w) =
        ((g : Matrix (Fin n) (Fin n) k) *ᵥ w) ⬝ᵥ ((g : Matrix (Fin n) (Fin n) k) *ᵥ v) :=
      dotProduct_comm _ _
    _ = v ⬝ᵥ ((g : Matrix (Fin n) (Fin n) k)ᵀ *ᵥ
          ((g : Matrix (Fin n) (Fin n) k) *ᵥ w)) :=
      (Matrix.dotProduct_transpose_mulVec (g : Matrix (Fin n) (Fin n) k) v
        ((g : Matrix (Fin n) (Fin n) k) *ᵥ w)).symm
    _ = v ⬝ᵥ (((g : Matrix (Fin n) (Fin n) k)ᵀ *
          (g : Matrix (Fin n) (Fin n) k)) *ᵥ w) := by
      rw [Matrix.mulVec_mulVec]
    _ = v ⬝ᵥ w := by
      have hstar : star (g : Matrix (Fin n) (Fin n) k) =
          (g : Matrix (Fin n) (Fin n) k)ᵀ := rfl
      rw [← hstar, Matrix.mem_unitaryGroup_iff'.mp g.prop, Matrix.one_mulVec]

/-- The standard representation of the orthogonal group is faithful. -/
theorem stdOrthogonalRep_injective : Function.Injective (stdOrthogonalRep k n) := by
  intro g h gh
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  have happly : (g : Matrix (Fin n) (Fin n) k) *ᵥ Pi.single j 1 =
      (h : Matrix (Fin n) (Fin n) k) *ᵥ Pi.single j 1 := by
    calc
      (g : Matrix (Fin n) (Fin n) k) *ᵥ Pi.single j 1 =
          stdOrthogonalRep k n g (Pi.single j 1) := rfl
      _ = stdOrthogonalRep k n h (Pi.single j 1) := LinearMap.congr_fun gh (Pi.single j 1)
      _ = (h : Matrix (Fin n) (Fin n) k) *ᵥ Pi.single j 1 := rfl
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using congr_fun happly i

/-- The standard representation of the orthogonal group, bundled as an object of `FDRep`. -/
noncomputable abbrev stdOrthogonalFDRep : FDRep k (Matrix.orthogonalGroup (Fin n) k) :=
  FDRep.of (stdOrthogonalRep k n)

/-- The dual, or contragredient, of the standard representation of the orthogonal group. -/
noncomputable def stdOrthogonalDualRep :
    Representation k (Matrix.orthogonalGroup (Fin n) k) (Module.Dual k (Fin n → k)) :=
  (stdOrthogonalRep k n).dual

/-- The dual standard orthogonal action is the transpose of the inverse matrix action. -/
@[simp]
theorem stdOrthogonalDualRep_apply (g : Matrix.orthogonalGroup (Fin n) k) :
    stdOrthogonalDualRep k n g =
      Module.Dual.transpose (R := k)
        (Matrix.mulVecLin ((g⁻¹ : Matrix.orthogonalGroup (Fin n) k) :
          Matrix (Fin n) (Fin n) k)) := by
  rw [stdOrthogonalDualRep, Representation.dual_apply, stdOrthogonalRep_apply]

/-- The dual standard representation of the orthogonal group, bundled as an object of `FDRep`. -/
noncomputable abbrev stdOrthogonalDualFDRep : FDRep k (Matrix.orthogonalGroup (Fin n) k) :=
  FDRep.of (stdOrthogonalDualRep k n)

end CommRing

section Field

variable [Field k]

attribute [local instance] starRingOfComm

/-- The character of the standard representation of the orthogonal group is the matrix trace. -/
@[simp]
theorem char_stdOrthogonalRep (g : Matrix.orthogonalGroup (Fin n) k) :
    (stdOrthogonalRep k n).character g = Matrix.trace (g : Matrix (Fin n) (Fin n) k) := by
  rw [Representation.character, stdOrthogonalRep_apply]
  exact Matrix.trace_toLin'_eq (g : Matrix (Fin n) (Fin n) k)

/-- The bundled standard orthogonal character is the matrix trace. -/
@[simp]
theorem char_stdOrthogonalFDRep (g : Matrix.orthogonalGroup (Fin n) k) :
    (stdOrthogonalFDRep k n).character g = Matrix.trace (g : Matrix (Fin n) (Fin n) k) := by
  simpa only [FDRep.character, FDRep.of_ρ', Representation.character] using
    char_stdOrthogonalRep k n g

/-- The dual standard orthogonal character is the inverse matrix trace. -/
@[simp]
theorem char_stdOrthogonalDualRep (g : Matrix.orthogonalGroup (Fin n) k) :
    (stdOrthogonalDualRep k n).character g =
      Matrix.trace ((g⁻¹ : Matrix.orthogonalGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  rw [stdOrthogonalDualRep, Representation.char_dual, char_stdOrthogonalRep]

/-- The bundled dual standard character of the orthogonal group is the inverse matrix trace. -/
@[simp]
theorem char_stdOrthogonalDualFDRep (g : Matrix.orthogonalGroup (Fin n) k) :
    (stdOrthogonalDualFDRep k n).character g =
      Matrix.trace ((g⁻¹ : Matrix.orthogonalGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  simpa only [FDRep.character, FDRep.of_ρ', Representation.character] using
    char_stdOrthogonalDualRep k n g

end Field

end TauCeti

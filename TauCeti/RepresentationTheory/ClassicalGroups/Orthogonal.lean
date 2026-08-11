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
* `TauCeti.stdOrthogonalRepEquivDual` is the equivariant self-duality induced by the dot product.

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

/-- The canonical inclusion of the orthogonal group into the general linear group. -/
def orthogonalGroupToGL : Matrix.orthogonalGroup (Fin n) k →* GL (Fin n) k :=
  Matrix.GeneralLinearGroup.toLin.symm.toMonoidHom.comp Matrix.UnitaryGroup.embeddingGL

/-- The orthogonal-to-general-linear inclusion has the original matrix as its underlying matrix. -/
@[simp]
theorem orthogonalGroupToGL_coe (g : Matrix.orthogonalGroup (Fin n) k) :
    (orthogonalGroupToGL k n g : Matrix (Fin n) (Fin n) k) = g := by
  apply Matrix.mulVec_injective
  funext v
  rw [← Matrix.mulVecLin_apply, ← Matrix.GeneralLinearGroup.coe_toLin]
  calc
    (Matrix.GeneralLinearGroup.toLin (orthogonalGroupToGL k n g) :
        (Fin n → k) →ₗ[k] Fin n → k) v =
        (Matrix.UnitaryGroup.embeddingGL g : (Fin n → k) →ₗ[k] Fin n → k) v := by
      simpa only [orthogonalGroupToGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using
        congrArg (fun f : LinearMap.GeneralLinearGroup k (Fin n → k) =>
          (f : (Fin n → k) →ₗ[k] Fin n → k) v)
          (Matrix.GeneralLinearGroup.toLin.apply_symm_apply
            (Matrix.UnitaryGroup.embeddingGL g))
    _ = Matrix.UnitaryGroup.toLin' g v :=
      LinearMap.congr_fun (Matrix.UnitaryGroup.coe_toGL g) v
    _ = (g : Matrix (Fin n) (Fin n) k) *ᵥ v := by
      simpa only [Matrix.UnitaryGroup.toLin'] using
        Matrix.toLin'_apply (g : Matrix (Fin n) (Fin n) k) v

/-- The canonical inclusion of the orthogonal group into the general linear group is injective. -/
theorem orthogonalGroupToGL_injective : Function.Injective (orthogonalGroupToGL k n) := by
  intro g h gh
  apply Subtype.ext
  have hcoe := congrArg (fun x : GL (Fin n) k => (x : Matrix (Fin n) (Fin n) k)) gh
  simpa only [orthogonalGroupToGL_coe] using hcoe

/-- The standard representation of the orthogonal group on column vectors. -/
def stdOrthogonalRep : Representation k (Matrix.orthogonalGroup (Fin n) k) (Fin n → k) :=
  (stdRep k n).comp (orthogonalGroupToGL k n)

/-- The standard orthogonal action is multiplication by the underlying matrix. -/
@[simp]
theorem stdOrthogonalRep_apply (g : Matrix.orthogonalGroup (Fin n) k) :
    stdOrthogonalRep k n g = Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k) := by
  simpa only [stdOrthogonalRep, MonoidHom.comp_apply, orthogonalGroupToGL_coe] using
    stdRep_apply k n (orthogonalGroupToGL k n g)

/-- Evaluation of the standard orthogonal action is matrix-vector multiplication. -/
theorem stdOrthogonalRep_apply_apply (g : Matrix.orthogonalGroup (Fin n) k) (v : Fin n → k) :
    stdOrthogonalRep k n g v = (g : Matrix (Fin n) (Fin n) k) *ᵥ v :=
  LinearMap.congr_fun (stdOrthogonalRep_apply k n g) v

/-- The standard orthogonal action preserves the coordinate dot product. -/
theorem stdOrthogonalRep_dotProduct_stdOrthogonalRep
    (g : Matrix.orthogonalGroup (Fin n) k) (v w : Fin n → k) :
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
      rw [(Matrix.mem_orthogonalGroup_iff' (Fin n) k).mp g.prop, Matrix.one_mulVec]

/-- The coordinate dot product identifies the standard module with its dual. -/
noncomputable def stdOrthogonalRepToDual : (Fin n → k) ≃ₗ[k] Module.Dual k (Fin n → k) :=
  (Pi.basisFun k (Fin n)).toDualEquiv

/-- `stdOrthogonalRepToDual` evaluates as the coordinate dot product. -/
theorem stdOrthogonalRepToDual_apply (v w : Fin n → k) :
    stdOrthogonalRepToDual k n v w = v ⬝ᵥ w := by
  rw [stdOrthogonalRepToDual, Module.Basis.toDualEquiv_apply]
  simp [Module.Basis.toDual, Pi.basisFun, dotProduct]

/-- The standard representation of the orthogonal group is faithful. -/
theorem stdOrthogonalRep_injective : Function.Injective (stdOrthogonalRep k n) := by
  intro g h gh
  apply orthogonalGroupToGL_injective k n
  apply stdRep_injective k n
  simpa only [stdOrthogonalRep, MonoidHom.comp_apply] using gh

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

/-- The coordinate-dot-product identification intertwines the standard and dual actions. -/
theorem stdOrthogonalRepToDual_equivariant (g : Matrix.orthogonalGroup (Fin n) k) :
    stdOrthogonalRepToDual k n ∘ₗ stdOrthogonalRep k n g =
      stdOrthogonalDualRep k n g ∘ₗ stdOrthogonalRepToDual k n := by
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro w
  -- Extensionality leaves coercions to functions opaque; this only exposes the displayed
  -- composition so that the public application lemmas below can rewrite it.
  change stdOrthogonalRepToDual k n (stdOrthogonalRep k n g v) w = _
  rw [stdOrthogonalRepToDual_apply]
  rw [stdOrthogonalDualRep_apply, LinearMap.comp_apply, Module.Dual.transpose_apply,
    LinearMap.comp_apply]
  -- The same coercion exposure lets `stdOrthogonalRepToDual_apply` describe the right side.
  change _ = stdOrthogonalRepToDual k n v
    (((g⁻¹ : Matrix.orthogonalGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ w)
  rw [stdOrthogonalRepToDual_apply, ← stdOrthogonalRep_apply_apply k n g⁻¹]
  calc
    stdOrthogonalRep k n g v ⬝ᵥ w =
        stdOrthogonalRep k n g v ⬝ᵥ
          stdOrthogonalRep k n g (stdOrthogonalRep k n g⁻¹ w) := by
      rw [Representation.self_inv_apply]
    _ = v ⬝ᵥ stdOrthogonalRep k n g⁻¹ w :=
      stdOrthogonalRep_dotProduct_stdOrthogonalRep k n g v (stdOrthogonalRep k n g⁻¹ w)

/-- The standard representation of the orthogonal group is equivariantly self-dual. -/
noncomputable def stdOrthogonalRepEquivDual :
    (stdOrthogonalRep k n).Equiv (stdOrthogonalDualRep k n) :=
  .mk (stdOrthogonalRepToDual k n) (stdOrthogonalRepToDual_equivariant k n)

/-- The orthogonal self-duality equivalence evaluates as the coordinate dot product. -/
@[simp]
theorem stdOrthogonalRepEquivDual_apply (v w : Fin n → k) :
    stdOrthogonalRepEquivDual k n v w = v ⬝ᵥ w :=
  stdOrthogonalRepToDual_apply k n v w

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
  simpa only [stdOrthogonalRep, Representation.character, MonoidHom.comp_apply,
    orthogonalGroupToGL_coe] using char_stdRep k n (orthogonalGroupToGL k n g)

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

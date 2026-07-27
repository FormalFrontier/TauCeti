/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.Standard
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.SymplecticGroup

/-!
# The standard representation of the symplectic group

This file restricts the standard representation of the general linear group to the symplectic
group. It defines the standard alternating form from `Matrix.J`, proves that the standard action
preserves it, and packages the resulting equivariant self-duality.

## Main definitions

* `TauCeti.symplecticGroupToGL` is the canonical inclusion into the general linear group.
* `TauCeti.stdSymplecticRep` is the standard representation of `Matrix.symplecticGroup`.
* `TauCeti.stdSymplecticBilinForm` is the nondegenerate invariant alternating form.
* `TauCeti.stdSymplecticRepEquivDual` is the induced equivariant self-duality.

## References

* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md),
  Layer 0.
-/

public section

open Matrix

universe u

namespace TauCeti

variable (k : Type u) (n : ℕ)

section CommRing

variable [CommRing k]

/-- The canonical inclusion of the symplectic group into the general linear group. -/
def symplecticGroupToGL :
    Matrix.symplecticGroup (Fin n) k →* GL (Fin n ⊕ Fin n) k where
  toFun g := Matrix.SpecialLinearGroup.toGL
    ⟨g, SymplecticGroup.det_eq_one g.2⟩
  map_one' := by
    ext i j
    rfl
  map_mul' g h := by
    ext i j
    rfl

/-- The symplectic-to-general-linear inclusion has the original matrix as underlying matrix. -/
@[simp]
theorem symplecticGroupToGL_coe (g : Matrix.symplecticGroup (Fin n) k) :
    (symplecticGroupToGL k n g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) = g :=
  (rfl)

/-- The canonical inclusion of the symplectic group into the general linear group is injective. -/
theorem symplecticGroupToGL_injective : Function.Injective (symplecticGroupToGL k n) := by
  intro g h hgh
  apply Subtype.ext
  simpa only [symplecticGroupToGL_coe] using
    congrArg (fun x : GL (Fin n ⊕ Fin n) k =>
      (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k)) hgh

/-- The standard representation of the symplectic group on column vectors. -/
def stdSymplecticRep :
    Representation k (Matrix.symplecticGroup (Fin n) k) ((Fin n ⊕ Fin n) → k) :=
  (Units.coeHom (((Fin n ⊕ Fin n) → k) →ₗ[k] ((Fin n ⊕ Fin n) → k))).comp
    (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp (symplecticGroupToGL k n))

/-- The standard symplectic action is multiplication by the underlying matrix. -/
@[simp]
theorem stdSymplecticRep_apply (g : Matrix.symplecticGroup (Fin n) k) :
    stdSymplecticRep k n g =
      Matrix.mulVecLin (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) := by
  -- Unfold the representation wrapper to expose the coercion from an invertible linear map.
  change (Matrix.GeneralLinearGroup.toLin (symplecticGroupToGL k n g) :
    ((Fin n ⊕ Fin n) → k) →ₗ[k] ((Fin n ⊕ Fin n) → k)) = _
  simpa only [symplecticGroupToGL_coe] using
    Matrix.GeneralLinearGroup.coe_toLin (symplecticGroupToGL k n g)

/-- Evaluation of the standard symplectic action is matrix-vector multiplication. -/
theorem stdSymplecticRep_apply_apply (g : Matrix.symplecticGroup (Fin n) k)
    (v : (Fin n ⊕ Fin n) → k) :
    stdSymplecticRep k n g v =
      (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) *ᵥ v :=
  LinearMap.congr_fun (stdSymplecticRep_apply k n g) v

/-- The standard representation of the symplectic group is faithful. -/
theorem stdSymplecticRep_injective : Function.Injective (stdSymplecticRep k n) := by
  intro g h hgh
  apply Subtype.ext
  apply Matrix.mulVec_injective
  funext v
  exact LinearMap.congr_fun
    ((stdSymplecticRep_apply k n g).symm.trans (hgh.trans (stdSymplecticRep_apply k n h))) v

/-- The standard representation of the symplectic group, bundled as an object of `FDRep`. -/
noncomputable abbrev stdSymplecticFDRep :
    FDRep k (Matrix.symplecticGroup (Fin n) k) :=
  FDRep.of (stdSymplecticRep k n)

/-- The standard alternating bilinear form represented by `Matrix.J`. -/
def stdSymplecticBilinForm :
    LinearMap.BilinForm k ((Fin n ⊕ Fin n) → k) :=
  Matrix.toBilin' (Matrix.J (Fin n) k)

/-- The standard symplectic form is `vᵀ J w`. -/
@[simp]
theorem stdSymplecticBilinForm_apply (v w : (Fin n ⊕ Fin n) → k) :
    stdSymplecticBilinForm k n v w = v ⬝ᵥ Matrix.J (Fin n) k *ᵥ w :=
  Matrix.toBilin'_apply' _ _ _

/-- The standard symplectic form is alternating. -/
theorem stdSymplecticBilinForm_isAlt : (stdSymplecticBilinForm k n).IsAlt := by
  intro v
  simp [stdSymplecticBilinForm_apply, Matrix.J, Matrix.fromBlocks_mulVec, dotProduct, mul_comm,
    Matrix.neg_mulVec]

/-- The standard symplectic form is nondegenerate. -/
theorem stdSymplecticBilinForm_nondegenerate :
    (stdSymplecticBilinForm k n).Nondegenerate := by
  rw [stdSymplecticBilinForm, Matrix.nondegenerate_toBilin'_iff,
    Matrix.nondegenerate_iff_forall_vecMul_and_mulVec_eq_zero]
  constructor
  · intro v hv
    have h := congrArg (fun w => w ᵥ* Matrix.J (Fin n) k) hv
    simpa [Matrix.vecMul_vecMul, Matrix.J_squared, Matrix.vecMul_neg] using h
  · intro v hv
    have h := congrArg (fun w => Matrix.J (Fin n) k *ᵥ w) hv
    simpa [Matrix.mulVec_mulVec, Matrix.J_squared, Matrix.neg_mulVec] using h

/-- The standard symplectic action preserves the standard alternating form. -/
@[simp]
theorem stdSymplecticBilinForm_comp_stdSymplecticRep
    (g : Matrix.symplecticGroup (Fin n) k) :
    (stdSymplecticBilinForm k n).comp
        (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k).mulVecLin
        (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k).mulVecLin =
      stdSymplecticBilinForm k n := by
  rw [stdSymplecticBilinForm, ← Matrix.toLin'_apply', Matrix.toBilin'_comp]
  rw [(SymplecticGroup.mem_iff' (l := Fin n) (R := k)).mp g.2]

/-- The standard symplectic pairing is invariant under the standard action. -/
@[simp]
theorem stdSymplecticBilinForm_stdSymplecticRep
    (g : Matrix.symplecticGroup (Fin n) k) (v w : (Fin n ⊕ Fin n) → k) :
    (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k).mulVec v ⬝ᵥ
        (Matrix.J (Fin n) k *
          (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k)).mulVec w =
      stdSymplecticBilinForm k n v w := by
  simpa only [LinearMap.BilinForm.comp_apply, stdSymplecticBilinForm_apply,
    Matrix.mulVecLin_apply, Matrix.mulVec_mulVec] using
    LinearMap.congr_fun
      (LinearMap.congr_fun (stdSymplecticBilinForm_comp_stdSymplecticRep k n g) v) w

end CommRing

section Field

variable [Field k]

/-- The standard symplectic form identifies the standard module with its dual. -/
noncomputable def stdSymplecticRepToDual :
    ((Fin n ⊕ Fin n) → k) ≃ₗ[k] Module.Dual k ((Fin n ⊕ Fin n) → k) :=
  (stdSymplecticBilinForm k n).toDual (stdSymplecticBilinForm_nondegenerate k n)

/-- The standard symplectic self-duality evaluates as the standard alternating form. -/
@[simp]
theorem stdSymplecticRepToDual_apply (v w : (Fin n ⊕ Fin n) → k) :
    stdSymplecticRepToDual k n v w = stdSymplecticBilinForm k n v w :=
  LinearMap.BilinForm.toDual_def (stdSymplecticBilinForm_nondegenerate k n)

/-- The dual, or contragredient, of the standard representation of the symplectic group. -/
noncomputable def stdSymplecticDualRep :
    Representation k (Matrix.symplecticGroup (Fin n) k)
      (Module.Dual k ((Fin n ⊕ Fin n) → k)) :=
  (stdSymplecticRep k n).dual

/-- The dual standard symplectic action is the transpose of the inverse matrix action. -/
@[simp]
theorem stdSymplecticDualRep_apply (g : Matrix.symplecticGroup (Fin n) k) :
    stdSymplecticDualRep k n g =
      Module.Dual.transpose (R := k)
        (Matrix.mulVecLin ((g⁻¹ : Matrix.symplecticGroup (Fin n) k) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k)) := by
  rw [stdSymplecticDualRep, Representation.dual_apply, stdSymplecticRep_apply]

/-- The standard-form identification intertwines the standard and dual actions. -/
theorem stdSymplecticRepToDual_equivariant
    (g : Matrix.symplecticGroup (Fin n) k) :
    stdSymplecticRepToDual k n ∘ₗ stdSymplecticRep k n g =
      stdSymplecticDualRep k n g ∘ₗ stdSymplecticRepToDual k n := by
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro w
  -- Extensionality leaves the displayed compositions hidden behind coercions.
  change stdSymplecticRepToDual k n (stdSymplecticRep k n g v) w = _
  rw [stdSymplecticRepToDual_apply]
  rw [stdSymplecticDualRep_apply, LinearMap.comp_apply, Module.Dual.transpose_apply,
    LinearMap.comp_apply]
  -- Expose the evaluation of the form-induced map on the right.
  change _ = stdSymplecticRepToDual k n v
    (((g⁻¹ : Matrix.symplecticGroup (Fin n) k) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) *ᵥ w)
  rw [stdSymplecticRepToDual_apply, ← stdSymplecticRep_apply_apply k n g⁻¹]
  calc
    stdSymplecticBilinForm k n (stdSymplecticRep k n g v) w =
        stdSymplecticBilinForm k n (stdSymplecticRep k n g v)
          (stdSymplecticRep k n g (stdSymplecticRep k n g⁻¹ w)) := by
      rw [Representation.self_inv_apply]
    _ = stdSymplecticBilinForm k n v (stdSymplecticRep k n g⁻¹ w) := by
      simpa only [stdSymplecticRep_apply, stdSymplecticBilinForm_apply,
        Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mul_assoc] using
        stdSymplecticBilinForm_stdSymplecticRep k n g v
          (stdSymplecticRep k n g⁻¹ w)

/-- The standard representation of the symplectic group is equivariantly self-dual. -/
noncomputable def stdSymplecticRepEquivDual :
    (stdSymplecticRep k n).Equiv (stdSymplecticDualRep k n) :=
  .mk (stdSymplecticRepToDual k n) (stdSymplecticRepToDual_equivariant k n)

/-- The symplectic self-duality equivalence evaluates as the standard alternating form. -/
@[simp]
theorem stdSymplecticRepEquivDual_apply (v w : (Fin n ⊕ Fin n) → k) :
    stdSymplecticRepEquivDual k n v w = stdSymplecticBilinForm k n v w :=
  stdSymplecticRepToDual_apply k n v w

/-- The dual standard symplectic representation, bundled as an object of `FDRep`. -/
noncomputable abbrev stdSymplecticDualFDRep :
    FDRep k (Matrix.symplecticGroup (Fin n) k) :=
  FDRep.of (stdSymplecticDualRep k n)

/-- The character of the standard symplectic representation is the matrix trace. -/
@[simp]
theorem char_stdSymplecticRep (g : Matrix.symplecticGroup (Fin n) k) :
    (stdSymplecticRep k n).character g =
      Matrix.trace (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) := by
  rw [Representation.character, stdSymplecticRep_apply, ← Matrix.toLin'_apply']
  exact Matrix.trace_toLin'_eq (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k)

/-- The bundled standard symplectic character is the matrix trace. -/
@[simp]
theorem char_stdSymplecticFDRep (g : Matrix.symplecticGroup (Fin n) k) :
    (stdSymplecticFDRep k n).character g =
      Matrix.trace (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) := by
  simpa only [FDRep.character, FDRep.of_ρ', Representation.character] using
    char_stdSymplecticRep k n g

/-- The dual standard symplectic character is the inverse matrix trace. -/
@[simp]
theorem char_stdSymplecticDualRep (g : Matrix.symplecticGroup (Fin n) k) :
    (stdSymplecticDualRep k n).character g =
      Matrix.trace ((g⁻¹ : Matrix.symplecticGroup (Fin n) k) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) := by
  rw [stdSymplecticDualRep, Representation.char_dual, char_stdSymplecticRep]

/-- The bundled dual standard symplectic character is the inverse matrix trace. -/
@[simp]
theorem char_stdSymplecticDualFDRep (g : Matrix.symplecticGroup (Fin n) k) :
    (stdSymplecticDualFDRep k n).character g =
      Matrix.trace ((g⁻¹ : Matrix.symplecticGroup (Fin n) k) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) := by
  simpa only [FDRep.character, FDRep.of_ρ', Representation.character] using
    char_stdSymplecticDualRep k n g

end Field

end TauCeti

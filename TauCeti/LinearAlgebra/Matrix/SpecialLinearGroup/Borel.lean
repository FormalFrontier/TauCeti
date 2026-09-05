/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.GroupTheory.Solvable
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Borel
import TauCeti.GroupTheory.DoubleCoset.Identity
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Solvable
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Solvable

/-!
# The upper-triangular subgroup of `SL₂`

The standard Borel subgroup of `SL₂(R)` consists of the determinant-one upper-triangular
matrices. Over a field, its two Bruhat cells are represented by the identity and by
`ModularGroup.S = !![0, -1; 1, 0]`. Thus the Borel together with `ModularGroup.S` generates
`SL₂`, and over an infinite field no larger solvable subgroup can contain it.

The maximal-solvability theorem is the abstract-group input for proving that the
upper-triangular closed subgroup scheme of `SL₂` is a Borel subgroup. The infinitude assumption
is used only to rule out solvability of `SL₂`; the Bruhat decomposition itself holds over every
field.

## Main declarations

* `TauCeti.SL2Borel`: the upper-triangular subgroup of `SL₂`.
* `TauCeti.SL2Borel.mem_doubleCoset_modularGroup_S_iff`: the big cell of the rank-one Bruhat
  decomposition is detected by the lower-left entry.
* `TauCeti.SL2Borel.closure_insert_modularGroup_S_eq_top`: the Borel and the Weyl element generate
  `SL₂`.
* `TauCeti.SL2Borel.le_of_isSolvable`: a solvable subgroup containing the Borel is contained in it.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §28.3.
* R. Steinberg, *Lectures on Chevalley Groups*, §3.
* The proofs of `closure_insert_modularGroup_S_eq_top` and `le_of_isSolvable` use the same generic
  two-double-coset lemmas as their `GL₂` counterparts.
-/

public section

open Matrix
open scoped MatrixGroups

namespace TauCeti

universe u

/-- The standard upper-triangular subgroup of `SL₂(R)`, obtained by pulling the
upper-triangular subgroup of `GL₂(R)` back along the canonical inclusion. -/
abbrev SL2Borel (R : Type u) [CommRing R] : Subgroup SL(2, R) :=
  (GL2Borel R).comap Matrix.SpecialLinearGroup.toGL

namespace SL2Borel

section CommRing

variable {R : Type u} [CommRing R]

private theorem coe_modularGroup_S :
    ((((ModularGroup.S : SL(2, ℤ)) : SL(2, R)) : SL(2, R)) :
        Matrix (Fin 2) (Fin 2) R) = !![0, -1; 1, 0] := by
  rw [Matrix.SpecialLinearGroup.coe_matrix_coe, ModularGroup.coe_S]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- An element of `SL₂(R)` belongs to the standard Borel exactly when its lower-left entry
vanishes. -/
theorem mem_iff {g : SL(2, R)} :
    g ∈ SL2Borel R ↔ (g : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 := by
  exact GL2Borel.mem_iff

/-- The lower-left entry of an element of the standard Borel subgroup vanishes. -/
@[simp]
theorem apply_one_zero (g : SL2Borel R) :
    (g : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 :=
  mem_iff.mp g.2

/-- The canonical inclusion from the `SL₂` Borel to the `GL₂` Borel. -/
def toGL2Borel : SL2Borel R →* GL2Borel R :=
  Matrix.SpecialLinearGroup.toGL.restrict fun _ hg ↦ hg

/-- The inclusion of the `SL₂` Borel into the `GL₂` Borel does not change the underlying
general linear matrix. -/
@[simp]
theorem coe_toGL2Borel (g : SL2Borel R) :
    (toGL2Borel g : GL (Fin 2) R) = Matrix.SpecialLinearGroup.toGL g.1 :=
  by
    simp only [toGL2Borel, MonoidHom.restrict, MonoidHom.codRestrict_apply,
      MonoidHom.domRestrict_apply]

/-- The inclusion from the `SL₂` Borel to the `GL₂` Borel is injective. -/
theorem toGL2Borel_injective : Function.Injective (toGL2Borel (R := R)) :=
  MonoidHom.restrict_injective _ Matrix.SpecialLinearGroup.toGL_injective

/-- The upper-triangular subgroup of `SL₂(R)` is solvable. -/
instance instIsSolvable : Group.IsSolvable (SL2Borel R) :=
  Group.isSolvable_of_isSolvable_injective (toGL2Borel_injective (R := R))

end CommRing

section Field

variable {F : Type u} [Field F]

/-- An element outside the upper-triangular subgroup of `SL₂(F)` lies in the big Bruhat cell
represented by `ModularGroup.S`. -/
theorem mem_doubleCoset_modularGroup_S_of_notMem {g : SL(2, F)} (hg : g ∉ SL2Borel F) :
    g ∈ DoubleCoset.doubleCoset (((ModularGroup.S : SL(2, ℤ)) : SL(2, F)))
      (SL2Borel F : Set SL(2, F)) (SL2Borel F : Set SL(2, F)) := by
  have hc : g 1 0 ≠ 0 := by
    simpa only [mem_iff, not_false_eq_true] using hg
  let x : SL(2, F) :=
    ⟨!![1, g 0 0 * (g 1 0)⁻¹; 0, 1], by simp [Matrix.det_fin_two_of]⟩
  let y : SL(2, F) :=
    ⟨!![g 1 0, g 1 1; 0, (g 1 0)⁻¹], by simp [Matrix.det_fin_two_of, hc]⟩
  have hx : x ∈ SL2Borel F := by
    rw [mem_iff]
    rfl
  have hy : y ∈ SL2Borel F := by
    rw [mem_iff]
    rfl
  refine DoubleCoset.mem_doubleCoset.mpr ⟨x, hx, y, hy, ?_⟩
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_modularGroup_S]
  dsimp only [x, y]
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [hc]
  · have hdet := g.2
    rw [Matrix.det_fin_two] at hdet
    simp
    field_simp
    linear_combination -hdet
  · simp [hc]
  · simp [hc]

/-- **The lower-left entry detects the big cell.** An element of `SL₂(F)` lies in the double
coset of `ModularGroup.S` by the standard Borel exactly when its lower-left entry is nonzero.

Not a `simp` lemma: `TauCeti.mem_doubleCoset_iff_mk_mem_orbit` rewrites double-coset membership
to orbit membership, so the left-hand side is not simp-normal. -/
theorem mem_doubleCoset_modularGroup_S_iff {g : SL(2, F)} :
    g ∈ DoubleCoset.doubleCoset (((ModularGroup.S : SL(2, ℤ)) : SL(2, F)))
      (SL2Borel F : Set SL(2, F)) (SL2Borel F : Set SL(2, F)) ↔ g 1 0 ≠ 0 := by
  constructor
  · intro hg
    obtain ⟨x, hx, y, hy, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hg
    have hx10 : x 1 0 = 0 := mem_iff.mp hx
    have hy10 : y 1 0 = 0 := mem_iff.mp hy
    have hxdet : x 0 0 * x 1 1 = 1 := by
      simpa only [Matrix.det_fin_two, hx10, mul_zero, sub_zero] using x.2
    have hydet : y 0 0 * y 1 1 = 1 := by
      simpa only [Matrix.det_fin_two, hy10, mul_zero, sub_zero] using y.2
    have hx11 : x 1 1 ≠ 0 := by
      intro h
      rw [h, mul_zero] at hxdet
      exact zero_ne_one hxdet
    have hy00 : y 0 0 ≠ 0 := by
      intro h
      rw [h, zero_mul] at hydet
      exact zero_ne_one hydet
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_modularGroup_S]
    simpa only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_one,
      Matrix.cons_val_zero, Matrix.head_cons, neg_mul, one_mul, zero_mul, add_zero, hx10, hy10,
      mul_zero, mul_one, zero_add] using mul_ne_zero hx11 hy00
  · intro hg
    exact mem_doubleCoset_modularGroup_S_of_notMem (mem_iff.not.mpr hg)

/-- The upper-triangular subgroup and the Weyl element `ModularGroup.S` generate `SL₂(F)`. -/
theorem closure_insert_modularGroup_S_eq_top :
    Subgroup.closure
        (insert (((ModularGroup.S : SL(2, ℤ)) : SL(2, F)))
          (SL2Borel F : Set SL(2, F))) = ⊤ := by
  exact closure_insert_eq_top_of_notMem_imp_mem_doubleCoset (SL2Borel F)
    ((ModularGroup.S : SL(2, ℤ)) : SL(2, F)) mem_doubleCoset_modularGroup_S_of_notMem

/-- Every solvable subgroup of `SL₂` over an infinite field that contains the standard Borel
is contained in it. -/
theorem le_of_isSolvable [Infinite F] (P : Subgroup SL(2, F)) [Group.IsSolvable P]
    (hBP : SL2Borel F ≤ P) : P ≤ SL2Borel F := by
  exact le_of_isSolvable_of_not_isSolvable_of_notMem_imp_mem_doubleCoset
    (SL2Borel F) P ((ModularGroup.S : SL(2, ℤ)) : SL(2, F))
    (Matrix.SpecialLinearGroup.not_isSolvable_fin_two F)
    mem_doubleCoset_modularGroup_S_of_notMem hBP

end Field

end SL2Borel

end TauCeti

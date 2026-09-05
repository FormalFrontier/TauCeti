/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.GroupTheory.Solvable
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Borel
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Solvable
import Mathlib.GroupTheory.IsPerfect

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
* `Matrix.SpecialLinearGroup.not_isSolvable_fin_two`: `SL₂` over an infinite field is not
  solvable.
* `TauCeti.SL2Borel.mem_doubleCoset_modularGroup_S_of_notMem`: the big-cell half of the rank-one
  Bruhat decomposition.
* `TauCeti.SL2Borel.closure_insert_modularGroup_S_eq_top`: the Borel and the Weyl element generate
  `SL₂`.
* `TauCeti.SL2Borel.le_of_isSolvable`: a solvable subgroup containing the Borel is contained in it.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §28.3.
* R. Steinberg, *Lectures on Chevalley Groups*, §3.
- The nonsolvability proof uses Mathlib's `Matrix.SL2.commutator_eq_top`.
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

namespace Matrix.SpecialLinearGroup

/-- The special linear group `SL₂` over an infinite field is not solvable. -/
theorem not_isSolvable_fin_two (F : Type u) [Field F] [Infinite F] :
    ¬ Group.IsSolvable SL(2, F) := by
  let S : Set F := {0} ∪ {1} ∪ {-1}
  let U := {x : F // x ∈ Sᶜ}
  let _ : Infinite U := (Set.toFinite S).infinite_compl.to_subtype
  obtain ⟨a, _, _⟩ := exists_pair_ne U
  have ha0 : (a : F) ≠ 0 := by
    intro h
    apply a.property
    simp [S, h]
  have ha1 : (a : F) ^ 2 ≠ 1 := by
    rw [sq_ne_one_iff]
    constructor
    · intro h
      apply a.property
      simp [S, h]
    · intro h
      apply a.property
      simp [S, h]
  let _ : Group.IsPerfect SL(2, F) := ⟨Matrix.SL2.commutator_eq_top ha0 ha1⟩
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  let t : SL(2, F) := Matrix.SpecialLinearGroup.transvection h01 1
  have ht : t ≠ 1 := by
    intro ht
    have hentry := congrArg
      (fun s : SL(2, F) ↦ (s : Matrix (Fin 2) (Fin 2) F) 0 1) ht
    simp [t, Matrix.SpecialLinearGroup.transvection_coe, Matrix.single] at hentry
  let _ : Nontrivial SL(2, F) := ⟨t, 1, ht⟩
  exact Group.IsPerfect.not_isSolvable SL(2, F)

end Matrix.SpecialLinearGroup

namespace SL2Borel

section CommRing

variable {R : Type u} [CommRing R]

/-- An element of `SL₂(R)` belongs to the standard Borel exactly when its lower-left entry
vanishes. -/
theorem mem_iff {g : SL(2, R)} :
    g ∈ SL2Borel R ↔ (g : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 := by
  exact GL2Borel.mem_iff

/-- The canonical inclusion from the `SL₂` Borel to the `GL₂` Borel. -/
def toGL2Borel : SL2Borel R →* GL2Borel R :=
  { toFun := fun g ↦ ⟨Matrix.SpecialLinearGroup.toGL g.1, g.2⟩
    map_one' := Subtype.ext (map_one Matrix.SpecialLinearGroup.toGL)
    map_mul' := fun g h ↦ Subtype.ext (map_mul Matrix.SpecialLinearGroup.toGL g.1 h.1) }

/-- The inclusion of the `SL₂` Borel into the `GL₂` Borel does not change the underlying
general linear matrix. -/
@[simp]
theorem coe_toGL2Borel (g : SL2Borel R) :
    (toGL2Borel g : GL (Fin 2) R) = Matrix.SpecialLinearGroup.toGL g.1 :=
  by
    rw [toGL2Borel]
    rfl

/-- The inclusion from the `SL₂` Borel to the `GL₂` Borel is injective. -/
theorem toGL2Borel_injective : Function.Injective (toGL2Borel (R := R)) := by
  intro g h hgh
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.toGL_injective
  exact congrArg Subtype.val hgh

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
  have hS :
      ((((ModularGroup.S : SL(2, ℤ)) : SL(2, F)) : SL(2, F)) :
          Matrix (Fin 2) (Fin 2) F) = !![0, -1; 1, 0] := by
    rw [Matrix.SpecialLinearGroup.coe_matrix_coe, ModularGroup.coe_S]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hS]
  change (g : Matrix (Fin 2) (Fin 2) F) =
    !![1, g 0 0 * (g 1 0)⁻¹; 0, 1] * !![0, -1; 1, 0] *
      !![g 1 0, g 1 1; 0, (g 1 0)⁻¹]
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

/-- The upper-triangular subgroup and the Weyl element `ModularGroup.S` generate `SL₂(F)`. -/
theorem closure_insert_modularGroup_S_eq_top :
    Subgroup.closure
        (insert (((ModularGroup.S : SL(2, ℤ)) : SL(2, F)))
          (SL2Borel F : Set SL(2, F))) = ⊤ := by
  refine eq_top_iff.mpr fun g _ ↦ ?_
  by_cases hg : g ∈ SL2Borel F
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ hg)
  · obtain ⟨x, hx, y, hy, rfl⟩ :=
      DoubleCoset.mem_doubleCoset.mp (mem_doubleCoset_modularGroup_S_of_notMem hg)
    exact mul_mem
      (mul_mem (Subgroup.subset_closure (Set.mem_insert_of_mem _ hx))
        (Subgroup.subset_closure (Set.mem_insert _ _)))
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ hy))

/-- Every solvable subgroup of `SL₂` over an infinite field that contains the standard Borel
is contained in it. -/
theorem le_of_isSolvable [Infinite F] (P : Subgroup SL(2, F)) [Group.IsSolvable P]
    (hBP : SL2Borel F ≤ P) : P ≤ SL2Borel F := by
  by_contra hPB
  obtain ⟨g, hgP, hgB⟩ := SetLike.not_le_iff_exists.mp hPB
  obtain ⟨x, hx, y, hy, hxy⟩ :=
    DoubleCoset.mem_doubleCoset.mp (mem_doubleCoset_modularGroup_S_of_notMem hgB)
  have hwP : ((ModularGroup.S : SL(2, ℤ)) : SL(2, F)) ∈ P := by
    have hxP := hBP hx
    have hyP := hBP hy
    have hprod : x⁻¹ * g * y⁻¹ ∈ P := mul_mem (mul_mem (inv_mem hxP) hgP) (inv_mem hyP)
    convert hprod using 1
    rw [hxy]
    group
  have hclosure :
      Subgroup.closure
          (insert (((ModularGroup.S : SL(2, ℤ)) : SL(2, F)))
            (SL2Borel F : Set SL(2, F))) ≤ P :=
    (Subgroup.closure_le P).mpr (Set.insert_subset_iff.mpr ⟨hwP, hBP⟩)
  rw [closure_insert_modularGroup_S_eq_top] at hclosure
  have hPtop : P = ⊤ := top_unique hclosure
  apply Matrix.SpecialLinearGroup.not_isSolvable_fin_two F
  apply Group.isSolvable_of_surjective (f := P.subtype)
  intro g
  refine ⟨⟨g, ?_⟩, rfl⟩
  rw [hPtop]
  exact Subgroup.mem_top g

end Field

end SL2Borel

end TauCeti

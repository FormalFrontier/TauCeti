/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.DiagramPermutations
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.B.RankTwo

/-!
# The special length-exchanging map of the pinned type `B₂` root datum

In characteristic two, the Suzuki construction uses a special isogeny of the simply connected
group of type `B₂`. At the root-datum level its character-lattice map exchanges the two Bourbaki
nodes and multiplies in the long-root direction. In the fundamental-weight coordinates of
`TauCeti.DynkinType.b2Root`, that map is

```text
A = !![0, 1; 2, 0].
```

This file computes the action of `A` on every root and of `Aᵀ` on every coroot. The induced root
permutation exchanges the two simple roots, the two other positive roots, and their negatives. The
rescaling exponent is the existing squared-length table `TauCeti.DynkinType.b2Length`: it is `1`
on short roots and `2` on long roots. Applying the data twice multiplies both lattices by `2`, and
the two exponents along each orbit multiply to `2`.

These equations are the explicit `B₂` input for the root-datum special-isogeny construction. They
do not yet construct a group-scheme morphism; Layer 9 of the reductive-groups roadmap requires that
later lift, together with its action on root subgroups, before the Suzuki--Ree lane can use it.

## Main definitions

* `TauCeti.DynkinType.b2SpecialIsogenyMatrix`: the character-lattice matrix.
* `TauCeti.DynkinType.b2SpecialIsogenyTableIndex`: the induced permutation of the coordinate-table
  indices.
* `TauCeti.DynkinType.b2SpecialIsogenyIndexEquiv`: the resulting permutation of the pinned datum's
  root indices.
* `TauCeti.DynkinType.b2SpecialIsogenyExponent`: the rescaling exponent on those indices.

## Main results

* `TauCeti.DynkinType.b2SpecialIsogenyMatrix_mulVec_root` and
  `TauCeti.DynkinType.b2SpecialIsogenyMatrix_transpose_mulVec_coroot`: the equations on the pinned
  datum.
* `TauCeti.DynkinType.b2SpecialIsogenyMatrix_mul_self`: the square of the lattice map is
  multiplication by `2`.
* `TauCeti.DynkinType.b2SpecialIsogenyExponent_mul_exponent`: the two rescaling exponents on an
  orbit multiply to the defining characteristic.

## References

The node numbering and coordinates follow Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*,
Plate II. The special-isogeny equations follow R. Steinberg, *Endomorphisms of Linear Algebraic
Groups*, §11; the Suzuki convention is also described in R. W. Carter, *Simple Groups of Lie
Type*, §§12.3--12.4. The exponent is `1` on long root subgroups and the characteristic on short
root subgroups when the group-scheme map is read contravariantly on its root datum. Here the
lattice map consequently rescales a root by its own squared length before exchanging its index.
-/

public section

namespace TauCeti.DynkinType

open Function

open scoped _root_.Matrix

/-! ## The lattice map and the root permutation -/

/-- The character-lattice matrix of the special length-exchanging map of the pinned `B₂` root
datum, in the fundamental-weight basis. -/
def b2SpecialIsogenyMatrix : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 2, 0]

/-- The explicit entries of the character-lattice special-isogeny matrix. -/
theorem b2SpecialIsogenyMatrix_def : b2SpecialIsogenyMatrix = !![0, 1; 2, 0] := (rfl)

/-- The permutation of the eight `B₂` roots induced by `TauCeti.DynkinType.b2SpecialIsogenyMatrix`.
It exchanges long roots with short roots and commutes with root negation. -/
def b2SpecialIsogenyTableIndex : Fin 8 → Fin 8 := ![1, 0, 3, 2, 5, 4, 7, 6]

/-- The explicit values of the special permutation on the coordinate-table indices. -/
theorem b2SpecialIsogenyTableIndex_def :
    b2SpecialIsogenyTableIndex = ![1, 0, 3, 2, 5, 4, 7, 6] := (rfl)

private lemma b2SpecialIsogenyTableIndex_involutive : Involutive b2SpecialIsogenyTableIndex := by
  intro i
  fin_cases i <;> decide

private def b2SpecialIsogenyTableIndexEquiv : Equiv.Perm (Fin 8) :=
  b2SpecialIsogenyTableIndex_involutive.toPerm _

private theorem b2SpecialIsogenyTableIndexEquiv_apply (i : Fin 8) :
    b2SpecialIsogenyTableIndexEquiv i = b2SpecialIsogenyTableIndex i := by
  rw [b2SpecialIsogenyTableIndexEquiv, Involutive.coe_toPerm]

private theorem b2SpecialIsogenyTableIndexEquiv_simple (i : Fin 2) :
    b2SpecialIsogenyTableIndexEquiv (Fin.castLE (by omega) i) =
      Fin.castLE (by omega) (lengthPermRankTwo i) := by
  fin_cases i <;>
    simp [b2SpecialIsogenyTableIndexEquiv_apply, b2SpecialIsogenyTableIndex]

/-- The special root permutation commutes with passing to the negative root. -/
@[simp] theorem b2SpecialIsogenyTableIndex_add_four (i : Fin 8) :
    b2SpecialIsogenyTableIndex (i + 4) = b2SpecialIsogenyTableIndex i + 4 := by
  decide +revert

/-- The special permutation on the native root indices of the pinned type `B₂` datum. It is the
coordinate-table permutation conjugated by `TauCeti.DynkinType.b2IndexEquiv`. -/
noncomputable def b2SpecialIsogenyIndexEquiv : Equiv.Perm (Fin (2 * 2 ^ 2)) :=
  b2IndexEquiv.symm.trans (b2SpecialIsogenyTableIndexEquiv.trans b2IndexEquiv)

/-- On a tabulated root, the native special permutation is the tabulated permutation. -/
@[simp] theorem b2SpecialIsogenyIndexEquiv_b2Index (i : Fin 8) :
    b2SpecialIsogenyIndexEquiv (b2Index i) =
      b2Index (b2SpecialIsogenyTableIndex i) := by
  rw [← b2IndexEquiv_apply]
  simp only [b2SpecialIsogenyIndexEquiv, Equiv.trans_apply, Equiv.symm_apply_apply,
    b2SpecialIsogenyTableIndexEquiv_apply]
  exact b2IndexEquiv_apply _

/-- Applying the special permutation twice fixes every native root index. -/
@[simp] theorem b2SpecialIsogenyIndexEquiv_apply_apply (i : Fin (2 * 2 ^ 2)) :
    b2SpecialIsogenyIndexEquiv (b2SpecialIsogenyIndexEquiv i) = i := by
  obtain ⟨j, rfl⟩ := b2Index_bijective.surjective i
  rw [b2SpecialIsogenyIndexEquiv_b2Index, b2SpecialIsogenyIndexEquiv_b2Index,
    b2SpecialIsogenyTableIndex_involutive]

private theorem b2SpecialIsogenyIndexEquiv_b2Index_simple (i : Fin 2) :
    b2SpecialIsogenyIndexEquiv (b2Index (Fin.castLE (by omega) i)) =
      b2Index (Fin.castLE (by omega) (lengthPermRankTwo i)) := by
  rw [b2SpecialIsogenyIndexEquiv_b2Index, ← b2SpecialIsogenyTableIndexEquiv_apply,
    b2SpecialIsogenyTableIndexEquiv_simple]

private theorem b2Index_castLE_eq_typeBSimpleIndex (i : Fin 2) :
    b2Index (Fin.castLE (by omega) i) = typeBSimpleIndex 2 i := by
  fin_cases i <;> simp

/-- On the pinned simple-root indices, the special permutation is the rank-two length
permutation. -/
@[simp] theorem b2SpecialIsogenyIndexEquiv_typeBSimpleIndex (i : Fin 2) :
    b2SpecialIsogenyIndexEquiv (typeBSimpleIndex 2 i) =
      typeBSimpleIndex 2 (lengthPermRankTwo i) := by
  rw [← b2Index_castLE_eq_typeBSimpleIndex, b2SpecialIsogenyIndexEquiv_b2Index_simple,
    b2Index_castLE_eq_typeBSimpleIndex]

/-- The exponent of the special map on the native root indices of the pinned type `B₂` datum. -/
noncomputable def b2SpecialIsogenyExponent (i : Fin (2 * 2 ^ 2)) : ℤ :=
  b2Length (b2IndexEquiv.symm i)

/-- On a tabulated root, the special exponent is its squared length. -/
@[simp] theorem b2SpecialIsogenyExponent_b2Index (i : Fin 8) :
    b2SpecialIsogenyExponent (b2Index i) = b2Length i := by
  rw [← b2IndexEquiv_apply]
  simp [b2SpecialIsogenyExponent]

/-- Every exponent of the special map is positive. -/
theorem b2SpecialIsogenyExponent_pos (i : Fin (2 * 2 ^ 2)) :
    0 < b2SpecialIsogenyExponent i := by
  obtain ⟨j, rfl⟩ := b2Index_bijective.surjective i
  rw [b2SpecialIsogenyExponent_b2Index]
  decide +revert

/-! ## Action on the pinned root datum -/

private theorem b2SpecialIsogenyMatrix_mulVec_b2Root (i : Fin 8) :
    b2SpecialIsogenyMatrix *ᵥ b2Root i =
      b2Length i • b2Root (b2SpecialIsogenyTableIndex i) := by
  decide +revert

private theorem b2SpecialIsogenyMatrix_transpose_mulVec_b2Coroot (i : Fin 8) :
    b2SpecialIsogenyMatrixᵀ *ᵥ b2Coroot (b2SpecialIsogenyTableIndex i) =
      b2Length i • b2Coroot i := by
  decide +revert

/-- **The special matrix carries every root of the pinned datum to its indexed image with the
prescribed exponent.** -/
theorem b2SpecialIsogenyMatrix_mulVec_root (i : Fin (2 * 2 ^ 2)) :
    b2SpecialIsogenyMatrix *ᵥ (typeBSimplyConnectedRootDatum 2).root i =
      b2SpecialIsogenyExponent i •
        (typeBSimplyConnectedRootDatum 2).root (b2SpecialIsogenyIndexEquiv i) := by
  obtain ⟨j, rfl⟩ := b2Index_bijective.surjective i
  rw [root_b2Index, b2SpecialIsogenyExponent_b2Index,
    b2SpecialIsogenyIndexEquiv_b2Index, root_b2Index]
  exact b2SpecialIsogenyMatrix_mulVec_b2Root j

/-- **The transposed special matrix satisfies the contragredient equation on every coroot of the
pinned datum.** -/
theorem b2SpecialIsogenyMatrix_transpose_mulVec_coroot
    (i : Fin (2 * 2 ^ 2)) :
    b2SpecialIsogenyMatrixᵀ *ᵥ
        (typeBSimplyConnectedRootDatum 2).coroot (b2SpecialIsogenyIndexEquiv i) =
      b2SpecialIsogenyExponent i • (typeBSimplyConnectedRootDatum 2).coroot i := by
  obtain ⟨j, rfl⟩ := b2Index_bijective.surjective i
  rw [b2SpecialIsogenyIndexEquiv_b2Index, coroot_b2Index,
    b2SpecialIsogenyExponent_b2Index, coroot_b2Index]
  exact b2SpecialIsogenyMatrix_transpose_mulVec_b2Coroot j

/-- The square of the character-lattice special matrix is twice the identity matrix. -/
theorem b2SpecialIsogenyMatrix_mul_self :
    b2SpecialIsogenyMatrix * b2SpecialIsogenyMatrix =
      (2 : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [b2SpecialIsogenyMatrix_def, Matrix.mul_apply, Fin.sum_univ_succ]

/-! ## Length and exponent conventions -/

private theorem b2Length_mul_b2Length_specialIsogenyTableIndex (i : Fin 8) :
    b2Length i * b2Length (b2SpecialIsogenyTableIndex i) = 2 := by
  decide +revert

/-- The exponents at a native root index and its image multiply to the characteristic `2`. -/
@[simp] theorem b2SpecialIsogenyExponent_mul_exponent (i : Fin (2 * 2 ^ 2)) :
    b2SpecialIsogenyExponent i *
      b2SpecialIsogenyExponent (b2SpecialIsogenyIndexEquiv i) = 2 := by
  obtain ⟨j, rfl⟩ := b2Index_bijective.surjective i
  rw [b2SpecialIsogenyExponent_b2Index, b2SpecialIsogenyIndexEquiv_b2Index,
    b2SpecialIsogenyExponent_b2Index]
  exact b2Length_mul_b2Length_specialIsogenyTableIndex j

/-- Every rescaling exponent of the special map is either `1` or the characteristic `2`. -/
theorem b2SpecialIsogenyExponent_eq_one_or_eq_two (i : Fin (2 * 2 ^ 2)) :
    b2SpecialIsogenyExponent i = 1 ∨ b2SpecialIsogenyExponent i = 2 := by
  obtain ⟨j, rfl⟩ := b2Index_bijective.surjective i
  rw [b2SpecialIsogenyExponent_b2Index]
  decide +revert

private theorem b2SpecialIsogenyExponent_b2Index_simple (i : Fin 2) :
    b2SpecialIsogenyExponent (b2Index (Fin.castLE (by omega) i)) =
      (B 2).rootLength i := by
  rw [b2SpecialIsogenyExponent_b2Index, b2Length_castLE]

/-- On a pinned simple-root index, the special exponent is its normalised squared length. -/
@[simp] theorem b2SpecialIsogenyExponent_typeBSimpleIndex (i : Fin 2) :
    b2SpecialIsogenyExponent (typeBSimpleIndex 2 i) = (B 2).rootLength i := by
  rw [← b2Index_castLE_eq_typeBSimpleIndex, b2SpecialIsogenyExponent_b2Index_simple]

/-- At a pinned simple-root index, the special exponent is `1` exactly on a short node. -/
theorem b2SpecialIsogenyExponent_typeBSimpleIndex_eq_one_iff (i : Fin 2) :
    b2SpecialIsogenyExponent (typeBSimpleIndex 2 i) = 1 ↔
      ¬ (B 2).IsLongSimpleRoot i := by
  rw [b2SpecialIsogenyExponent_typeBSimpleIndex, rootLength_B, isLongSimpleRoot_B]
  fin_cases i <;> simp

end TauCeti.DynkinType

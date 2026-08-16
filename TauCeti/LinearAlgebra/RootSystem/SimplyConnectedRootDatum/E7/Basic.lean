/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.RootSystem.DynkinType
public import Mathlib.Data.Fin.Tuple.Embedding

public section

/-!
# The integral roots of type E7

This file enumerates the 126 roots of type `E7` in the lattices used by the pinned simply connected
root datum constructed in `TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E7.Datum`.
Coroots are expressed in the simple-coroot basis and roots in the fundamental-weight basis. The
first seven entries are the Bourbaki simple roots; the remaining positive roots are ordered by
height, followed by their negatives. Completeness of the table among the norm-two vectors is proved
in `TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E7.Lattice`.

The enumeration is the root-data input for Layer 6 of the root-systems roadmap. It follows
Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VI.
-/

namespace TauCeti

open _root_.Matrix

namespace DynkinType

/-- The 63 positive `E7` coroots in the simple-coroot basis, ordered by height. -/
-- The literals below are laid out as seven rows of nine so that a table lookup unfolds through at
-- most sixteen entries; the grouping has no mathematical content.
@[expose] def e7PositiveCoroot (i : Fin 63) : Fin 7 → ℤ :=
  ![![![1, 0, 0, 0, 0, 0, 0],
      ![0, 1, 0, 0, 0, 0, 0],
      ![0, 0, 1, 0, 0, 0, 0],
      ![0, 0, 0, 1, 0, 0, 0],
      ![0, 0, 0, 0, 1, 0, 0],
      ![0, 0, 0, 0, 0, 1, 0],
      ![0, 0, 0, 0, 0, 0, 1],
      ![0, 0, 0, 0, 0, 1, 1],
      ![0, 0, 0, 0, 1, 1, 0]],
    ![![0, 0, 0, 1, 1, 0, 0],
      ![0, 0, 1, 1, 0, 0, 0],
      ![0, 1, 0, 1, 0, 0, 0],
      ![1, 0, 1, 0, 0, 0, 0],
      ![0, 0, 0, 0, 1, 1, 1],
      ![0, 0, 0, 1, 1, 1, 0],
      ![0, 0, 1, 1, 1, 0, 0],
      ![0, 1, 0, 1, 1, 0, 0],
      ![0, 1, 1, 1, 0, 0, 0]],
    ![![1, 0, 1, 1, 0, 0, 0],
      ![0, 0, 0, 1, 1, 1, 1],
      ![0, 0, 1, 1, 1, 1, 0],
      ![0, 1, 0, 1, 1, 1, 0],
      ![0, 1, 1, 1, 1, 0, 0],
      ![1, 0, 1, 1, 1, 0, 0],
      ![1, 1, 1, 1, 0, 0, 0],
      ![0, 0, 1, 1, 1, 1, 1],
      ![0, 1, 0, 1, 1, 1, 1]],
    ![![0, 1, 1, 1, 1, 1, 0],
      ![0, 1, 1, 2, 1, 0, 0],
      ![1, 0, 1, 1, 1, 1, 0],
      ![1, 1, 1, 1, 1, 0, 0],
      ![0, 1, 1, 1, 1, 1, 1],
      ![0, 1, 1, 2, 1, 1, 0],
      ![1, 0, 1, 1, 1, 1, 1],
      ![1, 1, 1, 1, 1, 1, 0],
      ![1, 1, 1, 2, 1, 0, 0]],
    ![![0, 1, 1, 2, 1, 1, 1],
      ![0, 1, 1, 2, 2, 1, 0],
      ![1, 1, 1, 1, 1, 1, 1],
      ![1, 1, 1, 2, 1, 1, 0],
      ![1, 1, 2, 2, 1, 0, 0],
      ![0, 1, 1, 2, 2, 1, 1],
      ![1, 1, 1, 2, 1, 1, 1],
      ![1, 1, 1, 2, 2, 1, 0],
      ![1, 1, 2, 2, 1, 1, 0]],
    ![![0, 1, 1, 2, 2, 2, 1],
      ![1, 1, 1, 2, 2, 1, 1],
      ![1, 1, 2, 2, 1, 1, 1],
      ![1, 1, 2, 2, 2, 1, 0],
      ![1, 1, 1, 2, 2, 2, 1],
      ![1, 1, 2, 2, 2, 1, 1],
      ![1, 1, 2, 3, 2, 1, 0],
      ![1, 1, 2, 2, 2, 2, 1],
      ![1, 1, 2, 3, 2, 1, 1]],
    ![![1, 2, 2, 3, 2, 1, 0],
      ![1, 1, 2, 3, 2, 2, 1],
      ![1, 2, 2, 3, 2, 1, 1],
      ![1, 1, 2, 3, 3, 2, 1],
      ![1, 2, 2, 3, 2, 2, 1],
      ![1, 2, 2, 3, 3, 2, 1],
      ![1, 2, 2, 4, 3, 2, 1],
      ![1, 2, 3, 4, 3, 2, 1],
      ![2, 2, 3, 4, 3, 2, 1]]]
    ⟨(i : ℕ) / 9, by omega⟩ ⟨(i : ℕ) % 9, by omega⟩

private def e7PositiveCorootEmbedding : Fin 63 ↪ (Fin 7 → ℤ) where
  toFun := e7PositiveCoroot
  inj' := by decide

private lemma e7PositiveCoroot_ne_neg (i j : Fin 63) :
    e7PositiveCoroot i ≠ -e7PositiveCoroot j := by
  fin_cases i <;> fin_cases j <;> decide

private def e7NegativeCorootEmbedding : Fin 63 ↪ (Fin 7 → ℤ) :=
  e7PositiveCorootEmbedding.trans (Equiv.neg (Fin 7 → ℤ)).toEmbedding

private lemma e7Coroot_disjoint :
    Disjoint (Set.range e7PositiveCorootEmbedding) (Set.range e7NegativeCorootEmbedding) := by
  rw [Set.disjoint_range_iff]
  exact e7PositiveCoroot_ne_neg

/-- The 126 `E7` coroots in the simple-coroot basis, with positive roots followed by negatives. -/
def e7Coroot : Fin 126 ↪ (Fin 7 → ℤ) :=
  Fin.Embedding.append e7Coroot_disjoint

private theorem e7Coroot_coe :
    ⇑e7Coroot = Fin.append (⇑e7PositiveCorootEmbedding) fun i ↦ -e7PositiveCoroot i :=
  Fin.Embedding.coe_append _

/-- Evaluate an `E7` coroot through the exposed table of positive coroots. -/
@[grind =] theorem e7Coroot_apply (i : Fin 126) :
    e7Coroot i = if hi : (i : ℕ) < 63 then e7PositiveCoroot ⟨i, hi⟩ else
      -e7PositiveCoroot ⟨(i : ℕ) - 63, by omega⟩ := by
  refine Fin.addCases (m := 63) (n := 63) ?_ ?_ i
  · intro j
    rw [e7Coroot_coe, Fin.append_left]
    simp
    rfl
  · intro j
    rw [e7Coroot_coe, Fin.append_right]
    simp

/-- The 126 `E7` roots in the fundamental-weight basis. -/
def e7Root : Fin 126 ↪ (Fin 7 → ℤ) where
  toFun i := e7Coroot i ᵥ* CartanMatrix.E₇
  inj' := by
    intro i j hij
    apply e7Coroot.injective
    apply sub_eq_zero.mp
    apply Matrix.eq_zero_of_vecMul_eq_zero (by rw [CartanMatrix.E₇_det]; norm_num)
    rw [sub_vecMul]
    exact sub_eq_zero.mpr hij

/-- Each `E7` root is the `E7` Cartan matrix applied to the corresponding coroot. -/
-- This is not a simp theorem because it would rewrite the root-table lemmas below.
theorem e7Root_apply (i : Fin 126) : e7Root i = e7Coroot i ᵥ* CartanMatrix.E₇ := (rfl)

/-- The `E7` roots are the images of the coroots under the Cartan matrix, read on the left or,
equivalently, on the right, the matrix being symmetric. -/
theorem e7Root_eq_mulVec (i : Fin 126) : e7Root i = CartanMatrix.E₇ *ᵥ e7Coroot i := by
  rw [e7Root_apply, ← mulVec_transpose, CartanMatrix.E₇_isSymm]

/-- The negative half of the coroot table is the negation of the positive half. -/
@[simp, grind =] theorem e7Coroot_addNat (i : Fin 63) :
    e7Coroot (Fin.addNat i 63) = -e7Coroot (Fin.castAdd 63 i) := by
  rw [← Fin.natAdd_eq_addNat, e7Coroot_coe, Fin.append_right, Fin.append_left]
  rfl

/-- The negative half of the root table is the negation of the positive half. -/
@[simp, grind =] theorem e7Root_addNat (i : Fin 63) :
    e7Root (Fin.addNat i 63) = -e7Root (Fin.castAdd 63 i) := by
  rw [e7Root_apply, e7Root_apply, e7Coroot_addNat, Matrix.neg_vecMul]

/-- Every listed `E7` root pairs to two with its corresponding coroot. -/
@[simp, grind =] theorem e7Root_dotProduct_coroot (i : Fin 126) : e7Root i ⬝ᵥ e7Coroot i = 2 := by
  fin_cases i <;> decide

/-- The index of the `i`-th Bourbaki simple root in the pinned `E₇` enumeration. -/
def e7SimpleIndex (i : Fin 7) : Fin 126 := Fin.castAdd 119 i

@[simp] lemma e7SimpleIndex_val (i : Fin 7) : (e7SimpleIndex i : ℕ) = i := (rfl)

lemma e7SimpleIndex_injective : Function.Injective e7SimpleIndex :=
  Fin.castAdd_injective 7 119

/-- The simple coroots of the pinned `E₇` datum are the standard basis vectors. -/
@[simp, grind =] theorem coroot_e7SimpleIndex (i : Fin 7) :
    e7Coroot (e7SimpleIndex i) = Pi.single i 1 := by
  fin_cases i <;> decide

/-- The simple roots of the pinned `E₇` datum are the rows of the Bourbaki Cartan matrix. -/
@[simp, grind =] theorem root_e7SimpleIndex (i : Fin 7) :
    e7Root (e7SimpleIndex i) = CartanMatrix.E₇ i := by
  rw [e7Root_apply, coroot_e7SimpleIndex, Matrix.single_one_vecMul]
  rfl

/-- Every positive `E7` coroot has nonnegative simple-coroot coordinates. -/
theorem e7Coroot_nonneg (i : Fin 63) (j : Fin 7) : 0 ≤ e7Coroot (Fin.castAdd 63 i) j := by
  fin_cases i <;> fin_cases j <;> decide

/-- The last positive entry of the coroot table has the Bourbaki marks `(2, 2, 3, 4, 3, 2, 1)`. -/
@[simp, grind =] theorem e7Coroot_apply_62 : e7Coroot 62 = ![2, 2, 3, 4, 3, 2, 1] := by decide

/-- The last positive entry of the root table has fundamental-weight coordinates
`(1, 0, 0, 0, 0, 0, 0)`. -/
@[simp, grind =] theorem e7Root_apply_62 : e7Root 62 = ![1, 0, 0, 0, 0, 0, 0] := by decide

/-- The last positive entry is the highest `E7` coroot: it dominates every entry of the table
in each simple-coroot coordinate. -/
theorem e7Coroot_le_apply_62 (i : Fin 126) (j : Fin 7) : e7Coroot i j ≤ e7Coroot 62 j := by
  revert j
  fin_cases i <;> decide

end DynkinType
end TauCeti

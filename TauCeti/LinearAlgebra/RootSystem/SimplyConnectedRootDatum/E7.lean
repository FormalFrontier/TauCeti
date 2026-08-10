/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.RootSystem.DynkinType
public import Mathlib.LinearAlgebra.Matrix.Dual

public section

/-!
# The integral roots of type E7

This file enumerates the 126 roots of type `E7` in the lattices used by the future pinned simply
connected root datum. Coroots are expressed in the simple-coroot basis and roots in the
fundamental-weight basis. The first seven entries are the Bourbaki simple roots; the remaining
positive roots are ordered by height, followed by their negatives.

The enumeration is the root-data input for Layer 6 of the root-systems roadmap. It follows
Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VI.
-/

namespace TauCeti
open _root_.Matrix
namespace DynkinType

private def e7PositiveCorootChunk0 : Fin 9 → (Fin 7 → ℤ) := ![
  ![1, 0, 0, 0, 0, 0, 0],
  ![0, 1, 0, 0, 0, 0, 0],
  ![0, 0, 1, 0, 0, 0, 0],
  ![0, 0, 0, 1, 0, 0, 0],
  ![0, 0, 0, 0, 1, 0, 0],
  ![0, 0, 0, 0, 0, 1, 0],
  ![0, 0, 0, 0, 0, 0, 1],
  ![0, 0, 0, 0, 0, 1, 1],
  ![0, 0, 0, 0, 1, 1, 0]
]

private def e7PositiveCorootChunk1 : Fin 9 → (Fin 7 → ℤ) := ![
  ![0, 0, 0, 1, 1, 0, 0],
  ![0, 0, 1, 1, 0, 0, 0],
  ![0, 1, 0, 1, 0, 0, 0],
  ![1, 0, 1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 1, 1, 1],
  ![0, 0, 0, 1, 1, 1, 0],
  ![0, 0, 1, 1, 1, 0, 0],
  ![0, 1, 0, 1, 1, 0, 0],
  ![0, 1, 1, 1, 0, 0, 0]
]

private def e7PositiveCorootChunk2 : Fin 9 → (Fin 7 → ℤ) := ![
  ![1, 0, 1, 1, 0, 0, 0],
  ![0, 0, 0, 1, 1, 1, 1],
  ![0, 0, 1, 1, 1, 1, 0],
  ![0, 1, 0, 1, 1, 1, 0],
  ![0, 1, 1, 1, 1, 0, 0],
  ![1, 0, 1, 1, 1, 0, 0],
  ![1, 1, 1, 1, 0, 0, 0],
  ![0, 0, 1, 1, 1, 1, 1],
  ![0, 1, 0, 1, 1, 1, 1]
]

private def e7PositiveCorootChunk3 : Fin 9 → (Fin 7 → ℤ) := ![
  ![0, 1, 1, 1, 1, 1, 0],
  ![0, 1, 1, 2, 1, 0, 0],
  ![1, 0, 1, 1, 1, 1, 0],
  ![1, 1, 1, 1, 1, 0, 0],
  ![0, 1, 1, 1, 1, 1, 1],
  ![0, 1, 1, 2, 1, 1, 0],
  ![1, 0, 1, 1, 1, 1, 1],
  ![1, 1, 1, 1, 1, 1, 0],
  ![1, 1, 1, 2, 1, 0, 0]
]

private def e7PositiveCorootChunk4 : Fin 9 → (Fin 7 → ℤ) := ![
  ![0, 1, 1, 2, 1, 1, 1],
  ![0, 1, 1, 2, 2, 1, 0],
  ![1, 1, 1, 1, 1, 1, 1],
  ![1, 1, 1, 2, 1, 1, 0],
  ![1, 1, 2, 2, 1, 0, 0],
  ![0, 1, 1, 2, 2, 1, 1],
  ![1, 1, 1, 2, 1, 1, 1],
  ![1, 1, 1, 2, 2, 1, 0],
  ![1, 1, 2, 2, 1, 1, 0]
]

private def e7PositiveCorootChunk5 : Fin 9 → (Fin 7 → ℤ) := ![
  ![0, 1, 1, 2, 2, 2, 1],
  ![1, 1, 1, 2, 2, 1, 1],
  ![1, 1, 2, 2, 1, 1, 1],
  ![1, 1, 2, 2, 2, 1, 0],
  ![1, 1, 1, 2, 2, 2, 1],
  ![1, 1, 2, 2, 2, 1, 1],
  ![1, 1, 2, 3, 2, 1, 0],
  ![1, 1, 2, 2, 2, 2, 1],
  ![1, 1, 2, 3, 2, 1, 1]
]

private def e7PositiveCorootChunk6 : Fin 9 → (Fin 7 → ℤ) := ![
  ![1, 2, 2, 3, 2, 1, 0],
  ![1, 1, 2, 3, 2, 2, 1],
  ![1, 2, 2, 3, 2, 1, 1],
  ![1, 1, 2, 3, 3, 2, 1],
  ![1, 2, 2, 3, 2, 2, 1],
  ![1, 2, 2, 3, 3, 2, 1],
  ![1, 2, 2, 4, 3, 2, 1],
  ![1, 2, 3, 4, 3, 2, 1],
  ![2, 2, 3, 4, 3, 2, 1]
]

private def e7PositiveCoroot (i : Fin 63) : Fin 7 → ℤ :=
  if h : (i : ℕ) < 9 then e7PositiveCorootChunk0 ⟨i, h⟩
  else if h : (i : ℕ) < 18 then e7PositiveCorootChunk1 ⟨(i : ℕ) - 9, by omega⟩
  else if h : (i : ℕ) < 27 then e7PositiveCorootChunk2 ⟨(i : ℕ) - 18, by omega⟩
  else if h : (i : ℕ) < 36 then e7PositiveCorootChunk3 ⟨(i : ℕ) - 27, by omega⟩
  else if h : (i : ℕ) < 45 then e7PositiveCorootChunk4 ⟨(i : ℕ) - 36, by omega⟩
  else if h : (i : ℕ) < 54 then e7PositiveCorootChunk5 ⟨(i : ℕ) - 45, by omega⟩
  else e7PositiveCorootChunk6 ⟨(i : ℕ) - 54, by omega⟩

private lemma e7PositiveCoroot_injective : Function.Injective e7PositiveCoroot := by decide
private lemma e7PositiveCoroot_ne_neg (i j : Fin 63) :
    e7PositiveCoroot i ≠ -e7PositiveCoroot j := by
  fin_cases i <;> fin_cases j <;> decide

/-- The 126 `E7` coroots in the simple-coroot basis, with positive roots followed by negatives. -/
def e7Coroot : Fin 126 ↪ (Fin 7 → ℤ) where
  toFun i := if hi : (i : ℕ) < 63 then e7PositiveCoroot ⟨i, hi⟩ else
    -e7PositiveCoroot ⟨(i : ℕ) - 63, by omega⟩
  inj' := by
    intro i j hij
    by_cases hi : (i : ℕ) < 63 <;> by_cases hj : (j : ℕ) < 63
    · simp only [hi, hj, dite_true] at hij
      apply Fin.ext
      simpa using congrArg Fin.val (e7PositiveCoroot_injective hij)
    · simp only [hi, hj, dite_true, dite_false] at hij
      exact absurd hij (e7PositiveCoroot_ne_neg _ _)
    · simp only [hi, hj, dite_true, dite_false] at hij
      exact absurd hij.symm (e7PositiveCoroot_ne_neg _ _)
    · simp only [hi, hj, dite_false, neg_inj] at hij
      have h := congrArg Fin.val (e7PositiveCoroot_injective hij)
      apply Fin.ext
      simp only at h ⊢
      omega

/-- The 126 `E7` roots in the fundamental-weight basis. It is `@[expose]`d so that its defining
equation `e7Root_apply` holds by `rfl`. -/
@[expose] def e7Root : Fin 126 ↪ (Fin 7 → ℤ) where
  toFun i := e7Coroot i ᵥ* CartanMatrix.E₇
  inj' := by
    intro i j hij
    apply e7Coroot.injective
    apply sub_eq_zero.mp
    apply Matrix.eq_zero_of_vecMul_eq_zero (by rw [CartanMatrix.E₇_det]; norm_num)
    rw [sub_vecMul]
    exact sub_eq_zero.mpr hij

/-- Each `E7` root is the `E7` Cartan matrix applied to the corresponding coroot. This is the
defining equation of `e7Root`; it is deliberately not `@[simp]`, since it would rewrite the
left-hand sides of the root-table lemmas below. -/
theorem e7Root_apply (i : Fin 126) : e7Root i = e7Coroot i ᵥ* CartanMatrix.E₇ := rfl

/-- The negative half of the coroot table is the negation of the positive half. -/
@[simp] theorem e7Coroot_natAdd (i : Fin 63) :
    e7Coroot (Fin.addNat i 63) = -e7Coroot (Fin.castAdd 63 i) := by
  fin_cases i <;> decide

/-- The negative half of the root table is the negation of the positive half. -/
@[simp] theorem e7Root_natAdd (i : Fin 63) :
    e7Root (Fin.addNat i 63) = -e7Root (Fin.castAdd 63 i) := by
  rw [e7Root_apply, e7Root_apply, e7Coroot_natAdd, Matrix.neg_vecMul]

/-- Every listed `E7` root pairs to two with its corresponding coroot. -/
@[simp] theorem e7Root_dotProduct_coroot (i : Fin 126) : e7Root i ⬝ᵥ e7Coroot i = 2 := by
  fin_cases i <;> decide

/-- The first seven coroots are the standard basis of the simple-coroot lattice. -/
@[simp] theorem e7Coroot_simple (i : Fin 7) :
    e7Coroot (Fin.castAdd 119 i) = Pi.single i 1 := by
  fin_cases i <;> decide

/-- The first seven roots are the rows of the Bourbaki `E7` Cartan matrix. -/
@[simp] theorem e7Root_simple (i : Fin 7) :
    e7Root (Fin.castAdd 119 i) = CartanMatrix.E₇.row i := by
  rw [e7Root_apply, e7Coroot_simple, Matrix.single_one_vecMul]

/-- Every positive `E7` coroot has nonnegative simple-coroot coordinates. -/
theorem e7Coroot_nonneg (i : Fin 63) (j : Fin 7) : 0 ≤ e7Coroot (Fin.castAdd 63 i) j := by
  fin_cases i <;> fin_cases j <;> decide

/-- The last positive entry of the coroot table has the Bourbaki marks `(2, 2, 3, 4, 3, 2, 1)`. -/
theorem e7Coroot_apply_62 : e7Coroot 62 = ![2, 2, 3, 4, 3, 2, 1] := by decide

/-- The last positive entry is the highest `E7` coroot: it dominates every entry of the table
in each simple-coroot coordinate. -/
theorem e7Coroot_le_apply_62 (i : Fin 126) (j : Fin 7) : e7Coroot i j ≤ e7Coroot 62 j := by
  revert i j
  decide

end DynkinType
end TauCeti

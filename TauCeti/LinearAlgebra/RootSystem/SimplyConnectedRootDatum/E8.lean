/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.RootSystem.DynkinType
public import Mathlib.LinearAlgebra.Matrix.Dual

public section

/-!
# The integral roots of type E8

This file enumerates the 240 roots of type `E8` in the lattices used by the future pinned simply
connected root datum. Coroots are expressed in the simple-coroot basis and roots in the
fundamental-weight basis. The first eight entries are the Bourbaki simple roots; the remaining
positive roots are ordered by height, followed by their negatives.

The enumeration is the root-data input for Layer 6 of the root-systems roadmap. It follows
Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VII.
-/

namespace TauCeti

open _root_.Matrix

namespace DynkinType

private def e8PositiveCorootChunk0 : Fin 10 → (Fin 8 → ℤ) := ![
  ![1, 0, 0, 0, 0, 0, 0, 0],
  ![0, 1, 0, 0, 0, 0, 0, 0],
  ![0, 0, 1, 0, 0, 0, 0, 0],
  ![0, 0, 0, 1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 1, 0, 0, 0],
  ![0, 0, 0, 0, 0, 1, 0, 0],
  ![0, 0, 0, 0, 0, 0, 1, 0],
  ![0, 0, 0, 0, 0, 0, 0, 1],
  ![0, 0, 0, 0, 0, 0, 1, 1],
  ![0, 0, 0, 0, 0, 1, 1, 0]
]

private def e8PositiveCorootChunk1 : Fin 10 → (Fin 8 → ℤ) := ![
  ![0, 0, 0, 0, 1, 1, 0, 0],
  ![0, 0, 0, 1, 1, 0, 0, 0],
  ![0, 0, 1, 1, 0, 0, 0, 0],
  ![0, 1, 0, 1, 0, 0, 0, 0],
  ![1, 0, 1, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 1, 1, 1],
  ![0, 0, 0, 0, 1, 1, 1, 0],
  ![0, 0, 0, 1, 1, 1, 0, 0],
  ![0, 0, 1, 1, 1, 0, 0, 0],
  ![0, 1, 0, 1, 1, 0, 0, 0]
]

private def e8PositiveCorootChunk2 : Fin 10 → (Fin 8 → ℤ) := ![
  ![0, 1, 1, 1, 0, 0, 0, 0],
  ![1, 0, 1, 1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 1, 1, 1, 1],
  ![0, 0, 0, 1, 1, 1, 1, 0],
  ![0, 0, 1, 1, 1, 1, 0, 0],
  ![0, 1, 0, 1, 1, 1, 0, 0],
  ![0, 1, 1, 1, 1, 0, 0, 0],
  ![1, 0, 1, 1, 1, 0, 0, 0],
  ![1, 1, 1, 1, 0, 0, 0, 0],
  ![0, 0, 0, 1, 1, 1, 1, 1]
]

private def e8PositiveCorootChunk3 : Fin 10 → (Fin 8 → ℤ) := ![
  ![0, 0, 1, 1, 1, 1, 1, 0],
  ![0, 1, 0, 1, 1, 1, 1, 0],
  ![0, 1, 1, 1, 1, 1, 0, 0],
  ![0, 1, 1, 2, 1, 0, 0, 0],
  ![1, 0, 1, 1, 1, 1, 0, 0],
  ![1, 1, 1, 1, 1, 0, 0, 0],
  ![0, 0, 1, 1, 1, 1, 1, 1],
  ![0, 1, 0, 1, 1, 1, 1, 1],
  ![0, 1, 1, 1, 1, 1, 1, 0],
  ![0, 1, 1, 2, 1, 1, 0, 0]
]

private def e8PositiveCorootChunk4 : Fin 10 → (Fin 8 → ℤ) := ![
  ![1, 0, 1, 1, 1, 1, 1, 0],
  ![1, 1, 1, 1, 1, 1, 0, 0],
  ![1, 1, 1, 2, 1, 0, 0, 0],
  ![0, 1, 1, 1, 1, 1, 1, 1],
  ![0, 1, 1, 2, 1, 1, 1, 0],
  ![0, 1, 1, 2, 2, 1, 0, 0],
  ![1, 0, 1, 1, 1, 1, 1, 1],
  ![1, 1, 1, 1, 1, 1, 1, 0],
  ![1, 1, 1, 2, 1, 1, 0, 0],
  ![1, 1, 2, 2, 1, 0, 0, 0]
]

private def e8PositiveCorootChunk5 : Fin 10 → (Fin 8 → ℤ) := ![
  ![0, 1, 1, 2, 1, 1, 1, 1],
  ![0, 1, 1, 2, 2, 1, 1, 0],
  ![1, 1, 1, 1, 1, 1, 1, 1],
  ![1, 1, 1, 2, 1, 1, 1, 0],
  ![1, 1, 1, 2, 2, 1, 0, 0],
  ![1, 1, 2, 2, 1, 1, 0, 0],
  ![0, 1, 1, 2, 2, 1, 1, 1],
  ![0, 1, 1, 2, 2, 2, 1, 0],
  ![1, 1, 1, 2, 1, 1, 1, 1],
  ![1, 1, 1, 2, 2, 1, 1, 0]
]

private def e8PositiveCorootChunk6 : Fin 10 → (Fin 8 → ℤ) := ![
  ![1, 1, 2, 2, 1, 1, 1, 0],
  ![1, 1, 2, 2, 2, 1, 0, 0],
  ![0, 1, 1, 2, 2, 2, 1, 1],
  ![1, 1, 1, 2, 2, 1, 1, 1],
  ![1, 1, 1, 2, 2, 2, 1, 0],
  ![1, 1, 2, 2, 1, 1, 1, 1],
  ![1, 1, 2, 2, 2, 1, 1, 0],
  ![1, 1, 2, 3, 2, 1, 0, 0],
  ![0, 1, 1, 2, 2, 2, 2, 1],
  ![1, 1, 1, 2, 2, 2, 1, 1]
]

private def e8PositiveCorootChunk7 : Fin 10 → (Fin 8 → ℤ) := ![
  ![1, 1, 2, 2, 2, 1, 1, 1],
  ![1, 1, 2, 2, 2, 2, 1, 0],
  ![1, 1, 2, 3, 2, 1, 1, 0],
  ![1, 2, 2, 3, 2, 1, 0, 0],
  ![1, 1, 1, 2, 2, 2, 2, 1],
  ![1, 1, 2, 2, 2, 2, 1, 1],
  ![1, 1, 2, 3, 2, 1, 1, 1],
  ![1, 1, 2, 3, 2, 2, 1, 0],
  ![1, 2, 2, 3, 2, 1, 1, 0],
  ![1, 1, 2, 2, 2, 2, 2, 1]
]

private def e8PositiveCorootChunk8 : Fin 10 → (Fin 8 → ℤ) := ![
  ![1, 1, 2, 3, 2, 2, 1, 1],
  ![1, 1, 2, 3, 3, 2, 1, 0],
  ![1, 2, 2, 3, 2, 1, 1, 1],
  ![1, 2, 2, 3, 2, 2, 1, 0],
  ![1, 1, 2, 3, 2, 2, 2, 1],
  ![1, 1, 2, 3, 3, 2, 1, 1],
  ![1, 2, 2, 3, 2, 2, 1, 1],
  ![1, 2, 2, 3, 3, 2, 1, 0],
  ![1, 1, 2, 3, 3, 2, 2, 1],
  ![1, 2, 2, 3, 2, 2, 2, 1]
]

private def e8PositiveCorootChunk9 : Fin 10 → (Fin 8 → ℤ) := ![
  ![1, 2, 2, 3, 3, 2, 1, 1],
  ![1, 2, 2, 4, 3, 2, 1, 0],
  ![1, 1, 2, 3, 3, 3, 2, 1],
  ![1, 2, 2, 3, 3, 2, 2, 1],
  ![1, 2, 2, 4, 3, 2, 1, 1],
  ![1, 2, 3, 4, 3, 2, 1, 0],
  ![1, 2, 2, 3, 3, 3, 2, 1],
  ![1, 2, 2, 4, 3, 2, 2, 1],
  ![1, 2, 3, 4, 3, 2, 1, 1],
  ![2, 2, 3, 4, 3, 2, 1, 0]
]

private def e8PositiveCorootChunk10 : Fin 10 → (Fin 8 → ℤ) := ![
  ![1, 2, 2, 4, 3, 3, 2, 1],
  ![1, 2, 3, 4, 3, 2, 2, 1],
  ![2, 2, 3, 4, 3, 2, 1, 1],
  ![1, 2, 2, 4, 4, 3, 2, 1],
  ![1, 2, 3, 4, 3, 3, 2, 1],
  ![2, 2, 3, 4, 3, 2, 2, 1],
  ![1, 2, 3, 4, 4, 3, 2, 1],
  ![2, 2, 3, 4, 3, 3, 2, 1],
  ![1, 2, 3, 5, 4, 3, 2, 1],
  ![2, 2, 3, 4, 4, 3, 2, 1]
]

private def e8PositiveCorootChunk11 : Fin 10 → (Fin 8 → ℤ) := ![
  ![1, 3, 3, 5, 4, 3, 2, 1],
  ![2, 2, 3, 5, 4, 3, 2, 1],
  ![2, 2, 4, 5, 4, 3, 2, 1],
  ![2, 3, 3, 5, 4, 3, 2, 1],
  ![2, 3, 4, 5, 4, 3, 2, 1],
  ![2, 3, 4, 6, 4, 3, 2, 1],
  ![2, 3, 4, 6, 5, 3, 2, 1],
  ![2, 3, 4, 6, 5, 4, 2, 1],
  ![2, 3, 4, 6, 5, 4, 3, 1],
  ![2, 3, 4, 6, 5, 4, 3, 2]
]

private def e8PositiveCoroot (i : Fin 120) : Fin 8 → ℤ :=
  if h : (i : ℕ) < 10 then e8PositiveCorootChunk0 ⟨i, h⟩
  else if h : (i : ℕ) < 20 then e8PositiveCorootChunk1 ⟨(i : ℕ) - 10, by omega⟩
  else if h : (i : ℕ) < 30 then e8PositiveCorootChunk2 ⟨(i : ℕ) - 20, by omega⟩
  else if h : (i : ℕ) < 40 then e8PositiveCorootChunk3 ⟨(i : ℕ) - 30, by omega⟩
  else if h : (i : ℕ) < 50 then e8PositiveCorootChunk4 ⟨(i : ℕ) - 40, by omega⟩
  else if h : (i : ℕ) < 60 then e8PositiveCorootChunk5 ⟨(i : ℕ) - 50, by omega⟩
  else if h : (i : ℕ) < 70 then e8PositiveCorootChunk6 ⟨(i : ℕ) - 60, by omega⟩
  else if h : (i : ℕ) < 80 then e8PositiveCorootChunk7 ⟨(i : ℕ) - 70, by omega⟩
  else if h : (i : ℕ) < 90 then e8PositiveCorootChunk8 ⟨(i : ℕ) - 80, by omega⟩
  else if h : (i : ℕ) < 100 then e8PositiveCorootChunk9 ⟨(i : ℕ) - 90, by omega⟩
  else if h : (i : ℕ) < 110 then e8PositiveCorootChunk10 ⟨(i : ℕ) - 100, by omega⟩
  else e8PositiveCorootChunk11 ⟨(i : ℕ) - 110, by omega⟩

private def e8CorootCode (x : Fin 8 → ℤ) : ℤ :=
  x 0 + 7 * x 1 + 49 * x 2 + 343 * x 3 + 2401 * x 4 + 16807 * x 5 +
    117649 * x 6 + 823543 * x 7

private lemma e8PositiveCoroot_injective : Function.Injective e8PositiveCoroot := by
  apply Function.Injective.of_comp (f := e8CorootCode)
  decide

private lemma e8PositiveCoroot_nonneg (i : Fin 120) (j : Fin 8) :
    0 ≤ e8PositiveCoroot i j := by
  fin_cases i <;> fin_cases j <;> decide

private lemma e8PositiveCoroot_sum_pos (i : Fin 120) :
    0 < ∑ j, e8PositiveCoroot i j := by
  fin_cases i <;> decide

private lemma e8PositiveCoroot_ne_neg (i j : Fin 120) :
    e8PositiveCoroot i ≠ -e8PositiveCoroot j := by
  intro h
  have hsum := congrArg (fun x : Fin 8 → ℤ ↦ ∑ k, x k) h
  have hj : 0 < ∑ k, e8PositiveCoroot j k := e8PositiveCoroot_sum_pos j
  simp only [Pi.neg_apply, Finset.sum_neg_distrib] at hsum
  have hi : 0 < ∑ k, e8PositiveCoroot i k := e8PositiveCoroot_sum_pos i
  omega

/-- The 240 `E8` coroots in the simple-coroot basis, with positive roots followed by negatives. -/
def e8Coroot : Fin 240 ↪ (Fin 8 → ℤ) where
  toFun i := if hi : (i : ℕ) < 120 then e8PositiveCoroot ⟨i, hi⟩ else
    -e8PositiveCoroot ⟨(i : ℕ) - 120, by omega⟩
  inj' := by
    intro i j hij
    by_cases hi : (i : ℕ) < 120 <;> by_cases hj : (j : ℕ) < 120
    · simp only [hi, hj, dite_true] at hij
      apply Fin.ext
      simpa using congrArg Fin.val (e8PositiveCoroot_injective hij)
    · simp only [hi, hj, dite_true, dite_false] at hij
      exact absurd hij (e8PositiveCoroot_ne_neg _ _)
    · simp only [hi, hj, dite_true, dite_false] at hij
      exact absurd hij.symm (e8PositiveCoroot_ne_neg _ _)
    · simp only [hi, hj, dite_false, neg_inj] at hij
      have h := congrArg Fin.val (e8PositiveCoroot_injective hij)
      apply Fin.ext
      simp only at h ⊢
      omega

/-- The 240 `E8` roots in the fundamental-weight basis. -/
def e8Root : Fin 240 ↪ (Fin 8 → ℤ) where
  toFun i := e8Coroot i ᵥ* CartanMatrix.E₈
  inj' := by
    intro i j hij
    apply e8Coroot.injective
    apply sub_eq_zero.mp
    apply Matrix.eq_zero_of_vecMul_eq_zero (by rw [CartanMatrix.E₈_det]; norm_num)
    rw [sub_vecMul]
    exact sub_eq_zero.mpr hij

/-- The `E8` roots are obtained from the coroot coordinates using the Cartan matrix. -/
theorem e8Root_apply (i : Fin 240) :
    e8Root i = e8Coroot i ᵥ* CartanMatrix.E₈ := (rfl)

private lemma e8Coroot_castAdd (i : Fin 120) :
    e8Coroot (Fin.castAdd 120 i) = e8PositiveCoroot i := by
  -- Expose the dependent `if` in the embedding's coercion so that its positive branch reduces.
  change (if h : (i : ℕ) < 120 then e8PositiveCoroot ⟨i, h⟩ else
    -e8PositiveCoroot ⟨(i : ℕ) - 120, by omega⟩) = e8PositiveCoroot i
  rw [dif_pos i.isLt]

/-- The negative half of the coroot table is the negation of the positive half. -/
@[simp] theorem e8Coroot_addNat (i : Fin 120) :
    e8Coroot (Fin.addNat i 120) = -e8Coroot (Fin.castAdd 120 i) := by
  rw [e8Coroot_castAdd]
  change (if h : (i : ℕ) + 120 < 120 then e8PositiveCoroot ⟨(i : ℕ) + 120, h⟩ else
    -e8PositiveCoroot ⟨(i : ℕ) + 120 - 120, by omega⟩) = -e8PositiveCoroot i
  rw [dif_neg (by omega)]
  congr

/-- The negative half of the root table is the negation of the positive half. -/
@[simp] theorem e8Root_addNat (i : Fin 120) :
    e8Root (Fin.addNat i 120) = -e8Root (Fin.castAdd 120 i) := by
  rw [e8Root_apply, e8Coroot_addNat, Matrix.neg_vecMul, e8Root_apply]

/-- Every listed `E8` root pairs to two with its corresponding coroot. -/
@[simp] theorem e8Root_dotProduct_coroot (i : Fin 240) : e8Root i ⬝ᵥ e8Coroot i = 2 := by
  fin_cases i <;> decide

/-- The first eight roots are the rows of the Bourbaki `E8` Cartan matrix. -/
@[simp] theorem e8Root_simple (i : Fin 8) :
    e8Root (Fin.castAdd 232 i) = CartanMatrix.E₈.row i := by
  fin_cases i <;> decide

/-- The first eight coroots are the standard basis of the simple-coroot lattice. -/
@[simp] theorem e8Coroot_simple (i : Fin 8) :
    e8Coroot (Fin.castAdd 232 i) = Pi.single i 1 := by
  fin_cases i <;> decide

/-- Every positive `E8` coroot has nonnegative simple-coroot coordinates. -/
theorem e8Coroot_nonneg (i : Fin 120) (j : Fin 8) :
    0 ≤ e8Coroot (Fin.castAdd 120 i) j := by
  rw [e8Coroot_castAdd]
  exact e8PositiveCoroot_nonneg i j

/-- The last positive `E8` coroot has Bourbaki marks `(2, 3, 4, 6, 5, 4, 3, 2)`. -/
theorem e8Coroot_apply_last_positive :
    e8Coroot 119 = ![2, 3, 4, 6, 5, 4, 3, 2] := by decide

end DynkinType

end TauCeti

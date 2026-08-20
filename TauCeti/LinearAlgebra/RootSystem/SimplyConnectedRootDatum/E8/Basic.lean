/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.DynkinType
public import Mathlib.Data.Fin.Tuple.Embedding
public import Mathlib.LinearAlgebra.Matrix.Dual

public section

/-!
# The integral roots of type E8

This file enumerates the 240 roots of type `E8` in the lattices used by the pinned simply connected
root datum, which is built from these tables in
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E8.Datum`; that the enumeration below
misses no root is proved in `TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E8.Lattice`.
Coroots are expressed in the simple-coroot basis and roots in the
fundamental-weight basis. Both tables are indexed by the same `Fin 240`: the first eight entries
of the root table are the Bourbaki simple roots and the first eight entries of the coroot table
are the corresponding simple coroots. The remaining positive entries are ordered by height, and
the last 120 entries are the negatives of the first 120.

The enumeration is the root-data input for Layer 6 of the root-systems roadmap. It follows
Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VII.
-/

namespace TauCeti

open _root_.Matrix

namespace DynkinType

/-- The 120 positive `E8` coroots in the simple-coroot basis. The first eight entries are the
Bourbaki simple coroots and the rest are ordered by height. -/
def e8PositiveCoroot : Fin 120 ↪ (Fin 8 → ℤ) :=
  let e8PositiveCorootTable : Fin 12 → Fin 10 → (Fin 8 → ℤ) := ![
  ![
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
  ],
  ![
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
  ],
  ![
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
  ],
  ![
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
  ],
  ![
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
  ],
  ![
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
  ],
  ![
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
  ],
  ![
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
  ],
  ![
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
  ],
  ![
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
  ],
  ![
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
  ],
  ![
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
  ]
  let e8CorootCode (x : Fin 8 → ℤ) : ℤ :=
    x 0 + 7 * x 1 + 49 * x 2 + 343 * x 3 + 2401 * x 4 + 16807 * x 5 +
      117649 * x 6 + 823543 * x 7
  {
    toFun i := e8PositiveCorootTable ⟨(i : ℕ) / 10, by omega⟩ ⟨(i : ℕ) % 10, by omega⟩
    inj' := by
      apply Function.Injective.of_comp (f := e8CorootCode)
      -- The 120 × 120 case check runs in the kernel, whose evaluation has no recursion limit.
      decide +kernel
  }

/-- There are 63 positive `E₈` coroots in the principal `E₇` subsystem, characterized by
having zero final simple-coroot coordinate. -/
theorem card_filter_e8PositiveCoroot_last_eq_zero :
    (Finset.univ.filter fun i => e8PositiveCoroot i 7 = 0).card = 63 := by
  decide +kernel

/-- Every positive `E8` coroot has nonnegative simple-coroot coordinates. -/
theorem e8PositiveCoroot_nonneg (i : Fin 120) (j : Fin 8) :
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

/-- The negatives of the 120 positive `E8` coroots. -/
private def e8NegativeCoroot : Fin 120 ↪ (Fin 8 → ℤ) :=
  e8PositiveCoroot.trans (Equiv.neg (Fin 8 → ℤ)).toEmbedding

private lemma e8PositiveCoroot_range_disjoint :
    Disjoint (Set.range e8PositiveCoroot) (Set.range e8NegativeCoroot) := by
  rw [Set.disjoint_left]
  rintro _ ⟨i, rfl⟩ ⟨j, hj⟩
  exact e8PositiveCoroot_ne_neg i j hj.symm

/-- The 240 `E8` coroots in the simple-coroot basis, with the positive coroots followed by their
negatives. -/
def e8Coroot : Fin 240 ↪ (Fin 8 → ℤ) :=
  Fin.Embedding.append e8PositiveCoroot_range_disjoint

/-- The 240 `E8` roots in the fundamental-weight basis. -/
def e8Root : Fin 240 ↪ (Fin 8 → ℤ) where
  toFun i := e8Coroot i ᵥ* CartanMatrix.E 8
  inj' := by
    intro i j hij
    apply e8Coroot.injective
    apply sub_eq_zero.mp
    apply Matrix.eq_zero_of_vecMul_eq_zero (by rw [CartanMatrix.E₈_det]; norm_num)
    rw [sub_vecMul]
    exact sub_eq_zero.mpr hij

/-- The `E8` roots are obtained from the coroot coordinates using the Cartan matrix. -/
theorem e8Root_apply (i : Fin 240) :
    e8Root i = e8Coroot i ᵥ* CartanMatrix.E 8 := (rfl)

/-- The `E8` roots are the images of the coroots under the Cartan matrix, read on the left or,
equivalently, on the right, the matrix being symmetric. -/
theorem e8Root_eq_mulVec (i : Fin 240) : e8Root i = CartanMatrix.E 8 *ᵥ e8Coroot i := by
  rw [e8Root_apply, ← mulVec_transpose, (CartanMatrix.E_isSymm 8)]

/-- The coroot table is the concatenation of the positive coroots with their negatives. -/
private theorem e8Coroot_coe :
    ⇑e8Coroot = Fin.append (⇑e8PositiveCoroot) fun i ↦ -e8PositiveCoroot i :=
  Fin.Embedding.coe_append _

/-- The first half of the coroot table is the positive coroot enumeration. -/
@[simp] theorem e8Coroot_castAdd (i : Fin 120) :
    e8Coroot (Fin.castAdd 120 i) = e8PositiveCoroot i := by
  rw [e8Coroot_coe, Fin.append_left]

/-- The negative half of the coroot table is the negation of the positive half. -/
@[simp] theorem e8Coroot_addNat (i : Fin 120) :
    e8Coroot (Fin.addNat i 120) = -e8PositiveCoroot i := by
  rw [← Fin.natAdd_eq_addNat, e8Coroot_coe, Fin.append_right]

/-- The negative half of the root table is the negation of the positive half. -/
@[simp] theorem e8Root_addNat (i : Fin 120) :
    e8Root (Fin.addNat i 120) = -e8Root (Fin.castAdd 120 i) := by
  rw [e8Root_apply, e8Root_apply, e8Coroot_addNat, e8Coroot_castAdd, Matrix.neg_vecMul]

private theorem e8PositiveCoroot_norm_chunk (c : Fin 12) (i : Fin 10) :
    (e8PositiveCoroot ⟨10 * c + i, by omega⟩ ᵥ* CartanMatrix.E 8) ⬝ᵥ
      e8PositiveCoroot ⟨10 * c + i, by omega⟩ = 2 := by
  fin_cases c <;> decide +kernel +revert

private theorem e8PositiveCoroot_norm (i : Fin 120) :
    (e8PositiveCoroot i ᵥ* CartanMatrix.E 8) ⬝ᵥ e8PositiveCoroot i = 2 := by
  let c : Fin 12 := ⟨(i : ℕ) / 10, by omega⟩
  let r : Fin 10 := ⟨(i : ℕ) % 10, by omega⟩
  have hi : i = ⟨10 * c + r, by omega⟩ := Fin.ext (by dsimp [c, r]; omega)
  rw [hi]
  exact e8PositiveCoroot_norm_chunk c r

/-- Every listed `E8` root pairs to two with its corresponding coroot. -/
@[simp] theorem e8Root_dotProduct_coroot (i : Fin 240) : e8Root i ⬝ᵥ e8Coroot i = 2 := by
  induction i using Fin.addCases (m := 120) (n := 120) with
  | left i =>
      rw [e8Root_apply, e8Coroot_castAdd]
      exact e8PositiveCoroot_norm i
  | right i =>
      rw [e8Root_apply, Fin.natAdd_eq_addNat, e8Coroot_addNat, neg_vecMul,
        neg_dotProduct_neg]
      exact e8PositiveCoroot_norm i

/-- The index of the `i`-th Bourbaki simple root in the pinned `E₈` enumeration. -/
def e8SimpleIndex (i : Fin 8) : Fin 240 := Fin.castAdd 232 i

@[simp] lemma e8SimpleIndex_val (i : Fin 8) : (e8SimpleIndex i : ℕ) = i := (rfl)

lemma e8SimpleIndex_injective : Function.Injective e8SimpleIndex :=
  Fin.castAdd_injective 8 232

/-- The simple roots of the pinned `E₈` datum are the rows of the Bourbaki Cartan matrix. -/
@[simp] theorem root_e8SimpleIndex (i : Fin 8) :
    e8Root (e8SimpleIndex i) = CartanMatrix.E 8 i := by
  fin_cases i <;> decide

/-- The simple coroots of the pinned `E₈` datum are the standard basis vectors. -/
@[simp] theorem coroot_e8SimpleIndex (i : Fin 8) :
    e8Coroot (e8SimpleIndex i) = Pi.single i 1 := by
  fin_cases i <;> decide

/-- The last positive `E8` coroot has Bourbaki marks `(2, 3, 4, 6, 5, 4, 3, 2)`. -/
theorem e8Coroot_apply_last_positive :
    e8Coroot 119 = ![2, 3, 4, 6, 5, 4, 3, 2] := by decide

end DynkinType

end TauCeti

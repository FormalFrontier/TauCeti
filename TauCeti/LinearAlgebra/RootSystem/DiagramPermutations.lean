/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Submatrix
public import TauCeti.LinearAlgebra.RootSystem.RootLength
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Numbered diagram permutations for the finite groups of Lie type

This file pins the permutations of Bourbaki-numbered simple roots used by the graph automorphisms
and exceptional isogenies in the construction of finite groups of Lie type.  Bourbaki node `i` is
represented by `Fin` index `i - 1`, as in `TauCeti.DynkinType.cartanMatrix`.

The ordinary graph automorphisms preserve the relevant Cartan matrix.  The Suzuki--Ree
permutations instead exchange long and short nodes; the corresponding special isogenies attach
different field exponents to the two root lengths.

The conventions follow Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, plates I--IX, and
the `CFSGStatement` roadmap's conventions for Steinberg endomorphisms.

## Main definitions

* `TauCeti.graphPermA`: reversal of the `Aₙ` chain.
* `TauCeti.graphPermD`: exchange of the final two indices, giving the fork symmetry of `Dₙ` for
  `4 ≤ n`.
* `TauCeti.graphPermE6`: the order-two symmetry of `E₆`.
* `TauCeti.trialityPermD4`: the order-three triality symmetry of `D₄`.
* `TauCeti.lengthPermRankTwo`: the length-exchanging permutation for `B₂` and `G₂`.
* `TauCeti.lengthPermF4`: the length-exchanging permutation for `F₄`.
* `TauCeti.DynkinType.diagramSymmetry`: the group of node permutations preserving the Cartan matrix
  of a Dynkin type, of which the graph permutations above are members.

## Main results

* `TauCeti.orderOf_graphPermA`, `TauCeti.orderOf_graphPermD`, `TauCeti.orderOf_graphPermE6` and
  `TauCeti.orderOf_trialityPermD4`: the graph permutations have order exactly two (for
  `graphPermA`, on at least two nodes), except for triality, which has order three.
* `TauCeti.cartanMatrix_A_graphPermA`, `TauCeti.cartanMatrix_D_graphPermD`,
  `TauCeti.cartanMatrix_E6_graphPermE6` and `TauCeti.cartanMatrix_D4_trialityPermD4`: each graph
  permutation is an automorphism of the corresponding Cartan matrix.
* `TauCeti.cartanMatrix_B2_lengthPermRankTwo`, `TauCeti.cartanMatrix_G2_lengthPermRankTwo` and
  `TauCeti.cartanMatrix_F4_lengthPermF4`: each length permutation instead carries its Cartan matrix
  to the transposed matrix, and `TauCeti.cartanMatrix_B2_submatrix_lengthPermRankTwo_ne` and its
  two counterparts record that this is a different matrix, so a length permutation is not a
  diagram symmetry.
* `TauCeti.lengthPermRankTwo_lengthPermRankTwo` and `TauCeti.lengthPermF4_lengthPermF4`: the length
  permutations are involutions.
-/

public section

namespace TauCeti

/-- The `Aₙ` diagram automorphism, reversing its chain of Bourbaki-numbered nodes. -/
def graphPermA (n : ℕ) : Equiv.Perm (Fin n) :=
  Fin.revPerm

/-- The permutation exchanging the final two indices of `Fin n`. For `4 ≤ n`, this is the `Dₙ`
diagram automorphism exchanging its two fork nodes and fixing the chain. -/
def graphPermD (n : ℕ) (hn : 2 ≤ n) : Equiv.Perm (Fin n) :=
  Equiv.swap ⟨n - 2, by omega⟩ ⟨n - 1, by omega⟩

/-- The `E₆` diagram automorphism, exchanging Bourbaki nodes `1 ↔ 6` and `3 ↔ 5`. -/
def graphPermE6 : Equiv.Perm (Fin 6) :=
  Equiv.swap 0 5 * Equiv.swap 2 4

/-- Triality of `D₄`, cycling its three outer nodes `(0 2 3)` and fixing the central node `1`. -/
def trialityPermD4 : Equiv.Perm (Fin 4) :=
  Equiv.swap 0 3 * Equiv.swap 0 2

/-- The length-exchanging permutation of the two nodes of `B₂` and `G₂`. -/
def lengthPermRankTwo : Equiv.Perm (Fin 2) :=
  Equiv.swap 0 1

/-- The length-exchanging permutation of `F₄`, reversing its four-node diagram. -/
def lengthPermF4 : Equiv.Perm (Fin 4) :=
  graphPermA 4

/-- Reversal of a chain of at least two nodes moves the first node, so it is not the identity.
The bound is necessary: `graphPermA 0` and `graphPermA 1` are the identity. -/
theorem graphPermA_ne_one {n : ℕ} (hn : 2 ≤ n) : graphPermA n ≠ 1 := by
  intro h
  have h0 : n - (0 + 1) = 0 := by
    have h1 : graphPermA n ⟨0, by omega⟩ = ⟨0, by omega⟩ := by rw [h]; rfl
    rw [graphPermA, Fin.revPerm_apply] at h1
    exact congrArg Fin.val h1
  omega

/-- Reversing the `Aₙ` chain twice is the identity. -/
@[simp] theorem graphPermA_sq (n : ℕ) : graphPermA n ^ 2 = 1 := by
  ext i
  simp [graphPermA, pow_two, Equiv.Perm.mul_apply]

/-- Reversal of a chain of at least two nodes has order exactly two. -/
@[simp] theorem orderOf_graphPermA {n : ℕ} (hn : 2 ≤ n) : orderOf (graphPermA n) = 2 :=
  orderOf_eq_prime (graphPermA_sq n) (graphPermA_ne_one hn)

/-- The final-index swap sends index `n - 2` to index `n - 1`; for `4 ≤ n`, these are the two
`Dₙ` fork nodes. -/
@[simp] lemma graphPermD_apply_left (n : ℕ) (hn : 2 ≤ n) :
    graphPermD n hn ⟨n - 2, by omega⟩ = ⟨n - 1, by omega⟩ := by
  simp [graphPermD]

/-- The final-index swap sends index `n - 1` to index `n - 2`; for `4 ≤ n`, these are the two
`Dₙ` fork nodes. -/
@[simp] lemma graphPermD_apply_right (n : ℕ) (hn : 2 ≤ n) :
    graphPermD n hn ⟨n - 1, by omega⟩ = ⟨n - 2, by omega⟩ := by
  simp [graphPermD]

/-- The final-index swap fixes every index except `n - 2` and `n - 1`; for `4 ≤ n`, these are the
two `Dₙ` fork nodes. -/
@[simp] lemma graphPermD_apply_of_ne_of_ne (n : ℕ) (hn : 2 ≤ n) (i : Fin n)
    (hi : (i : ℕ) ≠ n - 2) (hi' : (i : ℕ) ≠ n - 1) : graphPermD n hn i = i := by
  apply Equiv.swap_apply_of_ne_of_ne <;> simpa [Fin.ext_iff]

/-- The final-index swap is its own inverse. -/
@[simp] lemma graphPermD_symm (n : ℕ) (hn : 2 ≤ n) :
    (graphPermD n hn).symm = graphPermD n hn := by
  simp [graphPermD]

/-- Swapping the final two indices twice is the identity. -/
@[simp] theorem graphPermD_sq (n : ℕ) (hn : 2 ≤ n) : graphPermD n hn ^ 2 = 1 := by
  simp [graphPermD, pow_two]

/-- The two swapped indices are distinct, so the swap is not the identity. -/
theorem graphPermD_ne_one (n : ℕ) (hn : 2 ≤ n) : graphPermD n hn ≠ 1 := by
  rw [graphPermD, ne_eq, Equiv.swap_eq_one_iff]
  intro h
  have : n - 2 = n - 1 := congrArg Fin.val h
  omega

/-- Exchanging the final two indices has order exactly two. -/
@[simp] theorem orderOf_graphPermD (n : ℕ) (hn : 2 ≤ n) : orderOf (graphPermD n hn) = 2 :=
  orderOf_eq_prime (graphPermD_sq n hn) (graphPermD_ne_one n hn)

/-- The `E₆` graph permutation sends node `0` to node `5`. -/
@[simp] lemma graphPermE6_apply_zero : graphPermE6 0 = 5 := by decide
/-- The `E₆` graph permutation fixes node `1`. -/
@[simp] lemma graphPermE6_apply_one : graphPermE6 1 = 1 := by decide
/-- The `E₆` graph permutation sends node `2` to node `4`. -/
@[simp] lemma graphPermE6_apply_two : graphPermE6 2 = 4 := by decide
/-- The `E₆` graph permutation fixes node `3`. -/
@[simp] lemma graphPermE6_apply_three : graphPermE6 3 = 3 := by decide
/-- The `E₆` graph permutation sends node `4` to node `2`. -/
@[simp] lemma graphPermE6_apply_four : graphPermE6 4 = 2 := by decide
/-- The `E₆` graph permutation sends node `5` to node `0`. -/
@[simp] lemma graphPermE6_apply_five : graphPermE6 5 = 0 := by decide

/-- Applying the `E₆` graph permutation twice is the identity. -/
@[simp] theorem graphPermE6_sq : graphPermE6 ^ 2 = 1 := by decide

/-- The `E₆` graph permutation has order exactly two. -/
@[simp] theorem orderOf_graphPermE6 : orderOf graphPermE6 = 2 :=
  orderOf_eq_prime graphPermE6_sq (by decide)

/-- Triality sends outer node `0` to outer node `2`. -/
@[simp] lemma trialityPermD4_apply_zero : trialityPermD4 0 = 2 := by decide
/-- Triality fixes the central node `1`. -/
@[simp] lemma trialityPermD4_apply_one : trialityPermD4 1 = 1 := by decide
/-- Triality sends outer node `2` to outer node `3`. -/
@[simp] lemma trialityPermD4_apply_two : trialityPermD4 2 = 3 := by decide
/-- Triality sends outer node `3` to outer node `0`. -/
@[simp] lemma trialityPermD4_apply_three : trialityPermD4 3 = 0 := by decide

/-- Applying triality three times is the identity. -/
@[simp] theorem trialityPermD4_pow_three : trialityPermD4 ^ 3 = 1 := by decide

/-- Triality has order exactly three. -/
@[simp] theorem orderOf_trialityPermD4 : orderOf trialityPermD4 = 3 :=
  orderOf_eq_prime trialityPermD4_pow_three (by decide)

/-- The rank-two length permutation sends node `0` to node `1`. -/
@[simp] lemma lengthPermRankTwo_apply_zero : lengthPermRankTwo 0 = 1 := by decide
/-- The rank-two length permutation sends node `1` to node `0`. -/
@[simp] lemma lengthPermRankTwo_apply_one : lengthPermRankTwo 1 = 0 := by decide

/-- Exchanging the two rank-two nodes twice is the identity. -/
@[simp] theorem lengthPermRankTwo_sq : lengthPermRankTwo ^ 2 = 1 := by decide

/-- Exchanging the two rank-two nodes is an involution. -/
@[simp] theorem lengthPermRankTwo_lengthPermRankTwo (i : Fin 2) :
    lengthPermRankTwo (lengthPermRankTwo i) = i :=
  Equiv.swap_apply_self 0 1 i

/-- The two rank-two nodes are distinct, so exchanging them is not the identity. -/
theorem lengthPermRankTwo_ne_one : lengthPermRankTwo ≠ 1 := by decide

/-- Exchanging the two rank-two nodes has order exactly two. -/
@[simp] theorem orderOf_lengthPermRankTwo : orderOf lengthPermRankTwo = 2 :=
  orderOf_eq_prime lengthPermRankTwo_sq lengthPermRankTwo_ne_one

/-- Reversal of the `F₄` diagram sends node `i` to the node at the mirrored index. -/
lemma lengthPermF4_apply (i : Fin 4) : lengthPermF4 i = i.rev := by
  simp only [lengthPermF4, graphPermA, Fin.revPerm_apply]

/-- Reversal of a chain is an involution. -/
@[simp] theorem graphPermA_graphPermA (n : ℕ) (i : Fin n) : graphPermA n (graphPermA n i) = i := by
  simp only [graphPermA, Fin.revPerm_apply, Fin.rev_rev]

/-- Reversing the `F₄` diagram is an involution. -/
@[simp] theorem lengthPermF4_lengthPermF4 (i : Fin 4) : lengthPermF4 (lengthPermF4 i) = i :=
  graphPermA_graphPermA 4 i

/-- Reversal is an automorphism of the type-`A` Cartan matrix. -/
@[simp] theorem cartanMatrix_A_graphPermA (n : ℕ) (i j : Fin n) :
    (DynkinType.A n).cartanMatrix (graphPermA n i) (graphPermA n j) =
      (DynkinType.A n).cartanMatrix i j := by
  simp only [DynkinType.cartanMatrix_A, CartanMatrix.A, Matrix.of_apply, graphPermA,
    Fin.revPerm_apply, Fin.ext_iff, Fin.val_rev]
  split_ifs <;> omega

-- Every defining condition of `CartanMatrix.D n` is invariant under exchanging the two fork
-- indices, hence so is the whole `if`-chain; `key` records that exchange on index values.
private lemma cartanMatrix_D_swap_fork (n : ℕ) (hn : 4 ≤ n) (a b : Fin n) (ha : (a : ℕ) = n - 2)
    (hb : (b : ℕ) = n - 1) (i j : Fin n) :
    CartanMatrix.D n (Equiv.swap a b i) (Equiv.swap a b j) = CartanMatrix.D n i j := by
  have key : ∀ k : Fin n,
      ((Equiv.swap a b k : Fin n) : ℕ) = n - 1 ∧ (k : ℕ) = n - 2 ∨
      ((Equiv.swap a b k : Fin n) : ℕ) = n - 2 ∧ (k : ℕ) = n - 1 ∨
      ((Equiv.swap a b k : Fin n) : ℕ) = (k : ℕ) ∧ (k : ℕ) ≠ n - 2 ∧ (k : ℕ) ≠ n - 1 := by
    intro k
    rcases eq_or_ne k a with rfl | hka
    · exact Or.inl ⟨by rw [Equiv.swap_apply_left, hb], ha⟩
    · rcases eq_or_ne k b with rfl | hkb
      · exact Or.inr (Or.inl ⟨by rw [Equiv.swap_apply_right, ha], hb⟩)
      · exact Or.inr (Or.inr ⟨by rw [Equiv.swap_apply_of_ne_of_ne hka hkb],
          fun h => hka (Fin.ext (ha ▸ h)), fun h => hkb (Fin.ext (hb ▸ h))⟩)
  have hx := key i
  have hy := key j
  have hi := i.isLt
  have hj := j.isLt
  have e1 : ((Equiv.swap a b i : Fin n) : ℕ) = ((Equiv.swap a b j : Fin n) : ℕ) ↔
      (i : ℕ) = (j : ℕ) := by omega
  have e2 : ((Equiv.swap a b i : Fin n) : ℕ) + 1 = ((Equiv.swap a b j : Fin n) : ℕ) ∧
      ((Equiv.swap a b j : Fin n) : ℕ) + 2 < n ↔ (i : ℕ) + 1 = (j : ℕ) ∧ (j : ℕ) + 2 < n := by
    omega
  have e3 : ((Equiv.swap a b j : Fin n) : ℕ) + 1 = ((Equiv.swap a b i : Fin n) : ℕ) ∧
      ((Equiv.swap a b i : Fin n) : ℕ) + 2 < n ↔ (j : ℕ) + 1 = (i : ℕ) ∧ (i : ℕ) + 2 < n := by
    omega
  have e4 : ((Equiv.swap a b i : Fin n) : ℕ) + 3 = n ∧
      (((Equiv.swap a b j : Fin n) : ℕ) + 2 = n ∨ ((Equiv.swap a b j : Fin n) : ℕ) + 1 = n) ↔
      (i : ℕ) + 3 = n ∧ ((j : ℕ) + 2 = n ∨ (j : ℕ) + 1 = n) := by omega
  have e5 : ((Equiv.swap a b j : Fin n) : ℕ) + 3 = n ∧
      (((Equiv.swap a b i : Fin n) : ℕ) + 2 = n ∨ ((Equiv.swap a b i : Fin n) : ℕ) + 1 = n) ↔
      (j : ℕ) + 3 = n ∧ ((i : ℕ) + 2 = n ∨ (i : ℕ) + 1 = n) := by omega
  simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff, e1, e2, e3, e4, e5]

/-- Swapping the fork nodes is an automorphism of the type-`D` Cartan matrix. -/
@[simp] theorem cartanMatrix_D_graphPermD (n : ℕ) (hn : 4 ≤ n) (i j : Fin n) :
    (DynkinType.D n).cartanMatrix (graphPermD n (by omega) i) (graphPermD n (by omega) j) =
      (DynkinType.D n).cartanMatrix i j := by
  simp only [DynkinType.cartanMatrix_D, graphPermD]
  exact cartanMatrix_D_swap_fork n hn _ _ rfl rfl i j

/-- The pinned order-two permutation is an automorphism of the type-`E₆` Cartan matrix. -/
@[simp] theorem cartanMatrix_E6_graphPermE6 (i j : Fin 6) :
    DynkinType.E6.cartanMatrix (graphPermE6 i) (graphPermE6 j) =
      DynkinType.E6.cartanMatrix i j := by
  fin_cases i <;> fin_cases j <;> simp [DynkinType.cartanMatrix_E6, CartanMatrix.E]

/-- The pinned triality permutation is an automorphism of the type-`D₄` Cartan matrix. -/
@[simp] theorem cartanMatrix_D4_trialityPermD4 (i j : Fin 4) :
    (DynkinType.D 4).cartanMatrix (trialityPermD4 i) (trialityPermD4 j) =
      (DynkinType.D 4).cartanMatrix i j := by
  fin_cases i <;> fin_cases j <;>
    simp [DynkinType.cartanMatrix_D, CartanMatrix.D]

/-- The rank-two permutation exchanges the long and short nodes of `B₂`. -/
@[simp] theorem isLongSimpleRoot_lengthPermRankTwo_iff_not_isLongSimpleRoot_B2 (i : Fin 2) :
    (DynkinType.B 2).IsLongSimpleRoot (lengthPermRankTwo i) ↔
      ¬ (DynkinType.B 2).IsLongSimpleRoot i := by
  fin_cases i <;> simp [DynkinType.isLongSimpleRoot_B, lengthPermRankTwo]

/-- The rank-two permutation exchanges the long and short nodes of `G₂`. -/
@[simp] theorem isLongSimpleRoot_lengthPermRankTwo_iff_not_isLongSimpleRoot_G2 (i : Fin 2) :
    DynkinType.G2.IsLongSimpleRoot (lengthPermRankTwo i) ↔
      ¬ DynkinType.G2.IsLongSimpleRoot i := by
  fin_cases i <;> simp [DynkinType.isLongSimpleRoot_G2, lengthPermRankTwo]

/-- Diagram reversal exchanges the long and short nodes of `F₄`. -/
@[simp] theorem isLongSimpleRoot_lengthPermF4_iff_not_isLongSimpleRoot_F4 (i : Fin 4) :
    DynkinType.F4.IsLongSimpleRoot (lengthPermF4 i) ↔
      ¬ DynkinType.F4.IsLongSimpleRoot i := by
  fin_cases i <;> simp [DynkinType.isLongSimpleRoot_F4, lengthPermF4, graphPermA]

/-! ### The length permutations transpose the Cartan matrix

A length-exchanging permutation is not a symmetry of its diagram: it carries the Cartan matrix to
the transposed matrix, which is the Cartan matrix of the dual diagram. That is the reason the
families `²B₂`, `²G₂` and `²F₄` are built from an odd power of a half-Frobenius rather than from a
graph automorphism composed with a field Frobenius, and it is what makes the exceptional isogeny
attach the two different exponents `1` and `p` to the two root lengths. -/

/-- The rank-two length permutation carries the `B₂` Cartan matrix to its transpose. -/
@[simp] theorem cartanMatrix_B2_lengthPermRankTwo (i j : Fin 2) :
    (DynkinType.B 2).cartanMatrix (lengthPermRankTwo i) (lengthPermRankTwo j) =
      (DynkinType.B 2).cartanMatrix j i := by
  fin_cases i <;> fin_cases j <;> simp [DynkinType.cartanMatrix_B, CartanMatrix.B]

/-- The rank-two length permutation carries the `G₂` Cartan matrix to its transpose. -/
@[simp] theorem cartanMatrix_G2_lengthPermRankTwo (i j : Fin 2) :
    DynkinType.G2.cartanMatrix (lengthPermRankTwo i) (lengthPermRankTwo j) =
      DynkinType.G2.cartanMatrix j i := by
  fin_cases i <;> fin_cases j <;> simp [DynkinType.cartanMatrix_G2, CartanMatrix.G₂]

/-- Diagram reversal carries the `F₄` Cartan matrix to its transpose. -/
@[simp] theorem cartanMatrix_F4_lengthPermF4 (i j : Fin 4) :
    DynkinType.F4.cartanMatrix (lengthPermF4 i) (lengthPermF4 j) =
      DynkinType.F4.cartanMatrix j i := by
  fin_cases i <;> fin_cases j <;>
    simp [DynkinType.cartanMatrix_F4, CartanMatrix.F₄, lengthPermF4, graphPermA]

/-- The rank-two length permutation is not an automorphism of the `B₂` Cartan matrix: the entry it
moves to the corner `(0, 1)` is `-1` rather than `-2`. -/
theorem cartanMatrix_B2_submatrix_lengthPermRankTwo_ne :
    (DynkinType.B 2).cartanMatrix.submatrix lengthPermRankTwo lengthPermRankTwo ≠
      (DynkinType.B 2).cartanMatrix := fun h => by
  have := congrFun (congrFun h 0) 1
  simp [Matrix.submatrix_apply, DynkinType.cartanMatrix_B, CartanMatrix.B] at this

/-- The rank-two length permutation is not an automorphism of the `G₂` Cartan matrix. -/
theorem cartanMatrix_G2_submatrix_lengthPermRankTwo_ne :
    DynkinType.G2.cartanMatrix.submatrix lengthPermRankTwo lengthPermRankTwo ≠
      DynkinType.G2.cartanMatrix := fun h => by
  have := congrFun (congrFun h 0) 1
  simp [Matrix.submatrix_apply, DynkinType.cartanMatrix_G2, CartanMatrix.G₂] at this

/-- Diagram reversal is not an automorphism of the `F₄` Cartan matrix: it exchanges the two entries
`-1` and `-2` across the double bond. -/
theorem cartanMatrix_F4_submatrix_lengthPermF4_ne :
    DynkinType.F4.cartanMatrix.submatrix lengthPermF4 lengthPermF4 ≠ DynkinType.F4.cartanMatrix :=
  fun h => by
  have := congrFun (congrFun h 1) 2
  simp [Matrix.submatrix_apply, DynkinType.cartanMatrix_F4, CartanMatrix.F₄, lengthPermF4,
    graphPermA] at this

/-! ## Symmetries of the Bourbaki-numbered Cartan matrix -/

namespace DynkinType

/-- **The symmetry group of a Bourbaki-numbered Dynkin diagram**: the permutations of the nodes
which preserve the Cartan matrix. This is `TauCeti.matrixSymmetryGroup` at that matrix. -/
def diagramSymmetry (t : DynkinType) : Subgroup (Equiv.Perm (Fin t.rank)) :=
  matrixSymmetryGroup t.cartanMatrix

variable {t : DynkinType} {σ : Equiv.Perm (Fin t.rank)}

/-- The matrix form of membership in `TauCeti.DynkinType.diagramSymmetry`. This is the shape in
which `TauCeti.serreDiagramAut` takes a Cartan-matrix symmetry. -/
theorem mem_diagramSymmetry_iff_submatrix :
    σ ∈ t.diagramSymmetry ↔ t.cartanMatrix.submatrix σ σ = t.cartanMatrix :=
  mem_matrixSymmetryGroup_iff

/-- The entrywise form of membership in `TauCeti.DynkinType.diagramSymmetry`. This is the shape in
which the graph permutations above are shown to be diagram symmetries. -/
theorem mem_diagramSymmetry_iff :
    σ ∈ t.diagramSymmetry ↔ ∀ i j, t.cartanMatrix (σ i) (σ j) = t.cartanMatrix i j :=
  mem_diagramSymmetry_iff_submatrix.trans
    ⟨fun h i j => congrFun₂ h i j, fun h => by ext i j; exact h i j⟩

end DynkinType

end TauCeti

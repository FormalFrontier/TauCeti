/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.RootSystem.RootLength

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
* `TauCeti.graphPermD`: exchange of the two fork nodes of `Dₙ`.
* `TauCeti.graphPermE6`: the order-two symmetry of `E₆`.
* `TauCeti.trialityPermD4`: the order-three triality symmetry of `D₄`.
* `TauCeti.lengthPermRankTwo`: the length-exchanging permutation for `B₂` and `G₂`.
* `TauCeti.lengthPermF4`: the length-exchanging permutation for `F₄`.
-/

public section

namespace TauCeti

/-- The `Aₙ` diagram automorphism, reversing its chain of Bourbaki-numbered nodes. -/
def graphPermA (n : ℕ) : Equiv.Perm (Fin n) :=
  Fin.revPerm

/-- The `Dₙ` diagram automorphism, exchanging its two fork nodes and fixing the chain. -/
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

/-- The type-`A` graph permutation is Mathlib's `Fin.revPerm`, so its node action and its inverse
are `Fin.revPerm_apply` and `Fin.revPerm_symm`, and the rest of the reversal API is the `Fin.rev`
lemmas. -/
@[simp] lemma graphPermA_eq_revPerm (n : ℕ) : graphPermA n = Fin.revPerm := (rfl)

/-- Reversing the `Aₙ` chain twice is the identity. This is not a `simp` lemma because
`TauCeti.graphPermA_eq_revPerm` already rewrites its left-hand side. -/
theorem graphPermA_sq (n : ℕ) : graphPermA n ^ 2 = 1 := by
  ext i
  simp [pow_two, Equiv.Perm.mul_apply]

/-- The type-`D` graph permutation sends the first fork node to the second. -/
@[simp] lemma graphPermD_apply_left (n : ℕ) (hn : 2 ≤ n) :
    graphPermD n hn ⟨n - 2, by omega⟩ = ⟨n - 1, by omega⟩ := by
  simp [graphPermD]

/-- The type-`D` graph permutation sends the second fork node to the first. -/
@[simp] lemma graphPermD_apply_right (n : ℕ) (hn : 2 ≤ n) :
    graphPermD n hn ⟨n - 1, by omega⟩ = ⟨n - 2, by omega⟩ := by
  simp [graphPermD]

/-- The `Dₙ` graph permutation fixes every node except the two fork nodes. -/
lemma graphPermD_apply_of_ne (n : ℕ) (hn : 2 ≤ n) (i : Fin n)
    (hi : (i : ℕ) ≠ n - 2) (hi' : (i : ℕ) ≠ n - 1) : graphPermD n hn i = i := by
  apply Equiv.swap_apply_of_ne_of_ne <;> simpa [Fin.ext_iff]

/-- The type-`D` graph permutation is its own inverse. -/
@[simp] lemma graphPermD_symm (n : ℕ) (hn : 2 ≤ n) :
    (graphPermD n hn).symm = graphPermD n hn := by
  simp [graphPermD]

/-- Exchanging the two `Dₙ` fork nodes twice is the identity. -/
@[simp] theorem graphPermD_sq (n : ℕ) (hn : 2 ≤ n) : graphPermD n hn ^ 2 = 1 := by
  simp [graphPermD, pow_two]

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

/-- The rank-two length permutation sends node `0` to node `1`. -/
@[simp] lemma lengthPermRankTwo_apply_zero : lengthPermRankTwo 0 = 1 := by decide
/-- The rank-two length permutation sends node `1` to node `0`. -/
@[simp] lemma lengthPermRankTwo_apply_one : lengthPermRankTwo 1 = 0 := by decide

/-- Exchanging the two rank-two nodes twice is the identity. -/
@[simp] theorem lengthPermRankTwo_sq : lengthPermRankTwo ^ 2 = 1 := by decide

/-- The `F₄` length permutation is the reversal of the four-node chain, so its node action and its
order are those of `TauCeti.graphPermA`. -/
@[simp] lemma lengthPermF4_eq_graphPermA : lengthPermF4 = graphPermA 4 := (rfl)

/-- Reversal is an automorphism of the type-`A` Cartan matrix. -/
theorem cartanMatrix_A_graphPermA (n : ℕ) (i j : Fin n) :
    (DynkinType.A n).cartanMatrix (graphPermA n i) (graphPermA n j) =
      (DynkinType.A n).cartanMatrix i j := by
  simp only [DynkinType.cartanMatrix_A, CartanMatrix.A, Matrix.of_apply, graphPermA_eq_revPerm,
    Fin.revPerm_apply, Fin.ext_iff, Fin.val_rev]
  split_ifs <;> omega

private lemma cartanMatrix_D_fork_rows {n : ℕ} (hn : 4 ≤ n) (j : Fin n)
    (hj : (j : ℕ) ≠ n - 2) (hj' : (j : ℕ) ≠ n - 1) :
    CartanMatrix.D n ⟨n - 1, by omega⟩ j = CartanMatrix.D n ⟨n - 2, by omega⟩ j := by
  simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

/-- Swapping the fork nodes is an automorphism of the type-`D` Cartan matrix. -/
theorem cartanMatrix_D_graphPermD (n : ℕ) (hn : 4 ≤ n) (i j : Fin n) :
    (DynkinType.D n).cartanMatrix (graphPermD n (by omega) i) (graphPermD n (by omega) j) =
      (DynkinType.D n).cartanMatrix i j := by
  let a : Fin n := ⟨n - 2, by omega⟩
  let b : Fin n := ⟨n - 1, by omega⟩
  rw [DynkinType.cartanMatrix_D]
  rcases eq_or_ne i a with rfl | hi
  · rcases eq_or_ne j a with rfl | hj
    · simp [a]
    · rcases eq_or_ne j b with rfl | hj'
      · rw [graphPermD_apply_left, graphPermD_apply_right]
        simpa [a, b] using ((CartanMatrix.D_isSymm n).apply b a).symm
      · have hja : (j : ℕ) ≠ n - 2 := by simpa [a, Fin.ext_iff] using hj
        have hjb : (j : ℕ) ≠ n - 1 := by simpa [b, Fin.ext_iff] using hj'
        rw [graphPermD_apply_left, graphPermD_apply_of_ne n (by omega) j hja hjb]
        exact cartanMatrix_D_fork_rows hn j hja hjb
  · rcases eq_or_ne i b with rfl | hi'
    · rcases eq_or_ne j a with rfl | hj
      · rw [graphPermD_apply_right, graphPermD_apply_left]
        simpa [a, b] using (CartanMatrix.D_isSymm n).apply b a
      · rcases eq_or_ne j b with rfl | hj'
        · simp [b]
        · have hja : (j : ℕ) ≠ n - 2 := by simpa [a, Fin.ext_iff] using hj
          have hjb : (j : ℕ) ≠ n - 1 := by simpa [b, Fin.ext_iff] using hj'
          rw [graphPermD_apply_right, graphPermD_apply_of_ne n (by omega) j hja hjb]
          exact (cartanMatrix_D_fork_rows hn j hja hjb).symm
    · have hia : (i : ℕ) ≠ n - 2 := by simpa [a, Fin.ext_iff] using hi
      have hib : (i : ℕ) ≠ n - 1 := by simpa [b, Fin.ext_iff] using hi'
      rw [graphPermD_apply_of_ne n (by omega) i hia hib]
      rcases eq_or_ne j a with rfl | hj
      · rw [graphPermD_apply_left]
        calc
          CartanMatrix.D n i ⟨n - 1, by omega⟩ =
              CartanMatrix.D n ⟨n - 1, by omega⟩ i := (CartanMatrix.D_isSymm n).apply _ _
          _ = CartanMatrix.D n ⟨n - 2, by omega⟩ i :=
            cartanMatrix_D_fork_rows hn i hia hib
          _ = CartanMatrix.D n i a := by
            simpa [a] using ((CartanMatrix.D_isSymm n).apply a i).symm
      · rcases eq_or_ne j b with rfl | hj'
        · rw [graphPermD_apply_right]
          calc
            CartanMatrix.D n i ⟨n - 2, by omega⟩ =
                CartanMatrix.D n ⟨n - 2, by omega⟩ i := (CartanMatrix.D_isSymm n).apply _ _
            _ = CartanMatrix.D n ⟨n - 1, by omega⟩ i :=
              (cartanMatrix_D_fork_rows hn i hia hib).symm
            _ = CartanMatrix.D n i b := by
              simpa [b] using ((CartanMatrix.D_isSymm n).apply b i).symm
        · have hja : (j : ℕ) ≠ n - 2 := by simpa [a, Fin.ext_iff] using hj
          have hjb : (j : ℕ) ≠ n - 1 := by simpa [b, Fin.ext_iff] using hj'
          rw [graphPermD_apply_of_ne n (by omega) j hja hjb]

/-- The pinned order-two permutation is an automorphism of the type-`E₆` Cartan matrix. -/
theorem cartanMatrix_E6_graphPermE6 (i j : Fin 6) :
    DynkinType.E6.cartanMatrix (graphPermE6 i) (graphPermE6 j) =
      DynkinType.E6.cartanMatrix i j := by
  fin_cases i <;> fin_cases j <;> simp [DynkinType.cartanMatrix_E6, CartanMatrix.E₆]

/-- The pinned triality permutation is an automorphism of the type-`D₄` Cartan matrix. -/
theorem cartanMatrix_D4_trialityPermD4 (i j : Fin 4) :
    (DynkinType.D 4).cartanMatrix (trialityPermD4 i) (trialityPermD4 j) =
      (DynkinType.D 4).cartanMatrix i j := by
  fin_cases i <;> fin_cases j <;>
    simp [DynkinType.cartanMatrix_D, CartanMatrix.D]

/-- The rank-two permutation exchanges the long and short nodes of `B₂`. -/
theorem isLongSimpleRoot_lengthPermRankTwo_iff_not_isLongSimpleRoot_B2 (i : Fin 2) :
    (DynkinType.B 2).IsLongSimpleRoot (lengthPermRankTwo i) ↔
      ¬ (DynkinType.B 2).IsLongSimpleRoot i := by
  fin_cases i <;> simp [DynkinType.isLongSimpleRoot_B, lengthPermRankTwo]

/-- The rank-two permutation exchanges the long and short nodes of `G₂`. -/
theorem isLongSimpleRoot_lengthPermRankTwo_iff_not_isLongSimpleRoot_G2 (i : Fin 2) :
    DynkinType.G2.IsLongSimpleRoot (lengthPermRankTwo i) ↔
      ¬ DynkinType.G2.IsLongSimpleRoot i := by
  fin_cases i <;> simp [DynkinType.isLongSimpleRoot_G2, lengthPermRankTwo]

/-- Diagram reversal exchanges the long and short nodes of `F₄`. -/
theorem isLongSimpleRoot_lengthPermF4_iff_not_isLongSimpleRoot_F4 (i : Fin 4) :
    DynkinType.F4.IsLongSimpleRoot (lengthPermF4 i) ↔
      ¬ DynkinType.F4.IsLongSimpleRoot i := by
  fin_cases i <;> simp [DynkinType.isLongSimpleRoot_F4]

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.D.Basic
public import TauCeti.RepresentationTheory.Spin.Weight

/-!
# Type `D` spin weights in the simply connected character lattice

The spinor module has weights `1 / 2 * (±e₀ ± ⋯ ± e_{n-1})` in the usual orthonormal
coordinates. The simply connected type `Dₙ` datum instead writes its character lattice in the
fundamental-weight basis, so a weight is recorded by its pairings with the simple coroots

```text
eᵢ - eᵢ₊₁  (i + 1 < n),       e_{n-2} + e_{n-1}  (i + 1 = n).
```

In those coordinates all spin weights are integral. This file defines the resulting sign-vector
family `TauCeti.DynkinType.typeDSpinWeight`, compares it coordinate by coordinate with
`TauCeti.spinWeight`, and proves that the family spans the full character lattice `Fin n → ℤ`.
Using all spinor weights is essential in even rank: either half-spin family alone reaches only
one of the two nonzero spinor cosets of the root lattice.

The spanning result is the full-weight input needed to construct the simply connected type `D`
Chevalley carrier from the spin representation. The adjoint representation supplies only the
index-four root lattice.

## Main declarations

* `TauCeti.DynkinType.typeDSpinWeight`: a spin weight in fundamental-weight coordinates.
* `TauCeti.DynkinType.algebraMap_typeDSpinWeight_apply`: comparison with the half-integer
  orthonormal coordinates of `TauCeti.spinWeight`.
* `TauCeti.DynkinType.span_range_typeDSpinWeight_eq_top`: the spin weights generate the full
  simply connected character lattice.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Section 20.2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Section 13.2.

The integral-coordinate and spanning API follows the parallel type `B` construction in Tau Ceti
PR #4847. The fork coordinate and the use of both half-spin parities are the type `D` changes.

This advances Layer 9, "The Chevalley--Demazure construction", of the ReductiveGroups roadmap:
the explicit simply connected type `D` carrier requires an admissible spin lattice whose weights
generate the full character lattice.
-/

public section

namespace TauCeti.DynkinType

open Set Submodule

/-! ## Integral spin weights -/

/-- The next coordinate used to read a type `D` spin weight, staying at the terminal coordinate
when there is no successor. -/
def typeDSpinNext {n : ℕ} (i : Fin n) : Fin n :=
  ⟨min ((i : ℕ) + 1) (n - 1), by have := i.isLt; omega⟩

/-- The preceding coordinate used in the fork-root coordinate. -/
def typeDSpinPrev {n : ℕ} (i : Fin n) : Fin n :=
  ⟨(i : ℕ) - 1, by have := i.isLt; omega⟩

/-- The value of `typeDSpinPrev` is the truncated predecessor of the input value. -/
@[simp]
theorem typeDSpinPrev_val {n : ℕ} (i : Fin n) :
    (typeDSpinPrev i : ℕ) = (i : ℕ) - 1 :=
  (rfl)

/-- Away from the terminal coordinate, `typeDSpinNext` increments the index. -/
@[simp]
theorem typeDSpinNext_val_of_lt {n : ℕ} (i : Fin n) (h : (i : ℕ) + 1 < n) :
    (typeDSpinNext i : ℕ) = (i : ℕ) + 1 := by
  simp only [typeDSpinNext, Fin.val_mk]
  omega

/-- At the terminal coordinate, `typeDSpinNext` fixes the index. -/
@[simp]
theorem typeDSpinNext_eq_self_of_not_lt {n : ℕ} (i : Fin n) (h : ¬(i : ℕ) + 1 < n) :
    typeDSpinNext i = i := by
  apply Fin.ext
  simp only [typeDSpinNext, Fin.val_mk]
  have := i.isLt
  omega

private theorem typeDSpinNext_eq_mk {n : ℕ} (i : Fin n) (h : (i : ℕ) + 1 < n) :
    typeDSpinNext i = (⟨(i : ℕ) + 1, h⟩ : Fin n) := by
  apply Fin.ext
  exact typeDSpinNext_val_of_lt i h

private theorem typeDSpinNext_le_iff {n : ℕ} (i j : Fin n) (h : (i : ℕ) + 1 < n) :
    typeDSpinNext i ≤ j ↔ (i : ℕ) + 1 ≤ (j : ℕ) := by
  rw [typeDSpinNext_eq_mk i h]
  exact Fin.mk_le_mk

private theorem typeDSpinPrev_le_iff {n : ℕ} (i j : Fin n) :
    typeDSpinPrev i ≤ j ↔ (i : ℕ) - 1 ≤ (j : ℕ) := by
  exact Fin.mk_le_mk

/-- The weight of a type `Dₙ` spinor basis vector in fundamental-weight coordinates.

The finite set `s` records the positive signs. At a nonterminal node the coordinate is the
half-difference of two adjacent signs, hence `1`, `0`, or `-1`. At the terminal fork node it is
the half-sum of the last two signs. -/
def typeDSpinWeight {n : ℕ} (s : Finset (Fin n)) (i : Fin n) : ℤ :=
  if (i : ℕ) + 1 < n then
    (if i ∈ s then 1 else 0) -
      if typeDSpinNext i ∈ s then 1 else 0
  else
    (if typeDSpinPrev i ∈ s then 1 else 0) +
      (if i ∈ s then 1 else 0) - 1

/-- The coordinate formula for a type `D` spin weight. -/
theorem typeDSpinWeight_apply {n : ℕ} (s : Finset (Fin n)) (i : Fin n) :
    typeDSpinWeight s i =
      if (i : ℕ) + 1 < n then
        (if i ∈ s then 1 else 0) -
          if typeDSpinNext i ∈ s then 1 else 0
      else
        (if typeDSpinPrev i ∈ s then 1 else 0) +
          (if i ∈ s then 1 else 0) - 1 :=
  (rfl)

/-- In rational coordinates, `typeDSpinWeight` is obtained from the orthonormal sign weight by
pairing with the simple coroot: take an adjacent difference away from the terminal node and the
sum of the last two coordinates at the terminal fork node. -/
theorem algebraMap_typeDSpinWeight_apply {n : ℕ} (s : Finset (Fin n)) (i : Fin n) :
    algebraMap ℤ ℚ (typeDSpinWeight s i) =
      if h : (i : ℕ) + 1 < n then
        spinWeight ℚ s i - spinWeight ℚ s (⟨(i : ℕ) + 1, h⟩ : Fin n)
      else spinWeight ℚ s (typeDSpinPrev i) + spinWeight ℚ s i := by
  classical
  rw [typeDSpinWeight_apply]
  by_cases hnext : (i : ℕ) + 1 < n
  · rw [ite_eq_left hnext, typeDSpinNext_eq_mk i hnext, dite_eq_left hnext]
    by_cases hi : i ∈ s
    · rw [ite_eq_left hi]
      by_cases hsucc : (⟨(i : ℕ) + 1, hnext⟩ : Fin n) ∈ s
      · rw [ite_eq_left hsucc, sub_self, map_zero, spinWeight_of_mem hi,
          spinWeight_of_mem hsucc, sub_self]
      · rw [ite_eq_right hsucc, sub_zero, map_one]
        linarith [spinWeight_add_self_of_mem (K := ℚ) hi,
          spinWeight_add_self_of_notMem (K := ℚ) hsucc]
    · rw [ite_eq_right hi]
      by_cases hsucc : (⟨(i : ℕ) + 1, hnext⟩ : Fin n) ∈ s
      · rw [ite_eq_left hsucc, zero_sub, map_neg, map_one]
        linarith [spinWeight_add_self_of_notMem (K := ℚ) hi,
          spinWeight_add_self_of_mem (K := ℚ) hsucc]
      · rw [ite_eq_right hsucc, sub_self, map_zero, spinWeight_of_notMem hi,
          spinWeight_of_notMem hsucc, sub_self]
  · rw [ite_eq_right hnext, dite_eq_right hnext]
    by_cases hprev : typeDSpinPrev i ∈ s
    · rw [ite_eq_left hprev]
      by_cases hi : i ∈ s
      · rw [ite_eq_left hi]
        norm_num
        linarith [spinWeight_add_self_of_mem (K := ℚ) hprev,
          spinWeight_add_self_of_mem (K := ℚ) hi]
      · rw [ite_eq_right hi]
        norm_num
        linarith [spinWeight_add_self_of_mem (K := ℚ) hprev,
          spinWeight_add_self_of_notMem (K := ℚ) hi]
    · rw [ite_eq_right hprev]
      by_cases hi : i ∈ s
      · rw [ite_eq_left hi]
        norm_num
        linarith [spinWeight_add_self_of_notMem (K := ℚ) hprev,
          spinWeight_add_self_of_mem (K := ℚ) hi]
      · rw [ite_eq_right hi]
        norm_num
        linarith [spinWeight_add_self_of_notMem (K := ℚ) hprev,
          spinWeight_add_self_of_notMem (K := ℚ) hi]

/-- The comparison with half-integer spin weights, as an equality of coordinate vectors. -/
theorem algebraMap_typeDSpinWeight {n : ℕ} (s : Finset (Fin n)) :
    (fun i : Fin n => algebraMap ℤ ℚ (typeDSpinWeight s i)) =
      fun i : Fin n => if h : (i : ℕ) + 1 < n then
        spinWeight ℚ s i - spinWeight ℚ s (⟨(i : ℕ) + 1, h⟩ : Fin n)
      else spinWeight ℚ s (typeDSpinPrev i) + spinWeight ℚ s i := by
  funext i
  exact algebraMap_typeDSpinWeight_apply s i

/-- For a valid type `Dₙ`, the integral coordinate of a spin weight is its pairing with the
corresponding Bourbaki simple coroot in orthonormal coordinates. Type `D` is simply laced, so the
simple coroot is `typeDSimpleRoot n hn i`. -/
theorem algebraMap_typeDSpinWeight_eq_dotProduct {n : ℕ} (hn : 4 ≤ n)
    (s : Finset (Fin n)) (i : Fin n) :
    algebraMap ℤ ℚ (typeDSpinWeight s i) =
      spinWeight ℚ s ⬝ᵥ
        fun j => algebraMap ℤ ℚ (typeDSimpleRoot n hn i j) := by
  rw [algebraMap_typeDSpinWeight_apply]
  by_cases hnext : (i : ℕ) + 1 < n
  · rw [dite_eq_left hnext]
    have hmap :
        (fun j => algebraMap ℤ ℚ (typeDSimpleRoot n hn i j)) =
          (Pi.single i 1 - Pi.single (⟨(i : ℕ) + 1, hnext⟩ : Fin n) 1 :
            Fin n → ℚ) := by
      rw [typeDSimpleRoot_of_add_one_lt hn hnext]
      funext j
      simp [Pi.sub_apply, Pi.single_apply]
    rw [hmap]
    rw [dotProduct_sub, dotProduct_single, dotProduct_single, mul_one, mul_one]
  · have hi : i = (⟨n - 1, by omega⟩ : Fin n) := by
      apply Fin.ext
      dsimp only
      omega
    have hprev : typeDSpinPrev i = (⟨n - 2, by omega⟩ : Fin n) := by
      apply Fin.ext
      simp only [typeDSpinPrev_val]
      omega
    rw [dite_eq_right hnext]
    have hmap :
        (fun j => algebraMap ℤ ℚ (typeDSimpleRoot n hn i j)) =
          (Pi.single (⟨n - 2, by omega⟩ : Fin n) 1 +
            Pi.single (⟨n - 1, by omega⟩ : Fin n) 1 : Fin n → ℚ) := by
      rw [typeDSimpleRoot_of_not_add_one_lt hn hnext]
      funext j
      simp [Pi.add_apply, Pi.single_apply]
    rw [hmap]
    rw [dotProduct_add, dotProduct_single, dotProduct_single, mul_one, mul_one]
    exact congrArg₂ (· + ·) (congrArg (spinWeight ℚ s) hprev)
      (congrArg (spinWeight ℚ s) hi)

/-! ## A spanning family -/

/-- The sign set which is positive through `i` and negative after `i`. -/
private def typeDSpinCut {n : ℕ} (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun j => j ≤ i

private theorem mem_typeDSpinCut_iff {n : ℕ} (i j : Fin n) :
    j ∈ typeDSpinCut i ↔ j ≤ i := by
  simp [typeDSpinCut]

/-- The all-positive sign weight has only its terminal fundamental-weight coordinate nonzero. -/
private theorem typeDSpinWeight_univ_apply {n : ℕ} (i : Fin n) :
    typeDSpinWeight (Finset.univ : Finset (Fin n)) i =
      if (i : ℕ) + 1 = n then 1 else 0 := by
  rw [typeDSpinWeight_apply]
  by_cases hnext : (i : ℕ) + 1 < n
  · have hne : ¬(i : ℕ) + 1 = n := by omega
    rw [ite_eq_left hnext, ite_eq_right hne]
    simp
  · have heq : (i : ℕ) + 1 = n := by omega
    rw [ite_eq_right hnext, ite_eq_left heq]
    simp

/-- At the terminal node, the cut sign weight is the terminal coordinate basis vector. -/
private theorem typeDSpinWeight_cut_eq_single_of_isLast {n : ℕ} (i : Fin n)
    (hi : (i : ℕ) + 1 = n) :
    typeDSpinWeight (typeDSpinCut i) = Pi.single i 1 := by
  classical
  funext j
  rw [typeDSpinWeight_apply, Pi.single_apply]
  simp only [mem_typeDSpinCut_iff]
  by_cases hjnext : (j : ℕ) + 1 < n
  · rw [ite_eq_left hjnext]
    simp only [typeDSpinNext_le_iff j i hjnext]
    split_ifs <;> omega
  · rw [ite_eq_right hjnext]
    simp only [typeDSpinPrev_le_iff]
    split_ifs <;> omega

/-- At the penultimate node, the cut sign weight is the penultimate coordinate basis vector. -/
private theorem typeDSpinWeight_cut_eq_single_of_isPenultimate {n : ℕ} (i : Fin n)
    (hi : (i : ℕ) + 2 = n) :
    typeDSpinWeight (typeDSpinCut i) = Pi.single i 1 := by
  classical
  funext j
  rw [typeDSpinWeight_apply, Pi.single_apply]
  simp only [mem_typeDSpinCut_iff]
  by_cases hjnext : (j : ℕ) + 1 < n
  · rw [ite_eq_left hjnext]
    simp only [typeDSpinNext_le_iff j i hjnext]
    split_ifs <;> omega
  · rw [ite_eq_right hjnext]
    simp only [typeDSpinPrev_le_iff]
    split_ifs <;> omega

/-- Before the two fork nodes, adding the all-positive weight to the cut sign weight gives the
corresponding coordinate basis vector. -/
private theorem typeDSpinWeight_cut_add_univ_eq_single {n : ℕ} (i : Fin n)
    (hi : (i : ℕ) + 2 < n) :
    typeDSpinWeight (typeDSpinCut i) +
        typeDSpinWeight (Finset.univ : Finset (Fin n)) = Pi.single i 1 := by
  classical
  funext j
  rw [Pi.add_apply, typeDSpinWeight_apply, typeDSpinWeight_univ_apply, Pi.single_apply]
  simp only [mem_typeDSpinCut_iff]
  by_cases hjnext : (j : ℕ) + 1 < n
  · have hjnotlast : ¬(j : ℕ) + 1 = n := by omega
    rw [ite_eq_left hjnext, ite_eq_right hjnotlast]
    simp only [typeDSpinNext_le_iff j i hjnext]
    split_ifs <;> omega
  · have hjlast : (j : ℕ) + 1 = n := by omega
    rw [ite_eq_right hjnext, ite_eq_left hjlast]
    simp only [typeDSpinPrev_le_iff]
    split_ifs <;> omega

/-- **The type `Dₙ` spin weights generate the full simply connected character lattice.**

The all-positive sign sequence has weight `ω_{n-1}`. A sign sequence positive through a node
strictly before the fork has weight `ωᵢ - ω_{n-1}`; at the penultimate node it has weight
`ω_{n-2}`. Thus the weights from both half-spin parities contain enough differences to generate
every fundamental-weight basis vector. -/
theorem span_range_typeDSpinWeight_eq_top (n : ℕ) :
    Submodule.span ℤ (Set.range (typeDSpinWeight (n := n))) = ⊤ := by
  apply top_unique
  rw [← (Pi.basisFun ℤ (Fin n)).span_eq]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  rw [Pi.basisFun_apply]
  by_cases hlast : (i : ℕ) + 1 = n
  · rw [← typeDSpinWeight_cut_eq_single_of_isLast i hlast]
    exact Submodule.subset_span ⟨typeDSpinCut i, rfl⟩
  · by_cases hpenultimate : (i : ℕ) + 2 = n
    · rw [← typeDSpinWeight_cut_eq_single_of_isPenultimate i hpenultimate]
      exact Submodule.subset_span ⟨typeDSpinCut i, rfl⟩
    · have hi : (i : ℕ) + 2 < n := by omega
      rw [← typeDSpinWeight_cut_add_univ_eq_single i hi]
      exact Submodule.add_mem _
        (Submodule.subset_span ⟨typeDSpinCut i, rfl⟩)
        (Submodule.subset_span ⟨Finset.univ, rfl⟩)

end TauCeti.DynkinType

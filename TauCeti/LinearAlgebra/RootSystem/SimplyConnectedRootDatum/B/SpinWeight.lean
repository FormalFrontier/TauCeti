/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.B.Datum
public import TauCeti.RepresentationTheory.Spin.Weight

/-!
# Type `B` spin weights in the simply connected character lattice

The spinor module has weights `1 / 2 * (±e₀ ± ⋯ ± e_{n-1})` in the usual orthonormal
coordinates.  The simply connected type `Bₙ` datum instead writes its character lattice in the
fundamental-weight basis, so a weight is recorded by its pairings with the simple coroots

```text
eᵢ - eᵢ₊₁  (i + 1 < n),       2e_{n-1}  (i + 1 = n).
```

In those coordinates all spin weights are integral.  This file defines the resulting sign-vector
family `TauCeti.DynkinType.typeBSpinWeight`, compares it coordinate by coordinate with
`TauCeti.spinWeight`, and proves that the family spans the full character lattice `Fin n → ℤ`.
The spanning result is the full-weight input needed to construct the simply connected type `B`
Chevalley carrier from the spin representation: the adjoint representation supplies only the
index-two root lattice.

## Main declarations

* `TauCeti.DynkinType.typeBSpinWeight`: a spin weight in fundamental-weight coordinates.
* `TauCeti.DynkinType.algebraMap_typeBSpinWeight_apply`: comparison with the half-integer
  orthonormal coordinates of `TauCeti.spinWeight`.
* `TauCeti.DynkinType.span_range_typeBSpinWeight_eq_top`: the spin weights generate the full
  simply connected character lattice.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate II.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Section 20.1.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Section 13.2.

This advances Layer 9, "The Chevalley--Demazure construction", of the ReductiveGroups roadmap:
the explicit simply connected type `B` carrier requires an admissible spin lattice whose weights
generate the full character lattice.
-/

public section

namespace TauCeti.DynkinType

open Set Submodule

/-! ## Integral spin weights -/

/-- The next coordinate used to read a type `B` spin weight, staying at the terminal coordinate
when there is no successor. -/
def typeBSpinNext {n : ℕ} (i : Fin n) : Fin n :=
  ⟨min ((i : ℕ) + 1) (n - 1), by have := i.isLt; omega⟩

/-- Away from the terminal coordinate, `typeBSpinNext` increments the index. -/
@[simp]
theorem typeBSpinNext_val_of_lt {n : ℕ} (i : Fin n) (h : (i : ℕ) + 1 < n) :
    (typeBSpinNext i : ℕ) = (i : ℕ) + 1 := by
  simp only [typeBSpinNext, Fin.val_mk]
  omega

/-- At the terminal coordinate, `typeBSpinNext` fixes the index. -/
@[simp]
theorem typeBSpinNext_eq_self_of_not_lt {n : ℕ} (i : Fin n) (h : ¬(i : ℕ) + 1 < n) :
    typeBSpinNext i = i := by
  apply Fin.ext
  simp only [typeBSpinNext, Fin.val_mk]
  have := i.isLt
  omega

private theorem typeBSpinNext_eq_mk {n : ℕ} (i : Fin n) (h : (i : ℕ) + 1 < n) :
    typeBSpinNext i = (⟨(i : ℕ) + 1, h⟩ : Fin n) := by
  apply Fin.ext
  exact typeBSpinNext_val_of_lt i h

private theorem typeBSpinNext_le_iff {n : ℕ} (i j : Fin n) (h : (i : ℕ) + 1 < n) :
    typeBSpinNext i ≤ j ↔ (i : ℕ) + 1 ≤ (j : ℕ) := by
  rw [typeBSpinNext_eq_mk i h]
  exact Fin.mk_le_mk

/-- The weight of a type `Bₙ` spinor basis vector in fundamental-weight coordinates.

The finite set `s` records the positive signs. At a nonterminal node the coordinate is the
half-difference of two adjacent signs, hence `1`, `0`, or `-1`; at the terminal node it is the
last sign, because the last simple coroot is `2e_{n-1}`. -/
def typeBSpinWeight {n : ℕ} (s : Finset (Fin n)) (i : Fin n) : ℤ :=
  if (i : ℕ) + 1 < n then
    (if i ∈ s then 1 else 0) -
      if typeBSpinNext i ∈ s then 1 else 0
  else 2 * (if i ∈ s then 1 else 0) - 1

/-- The coordinate formula for a type `B` spin weight. -/
theorem typeBSpinWeight_apply {n : ℕ} (s : Finset (Fin n)) (i : Fin n) :
    typeBSpinWeight s i =
      if (i : ℕ) + 1 < n then
        (if i ∈ s then 1 else 0) -
          if typeBSpinNext i ∈ s then 1 else 0
      else 2 * (if i ∈ s then 1 else 0) - 1 :=
  (rfl)

/-- In rational coordinates, `typeBSpinWeight` is obtained from the orthonormal sign weight by
pairing with the simple coroot: take an adjacent difference away from the terminal node and
double the terminal coordinate. -/
theorem algebraMap_typeBSpinWeight_apply {n : ℕ} (s : Finset (Fin n)) (i : Fin n) :
    algebraMap ℤ ℚ (typeBSpinWeight s i) =
      if h : (i : ℕ) + 1 < n then
        spinWeight ℚ s i - spinWeight ℚ s (⟨(i : ℕ) + 1, h⟩ : Fin n)
      else spinWeight ℚ s i + spinWeight ℚ s i := by
  classical
  rw [typeBSpinWeight_apply]
  by_cases hnext : (i : ℕ) + 1 < n
  · rw [ite_eq_left hnext, typeBSpinNext_eq_mk i hnext, dite_eq_left hnext]
    by_cases hi : i ∈ s
    · rw [ite_eq_left hi]
      by_cases hsucc : (⟨(i : ℕ) + 1, hnext⟩ : Fin n) ∈ s
      · have hweight :
            spinWeight ℚ s (⟨(i : ℕ) + 1, hnext⟩ : Fin n) = ⅟(2 : ℚ) :=
          spinWeight_of_mem hsucc
        rw [ite_eq_left hsucc, sub_self, map_zero, spinWeight_of_mem hi, hweight, sub_self]
      · rw [ite_eq_right hsucc, sub_zero, map_one]
        linarith [spinWeight_add_self_of_mem (K := ℚ) hi,
          spinWeight_add_self_of_notMem (K := ℚ) hsucc]
    · rw [ite_eq_right hi]
      by_cases hsucc : (⟨(i : ℕ) + 1, hnext⟩ : Fin n) ∈ s
      · rw [ite_eq_left hsucc, zero_sub, map_neg, map_one]
        linarith [spinWeight_add_self_of_notMem (K := ℚ) hi,
          spinWeight_add_self_of_mem (K := ℚ) hsucc]
      · have hweight :
            spinWeight ℚ s (⟨(i : ℕ) + 1, hnext⟩ : Fin n) = -⅟(2 : ℚ) :=
          spinWeight_of_notMem hsucc
        rw [ite_eq_right hsucc, sub_self, map_zero, spinWeight_of_notMem hi, hweight, sub_self]
  · rw [ite_eq_right hnext, dite_eq_right hnext]
    by_cases hi : i ∈ s
    · rw [ite_eq_left hi]
      norm_num
      exact (spinWeight_add_self_of_mem (K := ℚ) hi).symm
    · rw [ite_eq_right hi]
      norm_num
      exact (spinWeight_add_self_of_notMem (K := ℚ) hi).symm

/-- The comparison with half-integer spin weights, as an equality of coordinate vectors. -/
theorem algebraMap_typeBSpinWeight {n : ℕ} (s : Finset (Fin n)) :
    (fun i : Fin n => algebraMap ℤ ℚ (typeBSpinWeight s i)) =
      fun i : Fin n => if h : (i : ℕ) + 1 < n then
        spinWeight ℚ s i - spinWeight ℚ s (⟨(i : ℕ) + 1, h⟩ : Fin n)
      else spinWeight ℚ s i + spinWeight ℚ s i := by
  funext i
  exact algebraMap_typeBSpinWeight_apply s i

/-! ## A spanning family -/

/-- The sign set which is positive through `i` and negative after `i`. Its spin weight is the
fundamental weight vector at `i`, minus the terminal fundamental weight when `i` is nonterminal. -/
private def typeBSpinCut {n : ℕ} (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun j => j ≤ i

private theorem mem_typeBSpinCut_iff {n : ℕ} (i j : Fin n) :
    j ∈ typeBSpinCut i ↔ j ≤ i := by
  simp [typeBSpinCut]

/-- The all-positive sign weight has only its terminal fundamental-weight coordinate nonzero. -/
private theorem typeBSpinWeight_univ_apply {n : ℕ} (i : Fin n) :
    typeBSpinWeight (Finset.univ : Finset (Fin n)) i =
      if (i : ℕ) + 1 = n then 1 else 0 := by
  rw [typeBSpinWeight_apply]
  by_cases hnext : (i : ℕ) + 1 < n
  · have hne : ¬(i : ℕ) + 1 = n := by omega
    rw [ite_eq_left hnext, ite_eq_right hne]
    simp
  · have heq : (i : ℕ) + 1 = n := by omega
    rw [ite_eq_right hnext, ite_eq_left heq]
    simp

/-- At a terminal node, the corresponding cut sign weight is the coordinate basis vector. -/
private theorem typeBSpinWeight_cut_eq_single_of_isLast {n : ℕ} (i : Fin n)
    (hi : (i : ℕ) + 1 = n) :
    typeBSpinWeight (typeBSpinCut i) = Pi.single i 1 := by
  classical
  funext j
  rw [typeBSpinWeight_apply, Pi.single_apply]
  simp only [mem_typeBSpinCut_iff]
  split_ifs with hjnext hji hjsucc hjlast hji <;> simp_all <;> omega

/-- At a nonterminal node, adding the all-positive weight to the cut sign weight gives the
corresponding coordinate basis vector. -/
private theorem typeBSpinWeight_cut_add_univ_eq_single {n : ℕ} (i : Fin n)
    (hi : (i : ℕ) + 1 < n) :
    typeBSpinWeight (typeBSpinCut i) +
        typeBSpinWeight (Finset.univ : Finset (Fin n)) = Pi.single i 1 := by
  classical
  funext j
  have hjlt := j.isLt
  rw [Pi.add_apply, typeBSpinWeight_apply, typeBSpinWeight_univ_apply, Pi.single_apply]
  by_cases hjnext : (j : ℕ) + 1 < n
  · have hjnotlast : ¬(j : ℕ) + 1 = n := by omega
    rw [ite_eq_left hjnext, ite_eq_right hjnotlast]
    simp only [mem_typeBSpinCut_iff]
    simp only [typeBSpinNext_le_iff j i hjnext]
    split_ifs <;> omega
  · have hjlast : (j : ℕ) + 1 = n := by omega
    rw [ite_eq_right hjnext, ite_eq_left hjlast]
    simp only [mem_typeBSpinCut_iff]
    split_ifs <;> omega

/-- **The type `Bₙ` spin weights generate the full simply connected character lattice.**

For a nonterminal node `i`, the sign sequence positive through `i` has weight
`ωᵢ - ω_{n-1}`, while the all-positive sequence has weight `ω_{n-1}`. At the terminal node the
cut sequence is already `ω_{n-1}`. Thus every fundamental-weight basis vector lies in the span. -/
theorem span_range_typeBSpinWeight_eq_top (n : ℕ) :
    Submodule.span ℤ (Set.range (typeBSpinWeight (n := n))) = ⊤ := by
  apply top_unique
  rw [← (Pi.basisFun ℤ (Fin n)).span_eq]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  rw [Pi.basisFun_apply]
  by_cases hi : (i : ℕ) + 1 = n
  · rw [← typeBSpinWeight_cut_eq_single_of_isLast i hi]
    exact Submodule.subset_span ⟨typeBSpinCut i, rfl⟩
  · have hi' : (i : ℕ) + 1 < n := by omega
    rw [← typeBSpinWeight_cut_add_univ_eq_single i hi']
    exact Submodule.add_mem _
      (Submodule.subset_span ⟨typeBSpinCut i, rfl⟩)
      (Submodule.subset_span ⟨Finset.univ, rfl⟩)

end TauCeti.DynkinType

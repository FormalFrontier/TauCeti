/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.SuccPredOrder
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

/-- The weight of a type `Bₙ` spinor basis vector in fundamental-weight coordinates.

The finite set `s` records the positive signs. At a nonterminal node the coordinate is the
half-difference of two adjacent signs, hence `1`, `0`, or `-1`; at the terminal node it is the
last sign, because the last simple coroot is `2e_{n-1}`. -/
def typeBSpinWeight {n : ℕ} (s : Finset (Fin n)) (i : Fin n) : ℤ :=
  if (i : ℕ) + 1 < n then
    (if i ∈ s then 1 else 0) -
      if Order.succ i ∈ s then 1 else 0
  else 2 * (if i ∈ s then 1 else 0) - 1

/-- The coordinate formula for a type `B` spin weight. -/
theorem typeBSpinWeight_apply {n : ℕ} (s : Finset (Fin n)) (i : Fin n) :
    typeBSpinWeight s i =
      if (i : ℕ) + 1 < n then
        (if i ∈ s then 1 else 0) -
          if Order.succ i ∈ s then 1 else 0
      else 2 * (if i ∈ s then 1 else 0) - 1 :=
  (rfl)

/-- The coordinate comparison, in any commutative ring in which `2` is invertible:
`typeBSpinWeight` is obtained from the orthonormal sign weight by pairing with the simple
coroot, that is, by taking an adjacent difference away from the terminal node and doubling the
terminal coordinate. -/
theorem algebraMap_typeBSpinWeight_apply {K : Type*} [CommRing K] [Invertible (2 : K)] {n : ℕ}
    (s : Finset (Fin n)) (i : Fin n) :
    algebraMap ℤ K (typeBSpinWeight s i) =
      if (i : ℕ) + 1 < n then spinWeight K s i - spinWeight K s (Order.succ i)
      else spinWeight K s i + spinWeight K s i := by
  classical
  rw [typeBSpinWeight_apply]
  by_cases hnext : (i : ℕ) + 1 < n
  · rw [ite_eq_left hnext, ite_eq_left hnext]
    by_cases hi : i ∈ s
    · by_cases hsucc : Order.succ i ∈ s
      · rw [ite_eq_left hi, ite_eq_left hsucc, sub_self, map_zero, spinWeight_of_mem hi,
          spinWeight_of_mem hsucc, sub_self]
      · have hneg : spinWeight K s (Order.succ i) = -spinWeight K s i := by
          rw [spinWeight_of_mem hi, spinWeight_of_notMem hsucc]
        rw [ite_eq_left hi, ite_eq_right hsucc, sub_zero, map_one, hneg, sub_neg_eq_add,
          spinWeight_add_self_of_mem hi]
    · by_cases hsucc : Order.succ i ∈ s
      · have hneg : spinWeight K s (Order.succ i) = -spinWeight K s i := by
          rw [spinWeight_of_notMem hi, spinWeight_of_mem hsucc, neg_neg]
        rw [ite_eq_right hi, ite_eq_left hsucc, zero_sub, map_neg, map_one, hneg, sub_neg_eq_add,
          spinWeight_add_self_of_notMem hi]
      · rw [ite_eq_right hi, ite_eq_right hsucc, sub_self, map_zero, spinWeight_of_notMem hi,
          spinWeight_of_notMem hsucc, sub_self]
  · rw [ite_eq_right hnext, ite_eq_right hnext]
    by_cases hi : i ∈ s
    · rw [ite_eq_left hi, spinWeight_add_self_of_mem hi]
      norm_num
    · rw [ite_eq_right hi, spinWeight_add_self_of_notMem hi]
      norm_num

/-- The comparison with half-integer spin weights, as an equality of coordinate vectors. -/
theorem algebraMap_typeBSpinWeight {K : Type*} [CommRing K] [Invertible (2 : K)] {n : ℕ}
    (s : Finset (Fin n)) :
    (fun i : Fin n => algebraMap ℤ K (typeBSpinWeight s i)) =
      fun i : Fin n => if (i : ℕ) + 1 < n then spinWeight K s i - spinWeight K s (Order.succ i)
      else spinWeight K s i + spinWeight K s i := by
  funext i
  exact algebraMap_typeBSpinWeight_apply s i

/-! ## A spanning family -/

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
    typeBSpinWeight (Finset.Iic i) = Pi.single i 1 := by
  classical
  funext j
  rw [typeBSpinWeight_apply, Pi.single_apply]
  simp only [Finset.mem_Iic]
  split_ifs with hjnext hji hjsucc hjlast hji <;> simp_all <;> omega

/-- At a nonterminal node, adding the all-positive weight to the cut sign weight gives the
corresponding coordinate basis vector. -/
private theorem typeBSpinWeight_cut_add_univ_eq_single {n : ℕ} (i : Fin n)
    (hi : (i : ℕ) + 1 < n) :
    typeBSpinWeight (Finset.Iic i) +
        typeBSpinWeight (Finset.univ : Finset (Fin n)) = Pi.single i 1 := by
  classical
  funext j
  have hjlt := j.isLt
  rw [Pi.add_apply, typeBSpinWeight_apply, typeBSpinWeight_univ_apply, Pi.single_apply]
  by_cases hjnext : (j : ℕ) + 1 < n
  · have hjnotlast : ¬(j : ℕ) + 1 = n := by omega
    rw [ite_eq_left hjnext, ite_eq_right hjnotlast]
    have hjnotmax : ¬IsMax j :=
      not_isMax_of_lt (b := (⟨(j : ℕ) + 1, hjnext⟩ : Fin n)) (by simp [Fin.lt_def])
    simp only [Finset.mem_Iic, Order.succ_le_iff_of_not_isMax hjnotmax, Fin.lt_def]
    split_ifs <;> omega
  · have hjlast : (j : ℕ) + 1 = n := by omega
    rw [ite_eq_right hjnext, ite_eq_left hjlast]
    simp only [Finset.mem_Iic]
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
    exact Submodule.subset_span ⟨Finset.Iic i, rfl⟩
  · have hi' : (i : ℕ) + 1 < n := by omega
    rw [← typeBSpinWeight_cut_add_univ_eq_single i hi']
    exact Submodule.add_mem _
      (Submodule.subset_span ⟨Finset.Iic i, rfl⟩)
      (Submodule.subset_span ⟨Finset.univ, rfl⟩)

end TauCeti.DynkinType

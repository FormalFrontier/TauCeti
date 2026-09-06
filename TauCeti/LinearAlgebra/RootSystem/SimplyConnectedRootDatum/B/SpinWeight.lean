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
@[simp]
theorem typeBSpinWeight_apply {n : ℕ} (s : Finset (Fin n)) (i : Fin n) :
    typeBSpinWeight s i =
      if (i : ℕ) + 1 < n then
        (if i ∈ s then 1 else 0) -
          if Order.succ i ∈ s then 1 else 0
      else 2 * (if i ∈ s then 1 else 0) - 1 :=
  (rfl)

/-- Mapping a difference of sign indicators gives the difference of the corresponding
half-integral sign weights. -/
private theorem algebraMap_indicator_sub_eq_spinWeight_sub {K : Type*} [CommRing K]
    [Invertible (2 : K)] {n : ℕ} (s : Finset (Fin n)) (i j : Fin n) :
    algebraMap ℤ K ((if i ∈ s then 1 else 0) - if j ∈ s then 1 else 0) =
      spinWeight K s i - spinWeight K s j := by
  by_cases hi : i ∈ s
  · by_cases hj : j ∈ s
    · simp [hi, hj]
    · simp [hi, hj, sub_neg_eq_add]
  · by_cases hj : j ∈ s
    · simpa [hi, hj, sub_eq_add_neg] using
        (spinWeight_add_self_of_notMem (K := K) hi).symm
    · simp [hi, hj]

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
  · simpa [hnext] using algebraMap_indicator_sub_eq_spinWeight_sub s i (Order.succ i)
  · simp only [ite_eq_right hnext]
    by_cases hi : i ∈ s
    · simp [hi]
    · simp only [ite_eq_right hi, mul_zero, zero_sub, map_neg, map_one]
      exact (spinWeight_add_self_of_notMem (K := K) hi).symm

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

/-- The cut weight has a `1` at the cut, a `-1` at a later terminal node, and zero in every
other coordinate. -/
private theorem typeBSpinWeight_Iic_apply {n : ℕ} (i j : Fin n) :
    typeBSpinWeight (Finset.Iic i) j =
      if j = i then 1 else if (j : ℕ) + 1 = n then -1 else 0 := by
  classical
  rcases lt_trichotomy j i with hji | hji | hij
  · have hjnext : (j : ℕ) + 1 < n := by omega
    have hjnotlast : ¬(j : ℕ) + 1 = n := by omega
    have hjnotmax : ¬IsMax j := not_isMax_of_lt hji
    have hsuccle : Order.succ j ≤ i :=
      (Order.succ_le_iff_of_not_isMax hjnotmax).2 hji
    simp [typeBSpinWeight_apply, hjnext, hjnotlast, Finset.mem_Iic, hji.le, hsuccle, hji.ne]
  · subst j
    by_cases hinext : (i : ℕ) + 1 < n
    · have hinotmax : ¬IsMax i :=
        not_isMax_of_lt (b := (⟨(i : ℕ) + 1, hinext⟩ : Fin n)) (by simp [Fin.lt_def])
      simp [typeBSpinWeight_apply, hinext, Finset.mem_Iic,
        Order.succ_le_iff_of_not_isMax hinotmax]
    · have hilast : (i : ℕ) + 1 = n := by omega
      simp [typeBSpinWeight_apply, hilast]
  · have hjnotle : ¬j ≤ i := not_le_of_gt hij
    have hsuccnotle : ¬Order.succ j ≤ i := fun h ↦ hjnotle (Order.le_succ j |>.trans h)
    by_cases hjnext : (j : ℕ) + 1 < n
    · have hjnotlast : ¬(j : ℕ) + 1 = n := by omega
      simp [typeBSpinWeight_apply, hjnext, hjnotlast, Finset.mem_Iic, hjnotle, hsuccnotle,
        hij.ne']
    · have hjlast : (j : ℕ) + 1 = n := by omega
      simp [typeBSpinWeight_apply, hjlast, Finset.mem_Iic, hjnotle, hij.ne']

/-- At a terminal node, the corresponding cut sign weight is the coordinate basis vector. -/
private theorem typeBSpinWeight_cut_eq_single_of_isLast {n : ℕ} (i : Fin n)
    (hi : (i : ℕ) + 1 = n) :
    typeBSpinWeight (Finset.Iic i) = Pi.single i 1 := by
  classical
  funext j
  rw [typeBSpinWeight_Iic_apply, Pi.single_apply]
  by_cases hji : j = i
  · simp [hji]
  · have hjnotlast : ¬(j : ℕ) + 1 = n := fun hjlast ↦ hji (Fin.ext (by omega))
    simp [hji, hjnotlast]

/-- At a nonterminal node, adding the all-positive weight to the cut sign weight gives the
corresponding coordinate basis vector. -/
private theorem typeBSpinWeight_cut_add_univ_eq_single {n : ℕ} (i : Fin n)
    (hi : (i : ℕ) + 1 < n) :
    typeBSpinWeight (Finset.Iic i) +
        typeBSpinWeight (Finset.univ : Finset (Fin n)) = Pi.single i 1 := by
  classical
  funext j
  rw [Pi.add_apply, typeBSpinWeight_Iic_apply, typeBSpinWeight_univ_apply, Pi.single_apply]
  by_cases hji : j = i
  · subst j
    simp [hi.ne]
  · by_cases hjlast : (j : ℕ) + 1 = n
    · simp [hji, hjlast]
    · simp [hji, hjlast]

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

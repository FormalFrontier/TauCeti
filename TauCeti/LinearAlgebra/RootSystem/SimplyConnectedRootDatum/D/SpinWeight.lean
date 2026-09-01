/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.DiagramPermutations
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

The type-`D` graph automorphism changes the sign of the final orthonormal coordinate. On the
sign-set indexing the spin basis, this toggles membership of the final index. The resulting
permutation exchanges the even and odd half-spin bases and carries each spin weight through the
fork-node permutation `TauCeti.graphPermD`. Thus the full spin module, rather than either
half-spin summand by itself, is the weight-stable input for the graph-twisted carrier.

The spanning result is the full-weight input needed to construct the simply connected type `D`
Chevalley carrier from the spin representation. The adjoint representation supplies only the
index-four root lattice.

## Main declarations

* `TauCeti.DynkinType.typeDSpinWeight`: a spin weight in fundamental-weight coordinates.
* `TauCeti.DynkinType.algebraMap_typeDSpinWeight_apply`: comparison with the half-integer
  orthonormal coordinates of `TauCeti.spinWeight`.
* `TauCeti.DynkinType.span_range_typeDSpinWeight_eq_top`: the spin weights generate the full
  simply connected character lattice.
* `TauCeti.DynkinType.typeDSpinGraphPerm`: the graph symmetry on the spin basis, with
  `TauCeti.DynkinType.typeDSpinWeight_typeDSpinGraphPerm_apply` recording its action on weights.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Section 20.2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Section 13.2.

The integral-coordinate and spanning API follows the parallel type `B` construction in Tau Ceti
PR #4847. The fork coordinate and the use of both half-spin parities are the type `D` changes.

This advances Layer 9, "The Chevalley--Demazure construction", of the ReductiveGroups roadmap:
the explicit simply connected type `D` carrier requires an admissible spin lattice whose weights
generate the full character lattice. Its graph automorphism additionally requires the weight-basis
permutation constructed here; that automorphism is consumed by the `²Dₙ(q)` branch in milestones
L0 and L1 of the CFSGStatement roadmap.
-/

public section

namespace TauCeti.DynkinType

open Set Submodule
open scoped symmDiff

/-! ## Integral spin weights -/

/-- The weight of a type `Dₙ` spinor basis vector in fundamental-weight coordinates.

The finite set `s` records the positive signs. At a nonterminal node the coordinate is the
half-difference of two adjacent signs, hence `1`, `0`, or `-1`. At the terminal fork node it is
the half-sum of the last two signs. -/
def typeDSpinWeight {n : ℕ} (s : Finset (Fin n)) (i : Fin n) : ℤ :=
  if h : (i : ℕ) + 1 < n then
    (if i ∈ s then 1 else 0) -
      if (⟨(i : ℕ) + 1, h⟩ : Fin n) ∈ s then 1 else 0
  else
    (if (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin n) ∈ s then 1 else 0) +
      (if i ∈ s then 1 else 0) - 1

/-- The coordinate formula for a type `D` spin weight. -/
@[simp]
theorem typeDSpinWeight_apply {n : ℕ} (s : Finset (Fin n)) (i : Fin n) :
    typeDSpinWeight s i =
      if h : (i : ℕ) + 1 < n then
        (if i ∈ s then 1 else 0) -
          if (⟨(i : ℕ) + 1, h⟩ : Fin n) ∈ s then 1 else 0
      else
        (if (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin n) ∈ s then 1 else 0) +
          (if i ∈ s then 1 else 0) - 1 :=
  (rfl)

private theorem algebraMap_signIndicator {K : Type*} [CommRing K] [Invertible (2 : K)]
    {n : ℕ} (s : Finset (Fin n)) (i : Fin n) :
    algebraMap ℤ K (if i ∈ s then 1 else 0) = spinWeight K s i + ⅟(2 : K) := by
  classical
  by_cases hi : i ∈ s
  · rw [ite_eq_left hi, map_one, spinWeight_of_mem hi]
    rw [← two_mul, mul_invOf_self]
  · rw [ite_eq_right hi, map_zero, spinWeight_of_notMem hi]
    simp

/-- After mapping to any coefficient ring in which `2` is invertible, `typeDSpinWeight` is obtained
from the orthonormal sign weight by pairing with the simple coroot: take an adjacent difference
away from the terminal node and the sum of the last two coordinates at the terminal fork node. -/
theorem algebraMap_typeDSpinWeight_apply {K : Type*} [CommRing K] [Invertible (2 : K)]
    {n : ℕ} (s : Finset (Fin n)) (i : Fin n) :
    algebraMap ℤ K (typeDSpinWeight s i) =
      if h : (i : ℕ) + 1 < n then
        spinWeight K s i - spinWeight K s (⟨(i : ℕ) + 1, h⟩ : Fin n)
      else spinWeight K s (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin n) +
        spinWeight K s i := by
  classical
  rw [typeDSpinWeight_apply]
  by_cases hnext : (i : ℕ) + 1 < n
  · simp only [dite_eq_left hnext]
    rw [map_sub, algebraMap_signIndicator, algebraMap_signIndicator]
    ring
  · simp only [dite_eq_right hnext]
    rw [map_sub, map_add, map_one, algebraMap_signIndicator, algebraMap_signIndicator]
    ring_nf
    rw [invOf_mul_self]
    ring

/-- The comparison with half-integer spin weights, as an equality of coordinate vectors. -/
theorem algebraMap_typeDSpinWeight {K : Type*} [CommRing K] [Invertible (2 : K)]
    {n : ℕ} (s : Finset (Fin n)) :
    (fun i : Fin n => algebraMap ℤ K (typeDSpinWeight s i)) =
      fun i : Fin n => if h : (i : ℕ) + 1 < n then
        spinWeight K s i - spinWeight K s (⟨(i : ℕ) + 1, h⟩ : Fin n)
      else spinWeight K s (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin n) +
        spinWeight K s i := by
  funext i
  exact algebraMap_typeDSpinWeight_apply s i

/-- For a valid type `Dₙ`, the integral coordinate of a spin weight is its pairing with the
corresponding Bourbaki simple coroot in orthonormal coordinates. Type `D` is simply laced, so the
simple coroot is `typeDSimpleRoot n hn i`. -/
theorem algebraMap_typeDSpinWeight_eq_dotProduct {K : Type*} [CommRing K]
    [Invertible (2 : K)] {n : ℕ} (hn : 4 ≤ n) (s : Finset (Fin n)) (i : Fin n) :
    algebraMap ℤ K (typeDSpinWeight s i) =
      spinWeight K s ⬝ᵥ
        fun j => algebraMap ℤ K (typeDSimpleRoot n hn i j) := by
  rw [algebraMap_typeDSpinWeight_apply]
  by_cases hnext : (i : ℕ) + 1 < n
  · rw [dite_eq_left hnext]
    have hmap :
        (fun j => algebraMap ℤ K (typeDSimpleRoot n hn i j)) =
          (Pi.single i 1 - Pi.single (⟨(i : ℕ) + 1, hnext⟩ : Fin n) 1 :
            Fin n → K) := by
      rw [typeDSimpleRoot_of_add_one_lt hn hnext]
      funext j
      simp [Pi.sub_apply, Pi.single_apply]
    rw [hmap]
    rw [dotProduct_sub, dotProduct_single, dotProduct_single, mul_one, mul_one]
  · have hi : i = (⟨n - 1, by omega⟩ : Fin n) := by
      apply Fin.ext
      dsimp only
      omega
    have hprev : (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin n) =
        (⟨n - 2, by omega⟩ : Fin n) := by
      apply Fin.ext
      dsimp only
      omega
    rw [dite_eq_right hnext]
    have hmap :
        (fun j => algebraMap ℤ K (typeDSimpleRoot n hn i j)) =
          (Pi.single (⟨n - 2, by omega⟩ : Fin n) 1 +
            Pi.single (⟨n - 1, by omega⟩ : Fin n) 1 : Fin n → K) := by
      rw [typeDSimpleRoot_of_not_add_one_lt hn hnext]
      funext j
      simp [Pi.add_apply, Pi.single_apply]
    rw [hmap]
    rw [dotProduct_add, dotProduct_single, dotProduct_single, mul_one, mul_one]
    exact congrArg₂ (· + ·) (congrArg (spinWeight K s) hprev)
      (congrArg (spinWeight K s) hi)

/-! ## The graph automorphism on spin weights -/

/-- The permutation of the type-`D` spin basis induced by the graph automorphism: toggle the sign
of the final orthonormal coordinate. A sign is encoded by membership in the indexing finset, so
this takes the symmetric difference with the singleton containing the final index. -/
def typeDSpinGraphPerm (n : ℕ) (hn : 1 ≤ n) : Equiv.Perm (Finset (Fin n)) :=
  let last : Fin n := ⟨n - 1, by omega⟩
  (symmDiff_left_involutive {last}).toPerm (· ∆ {last})

/-- The type-`D` spin graph permutation acts by symmetric difference with the final index. -/
theorem typeDSpinGraphPerm_apply (n : ℕ) (hn : 1 ≤ n) (s : Finset (Fin n)) :
    typeDSpinGraphPerm n hn s = s ∆ {(⟨n - 1, by omega⟩ : Fin n)} :=
  by simp [typeDSpinGraphPerm]

private theorem symmDiff_singleton_eq_erase_or_insert {α : Type*} [DecidableEq α]
    (s : Finset α) (a : α) :
    s ∆ {a} = if a ∈ s then s.erase a else insert a s := by
  ext x
  by_cases ha : a ∈ s <;> simp [Finset.mem_symmDiff, ha] <;> aesop

/-- An index belongs to the graph-transformed sign set precisely when its old membership agrees
with not being the final index. Thus membership is unchanged away from the final coordinate and
reversed there. -/
@[simp]
theorem mem_typeDSpinGraphPerm_iff (n : ℕ) (hn : 1 ≤ n) (s : Finset (Fin n)) (i : Fin n) :
    i ∈ typeDSpinGraphPerm n hn s ↔ (i ∈ s ↔ (i : ℕ) + 1 ≠ n) := by
  rw [typeDSpinGraphPerm_apply]
  by_cases hi : i = (⟨n - 1, by omega⟩ : Fin n)
  · subst i
    have hval : n - 1 + 1 = n := Nat.sub_add_cancel hn
    simp [Finset.mem_symmDiff, hval]
  · have hilast : (i : ℕ) + 1 ≠ n := by
      intro h
      apply hi
      apply Fin.ext
      dsimp only
      omega
    simp [Finset.mem_symmDiff, hi, hilast]

/-- Toggling the final sign twice is the identity. -/
@[simp]
theorem typeDSpinGraphPerm_apply_apply (n : ℕ) (hn : 1 ≤ n) (s : Finset (Fin n)) :
    typeDSpinGraphPerm n hn (typeDSpinGraphPerm n hn s) = s :=
  (typeDSpinGraphPerm n hn).left_inv s

/-- The permutation which toggles the final sign is an involution. -/
@[simp]
theorem typeDSpinGraphPerm_symm (n : ℕ) (hn : 1 ≤ n) :
    (typeDSpinGraphPerm n hn).symm = typeDSpinGraphPerm n hn :=
  by
    apply Equiv.ext
    intro s
    apply (typeDSpinGraphPerm n hn).injective
    rw [Equiv.apply_symm_apply, typeDSpinGraphPerm_apply_apply]

/-- The graph permutation exchanges the two half-spin parities: an even sign set is sent to an
odd one and conversely. -/
@[simp]
theorem even_card_typeDSpinGraphPerm_iff (n : ℕ) (hn : 1 ≤ n)
    (s : Finset (Fin n)) :
    Even (typeDSpinGraphPerm n hn s).card ↔ Odd s.card := by
  let last : Fin n := ⟨n - 1, by omega⟩
  by_cases hlast : last ∈ s
  · have hcard : (typeDSpinGraphPerm n hn s).card + 1 = s.card := by
      rw [typeDSpinGraphPerm_apply, symmDiff_singleton_eq_erase_or_insert, ite_eq_left hlast]
      simpa only [last]
        using Finset.card_erase_add_one hlast
    rw [← hcard, Nat.odd_add_one, Nat.not_odd_iff_even]
  · have hcard : (typeDSpinGraphPerm n hn s).card = s.card + 1 := by
      rw [typeDSpinGraphPerm_apply, symmDiff_singleton_eq_erase_or_insert, ite_eq_right hlast]
      simpa only [last]
        using Finset.card_insert_of_notMem hlast
    rw [hcard, Nat.even_add_one, Nat.not_even_iff_odd]

/-- Equivalently, the graph permutation sends odd sign sets to even ones. -/
@[simp]
theorem odd_card_typeDSpinGraphPerm_iff (n : ℕ) (hn : 1 ≤ n)
    (s : Finset (Fin n)) :
    Odd (typeDSpinGraphPerm n hn s).card ↔ Even s.card := by
  rw [← Nat.not_even_iff_odd, even_card_typeDSpinGraphPerm_iff,
    Nat.not_odd_iff_even]

/-- Toggling the final sign exchanges the two fork coordinates of a type-`D` spin weight. -/
private theorem typeDSpinWeight_typeDSpinGraphPerm_fork {n : ℕ} (hn : 2 ≤ n)
    (s : Finset (Fin n)) :
    typeDSpinWeight (typeDSpinGraphPerm n (by omega) s) ⟨n - 2, by omega⟩ =
        typeDSpinWeight s ⟨n - 1, by omega⟩ ∧
      typeDSpinWeight (typeDSpinGraphPerm n (by omega) s) ⟨n - 1, by omega⟩ =
        typeDSpinWeight s ⟨n - 2, by omega⟩ := by
  have hpen_lt : n - 2 + 1 < n := by omega
  have hlast_not_lt : ¬n - 1 + 1 < n := by omega
  have hnext :
      (⟨n - 2 + 1, hpen_lt⟩ : Fin n) = (⟨n - 1, by omega⟩ : Fin n) := by
    apply Fin.ext
    dsimp only
    omega
  have hprev :
      (⟨n - 1 - 1, by omega⟩ : Fin n) = (⟨n - 2, by omega⟩ : Fin n) := by
    apply Fin.ext
    dsimp only
    omega
  have hpen_not_last : n - 2 + 1 ≠ n := by omega
  have hlast_is_last : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  constructor
  · rw [typeDSpinWeight_apply, dite_eq_left hpen_lt, hnext,
      typeDSpinWeight_apply, dite_eq_right hlast_not_lt, hprev]
    by_cases hp : (⟨n - 2, by omega⟩ : Fin n) ∈ s <;>
      by_cases hl : (⟨n - 1, by omega⟩ : Fin n) ∈ s <;>
      simp [mem_typeDSpinGraphPerm_iff, hpen_not_last, hlast_is_last, hp, hl]
  · rw [typeDSpinWeight_apply, dite_eq_right hlast_not_lt, hprev,
      typeDSpinWeight_apply, dite_eq_left hpen_lt, hnext]
    by_cases hp : (⟨n - 2, by omega⟩ : Fin n) ∈ s <;>
      by_cases hl : (⟨n - 1, by omega⟩ : Fin n) ∈ s <;>
      simp [mem_typeDSpinGraphPerm_iff, hpen_not_last, hlast_is_last, hp, hl]

/-- **The final-sign toggle realizes the type-`D` graph automorphism on spin weights.** Applying
the fork-node permutation to the fundamental-weight coordinates of a spin weight gives the weight
indexed by the sign set with its final membership toggled. -/
theorem typeDSpinWeight_typeDSpinGraphPerm_apply {n : ℕ} (hn : 2 ≤ n)
    (s : Finset (Fin n)) (i : Fin n) :
    typeDSpinWeight (typeDSpinGraphPerm n (by omega) s) i =
      typeDSpinWeight s (graphPermD n hn i) := by
  by_cases hbefore : (i : ℕ) + 2 < n
  · have hnext : (i : ℕ) + 1 < n := by omega
    have hilast : (i : ℕ) ≠ n - 1 := by omega
    have hipenultimate : (i : ℕ) ≠ n - 2 := by omega
    rw [graphPermD_apply_of_ne_of_ne n hn i hipenultimate hilast,
      typeDSpinWeight_apply, typeDSpinWeight_apply, dite_eq_left hnext,
      dite_eq_left hnext]
    have hi_not_last : (i : ℕ) + 1 ≠ n := by omega
    have hnext_not_last :
        ((⟨(i : ℕ) + 1, hnext⟩ : Fin n) : ℕ) + 1 ≠ n := by
      dsimp only
      omega
    simp [mem_typeDSpinGraphPerm_iff, hi_not_last, hnext_not_last]
  · by_cases hpenultimate : (i : ℕ) + 2 = n
    · have hi : i = (⟨n - 2, by omega⟩ : Fin n) := by
        apply Fin.ext
        dsimp only
        omega
      rw [hi, graphPermD_apply_left]
      exact (typeDSpinWeight_typeDSpinGraphPerm_fork hn s).1
    · have hlast : (i : ℕ) + 1 = n := by omega
      have hi : i = (⟨n - 1, by omega⟩ : Fin n) := by
        apply Fin.ext
        dsimp only
        omega
      rw [hi, graphPermD_apply_right]
      exact (typeDSpinWeight_typeDSpinGraphPerm_fork hn s).2

/-- The type-`D` graph permutation preserves the full family of spin weights as a set. -/
theorem image_comp_graphPermD_range_typeDSpinWeight {n : ℕ} (hn : 2 ≤ n) :
    (fun wt : Fin n → ℤ => wt ∘ graphPermD n hn) ''
        Set.range (typeDSpinWeight (n := n)) =
      Set.range (typeDSpinWeight (n := n)) := by
  rw [← Set.range_comp]
  have hcomp :
      (fun wt : Fin n → ℤ => wt ∘ graphPermD n hn) ∘ typeDSpinWeight =
        typeDSpinWeight ∘ typeDSpinGraphPerm n (by omega) := by
    funext s i
    exact (typeDSpinWeight_typeDSpinGraphPerm_apply hn s i).symm
  rw [hcomp, Set.range_comp, EquivLike.range_eq_univ, Set.image_univ]

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
    rw [dite_eq_left hnext, ite_eq_right hne]
    simp
  · have heq : (i : ℕ) + 1 = n := by omega
    rw [dite_eq_right hnext, ite_eq_left heq]
    simp

private theorem typeDSpinWeight_cut_apply {n : ℕ} (i j : Fin n) :
    typeDSpinWeight (typeDSpinCut i) j =
      if j = i then 1
      else if (j : ℕ) + 1 = n ∧ (i : ℕ) + 2 < n then -1 else 0 := by
  rw [typeDSpinWeight_apply]
  simp only [mem_typeDSpinCut_iff]
  by_cases hjnext : (j : ℕ) + 1 < n
  · rw [dite_eq_left hjnext]
    simp only [Fin.le_def]
    split_ifs <;> omega
  · rw [dite_eq_right hjnext]
    simp only [Fin.le_def]
    split_ifs <;> omega

/-- At the terminal node, the cut sign weight is the terminal coordinate basis vector. -/
private theorem typeDSpinWeight_cut_eq_single_of_isLast {n : ℕ} (i : Fin n)
    (hi : (i : ℕ) + 1 = n) :
    typeDSpinWeight (typeDSpinCut i) = Pi.single i 1 := by
  classical
  funext j
  rw [typeDSpinWeight_cut_apply, Pi.single_apply]
  split_ifs <;> omega

/-- At the penultimate node, the cut sign weight is the penultimate coordinate basis vector. -/
private theorem typeDSpinWeight_cut_eq_single_of_isPenultimate {n : ℕ} (i : Fin n)
    (hi : (i : ℕ) + 2 = n) :
    typeDSpinWeight (typeDSpinCut i) = Pi.single i 1 := by
  classical
  funext j
  rw [typeDSpinWeight_cut_apply, Pi.single_apply]
  split_ifs <;> omega

/-- Before the two fork nodes, adding the all-positive weight to the cut sign weight gives the
corresponding coordinate basis vector. -/
private theorem typeDSpinWeight_cut_add_univ_eq_single {n : ℕ} (i : Fin n)
    (hi : (i : ℕ) + 2 < n) :
    typeDSpinWeight (typeDSpinCut i) +
        typeDSpinWeight (Finset.univ : Finset (Fin n)) = Pi.single i 1 := by
  classical
  funext j
  rw [Pi.add_apply, typeDSpinWeight_cut_apply, typeDSpinWeight_univ_apply, Pi.single_apply]
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

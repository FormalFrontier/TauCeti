/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.DynkinType

public section

/-!
# A base has at most one valid Dynkin type

`TauCeti.HasCartanType P b t` says that the Cartan matrix of a base `b` becomes the standard Cartan
matrix of the Dynkin type `t` after one simultaneous relabelling of its rows and columns. This file
proves that a base has **at most one valid** Cartan type: two valid Dynkin types whose standard
Cartan matrices are related by such a relabelling are equal. It is the uniqueness half of the
Cartan-Killing classification, and it needs no root system at all, only the standard matrices.

Validity is not a convenience here but the content of the statement. Outside the valid ranges the
standard matrices genuinely repeat: `B 1` and `C 1` are `A 1`, `D 3` is `A 3` after a relabelling
(`CartanMatrix.D_three'`), and `C 2` is `B 2` with its two nodes exchanged. Uniqueness therefore has
to fail without `TauCeti.DynkinType.Valid`, and every use of validity below is at one of those
coincidences.

## The invariants

A relabelling preserves the size of a matrix, and it preserves any property phrased in terms of
entries and row sums alone. Four such properties separate the nine valid families, and computing
their values on the standard matrices is the arithmetic content of the file.

For a simply-laced type the row sum `∑ j, A i j` is `2` minus the degree of the node `i`, so the
value `-1` marks a node of degree three, a branch node, and the value `1` marks a node of degree
one, a leaf. That reading is what the names below record, but no graph is ever formed: the row sum
is used as it stands, which is also why the same invariant is legitimate for the multiply-laced
types, where the degree reading fails (`F₄` has a row summing to `-1` and no branch node).

* a **multiple edge**, an off-diagonal entry `≤ -2`: this holds for exactly the non-simply-laced
  valid types `B`, `C`, `F₄`, `G₂`;
* a **double edge at a leaf**, a node whose row sums to `1` and whose column contains an entry
  `-2`: this holds for exactly `B`, and is what separates `Bₙ` from its transpose `Cₙ` and from
  `F₄`, whose double edge is interior;
* a **row summing to `-1`**: this holds for `D`, `E₆`, `E₇`, `E₈`, `F₄`, `G₂`, and fails for `A`
  and `C`;
* a **branch node with two leaves**, a row summing to `-1` with at least two nonzero entries in
  columns summing to `1`: this holds for `Dₙ` and fails for `E₆`, `E₇`, `E₈`, which is the one
  separation the rank does not already make.

## Main results

* `TauCeti.DynkinType.eq_of_valid_of_cartanMatrix_eq`: two valid Dynkin types whose standard Cartan
  matrices agree up to a simultaneous relabelling are equal.
* `TauCeti.DynkinType.eq_of_valid_of_forall_eq`: the same statement for a matrix carrying two such
  relabellings, which is the form the classification theorems consume.
* `TauCeti.HasCartanType.eq_of_valid`: a base has at most one valid Cartan type.
* `TauCeti.HasCartanType.existsUnique_of_valid`: a base of some valid Cartan type has exactly one.

## References

This is the uniqueness half of `existsUnique_dynkinType`, the classification target of Layer 5 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`; the existence half, which produces a
valid type in the first place, is independent of it. The coincidences outside the valid ranges are
those of Bourbaki, *Lie Groups and Lie Algebras, Chapters 4-6*, Ch. VI, §4.
-/

namespace TauCeti

namespace DynkinType

section MultipleEdge

variable {α β : Type*} {A : Matrix α α ℤ} {A' : Matrix β β ℤ}

/-- The diagram of `A` has a multiple edge: some off-diagonal entry is at most `-2`. -/
private abbrev HasMultipleEdge (A : Matrix α α ℤ) : Prop := ∃ i j, i ≠ j ∧ A i j ≤ -2

private lemma hasMultipleEdge_congr (e : α ≃ β) (he : ∀ i j, A i j = A' (e i) (e j)) :
    HasMultipleEdge A ↔ HasMultipleEdge A' := by
  refine ⟨fun ⟨i, j, hij, h⟩ ↦ ⟨e i, e j, e.injective.ne hij, by rwa [← he]⟩,
    fun ⟨i, j, hij, h⟩ ↦ ⟨e.symm i, e.symm j, e.symm.injective.ne hij, ?_⟩⟩
  rw [he, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact h

/-- A generalized Cartan matrix has a multiple edge exactly when it is not simply laced: its
off-diagonal entries are nonpositive, so failing to be `0` or `-1` means being at most `-2`. -/
private lemma hasMultipleEdge_iff_not_isSimplyLaced (hle : ∀ i j, i ≠ j → A i j ≤ 0) :
    HasMultipleEdge A ↔ ¬ A.IsSimplyLaced := by
  refine ⟨fun ⟨i, j, hij, h⟩ hsl ↦ ?_, fun h ↦ ?_⟩
  · rcases hsl hij with h' | h' <;> omega
  · by_contra hc
    refine h fun i j hij ↦ ?_
    have h1 : A i j ≤ 0 := hle i j hij
    have h2 : ¬ A i j ≤ -2 := fun hh ↦ hc ⟨i, j, hij, hh⟩
    omega

end MultipleEdge

section Invariants

variable {α β : Type*} [Fintype α] [Fintype β] {A : Matrix α α ℤ} {A' : Matrix β β ℤ}

/-- The sum of the entries of row `i`. For a simply-laced Cartan matrix this is `2` minus the degree
of the node `i` in the diagram. -/
private abbrev rowSum (A : Matrix α α ℤ) (i : α) : ℤ := ∑ j, A i j

/-- Some node of `A` has a row summing to `1` and a column containing an entry `-2`: the diagram has
a double edge one of whose ends is a leaf. -/
private abbrev HasLeafDoubleEdge (A : Matrix α α ℤ) : Prop :=
  ∃ j, rowSum A j = 1 ∧ ({i ∈ (Finset.univ : Finset α) | A i j = -2}).Nonempty

/-- Some row of `A` sums to `-1`. For a simply-laced Cartan matrix this says that the diagram has a
node of degree three. -/
private abbrev HasRowSumNegOne (A : Matrix α α ℤ) : Prop := ∃ i, rowSum A i = -1

/-- Some row of `A` sums to `-1` and has at least two nonzero entries in columns that sum to `1`.
For a simply-laced Cartan matrix this says that the diagram has a node of degree three at least two
of whose neighbours are leaves. -/
private abbrev HasBranchWithTwoLeaves (A : Matrix α α ℤ) : Prop :=
  ∃ i, rowSum A i = -1 ∧ 2 ≤ ({j ∈ (Finset.univ : Finset α) | A i j ≠ 0 ∧ rowSum A j = 1}).card

/-- Row sums are unchanged by a simultaneous relabelling of rows and columns. -/
private lemma rowSum_congr (e : α ≃ β) (he : ∀ i j, A i j = A' (e i) (e j)) (i : α) :
    rowSum A i = rowSum A' (e i) :=
  calc rowSum A i = ∑ j, A' (e i) (e j) := Finset.sum_congr rfl fun j _ ↦ he i j
    _ = rowSum A' (e i) := e.sum_comp fun j ↦ A' (e i) j

private lemma hasRowSumNegOne_congr (e : α ≃ β) (he : ∀ i j, A i j = A' (e i) (e j)) :
    HasRowSumNegOne A ↔ HasRowSumNegOne A' := by
  refine ⟨fun ⟨i, h⟩ ↦ ⟨e i, by rwa [← rowSum_congr e he]⟩, fun ⟨i, h⟩ ↦ ⟨e.symm i, ?_⟩⟩
  rw [rowSum_congr e he, Equiv.apply_symm_apply]
  exact h

private lemma hasLeafDoubleEdge_congr (e : α ≃ β) (he : ∀ i j, A i j = A' (e i) (e j)) :
    HasLeafDoubleEdge A ↔ HasLeafDoubleEdge A' := by
  have key : ∀ j : α, ({i ∈ (Finset.univ : Finset α) | A i j = -2}).Nonempty ↔
      ({i ∈ (Finset.univ : Finset β) | A' i (e j) = -2}).Nonempty := by
    intro j
    simp only [Finset.filter_nonempty_iff, Finset.mem_univ, true_and]
    exact ⟨fun ⟨i, h⟩ ↦ ⟨e i, by rwa [← he]⟩,
      fun ⟨i, h⟩ ↦ ⟨e.symm i, by rw [he, Equiv.apply_symm_apply]; exact h⟩⟩
  refine ⟨fun ⟨j, h1, h2⟩ ↦ ⟨e j, by rwa [← rowSum_congr e he], (key j).mp h2⟩,
    fun ⟨j, h1, h2⟩ ↦ ⟨e.symm j, ?_, ?_⟩⟩
  · rw [rowSum_congr e he, Equiv.apply_symm_apply]
    exact h1
  · rw [key (e.symm j), Equiv.apply_symm_apply]
    exact h2

private lemma hasBranchWithTwoLeaves_congr (e : α ≃ β) (he : ∀ i j, A i j = A' (e i) (e j)) :
    HasBranchWithTwoLeaves A ↔ HasBranchWithTwoLeaves A' := by
  have key : ∀ i : α, ({j ∈ (Finset.univ : Finset β) | A' (e i) j ≠ 0 ∧ rowSum A' j = 1})
      = ({j ∈ (Finset.univ : Finset α) | A i j ≠ 0 ∧ rowSum A j = 1}).map e.toEmbedding := by
    intro i
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Equiv.coe_toEmbedding]
    refine ⟨fun ⟨h1, h2⟩ ↦ ⟨e.symm j, ⟨?_, ?_⟩, e.apply_symm_apply j⟩, ?_⟩
    · rw [he, Equiv.apply_symm_apply]
      exact h1
    · rw [rowSum_congr e he, Equiv.apply_symm_apply]
      exact h2
    · rintro ⟨j, ⟨h1, h2⟩, rfl⟩
      exact ⟨by rwa [← he], by rwa [← rowSum_congr e he]⟩
  refine ⟨fun ⟨i, h1, h2⟩ ↦ ⟨e i, by rwa [← rowSum_congr e he], ?_⟩,
    fun ⟨i, h1, h2⟩ ↦ ⟨e.symm i, ?_, ?_⟩⟩
  · rwa [key i, Finset.card_map]
  · rw [rowSum_congr e he, Equiv.apply_symm_apply]
    exact h1
  · rw [← Finset.card_map e.toEmbedding, ← key (e.symm i), Equiv.apply_symm_apply]
    exact h2

end Invariants

section Values

/-! ### The invariants of the standard Cartan matrices

The classical families need their row sums computed by hand. Each row of a classical Cartan matrix
has at most four nonzero entries, so the row is rewritten as a sum of that many indicator functions
of a column index and summed term by term. The exceptional matrices are finite data, so `decide`
reads their invariants off directly. -/

/-- One indicator function of a column index, summed over the columns. -/
private lemma sum_range_ite (n c : ℕ) (v : ℤ) :
    ∑ j ∈ Finset.range n, (if j = c then v else 0) = if c < n then v else 0 := by
  rw [Finset.sum_ite_eq' (Finset.range n) c fun _ ↦ v]
  simp only [Finset.mem_range]

/-- The row sums of a type `A` Cartan matrix: `2` less one for each neighbour of the node. -/
private lemma rowSum_cartanMatrix_A {n m : ℕ} (hm : m < n) :
    rowSum (CartanMatrix.A n) ⟨m, hm⟩
      = (if m = 0 then 0 else -1) + 2 + (if m + 1 < n then -1 else 0) := by
  have key : ∀ j : Fin n, CartanMatrix.A n ⟨m, hm⟩ j
      = (if (j : ℕ) = m - 1 then (if m = 0 then (0 : ℤ) else -1) else 0)
        + (if (j : ℕ) = m then 2 else 0) + (if (j : ℕ) = m + 1 then -1 else 0) := by
    intro j
    have := j.isLt
    simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> omega
  calc rowSum (CartanMatrix.A n) ⟨m, hm⟩
      = ∑ j ∈ Finset.range n, ((if j = m - 1 then (if m = 0 then (0 : ℤ) else -1) else 0)
          + (if j = m then 2 else 0) + (if j = m + 1 then -1 else 0)) := by
        rw [← Fin.sum_univ_eq_sum_range (fun j ↦
          (if j = m - 1 then (if m = 0 then (0 : ℤ) else -1) else 0)
            + (if j = m then 2 else 0) + (if j = m + 1 then -1 else 0)) n]
        exact Finset.sum_congr rfl fun j _ ↦ key j
    _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_range_ite, sum_range_ite,
          sum_range_ite]
        split_ifs <;> omega

/-- The row sums of a type `C` Cartan matrix. The last node contributes `2 - 2` because the double
edge points away from it, which is what makes every row sum nonnegative. -/
private lemma rowSum_cartanMatrix_C {n m : ℕ} (hm : m < n) :
    rowSum (CartanMatrix.C n) ⟨m, hm⟩
      = (if m = 0 then 0 else if m = n - 1 then -2 else -1) + 2
        + (if m + 1 < n then -1 else 0) := by
  have key : ∀ j : Fin n, CartanMatrix.C n ⟨m, hm⟩ j
      = (if (j : ℕ) = m - 1 then
          (if m = 0 then (0 : ℤ) else if m = n - 1 then -2 else -1) else 0)
        + (if (j : ℕ) = m then 2 else 0) + (if (j : ℕ) = m + 1 then -1 else 0) := by
    intro j
    have := j.isLt
    simp only [CartanMatrix.C, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> omega
  calc rowSum (CartanMatrix.C n) ⟨m, hm⟩
      = ∑ j ∈ Finset.range n, ((if j = m - 1 then
            (if m = 0 then (0 : ℤ) else if m = n - 1 then -2 else -1) else 0)
          + (if j = m then 2 else 0) + (if j = m + 1 then -1 else 0)) := by
        rw [← Fin.sum_univ_eq_sum_range (fun j ↦
          (if j = m - 1 then
              (if m = 0 then (0 : ℤ) else if m = n - 1 then -2 else -1) else 0)
            + (if j = m then 2 else 0) + (if j = m + 1 then -1 else 0)) n]
        exact Finset.sum_congr rfl fun j _ ↦ key j
    _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_range_ite, sum_range_ite,
          sum_range_ite]
        split_ifs <;> omega

/-- The last node of a type `B` diagram is a leaf: it meets only the double edge. -/
private lemma rowSum_cartanMatrix_B_last {n : ℕ} (hn : 2 ≤ n) :
    rowSum (CartanMatrix.B n) ⟨n - 1, by omega⟩ = 1 := by
  have key : ∀ j : Fin n, CartanMatrix.B n ⟨n - 1, by omega⟩ j
      = (if (j : ℕ) = n - 2 then (-1 : ℤ) else 0) + (if (j : ℕ) = n - 1 then 2 else 0) := by
    intro j
    have := j.isLt
    simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> omega
  calc rowSum (CartanMatrix.B n) ⟨n - 1, by omega⟩
      = ∑ j ∈ Finset.range n,
          ((if j = n - 2 then (-1 : ℤ) else 0) + (if j = n - 1 then 2 else 0)) := by
        rw [← Fin.sum_univ_eq_sum_range
          (fun j ↦ (if j = n - 2 then (-1 : ℤ) else 0) + (if j = n - 1 then 2 else 0)) n]
        exact Finset.sum_congr rfl fun j _ ↦ key j
    _ = 1 := by
        rw [Finset.sum_add_distrib, sum_range_ite, sum_range_ite]
        split_ifs <;> omega

/-- The branch node of a type `D` diagram, at Bourbaki index `n - 3`, has three neighbours. -/
private lemma rowSum_cartanMatrix_D_branch {n : ℕ} (hn : 4 ≤ n) :
    rowSum (CartanMatrix.D n) ⟨n - 3, by omega⟩ = -1 := by
  have key : ∀ j : Fin n, CartanMatrix.D n ⟨n - 3, by omega⟩ j
      = (if (j : ℕ) = n - 4 then (-1 : ℤ) else 0) + (if (j : ℕ) = n - 3 then 2 else 0)
        + (if (j : ℕ) = n - 2 then -1 else 0) + (if (j : ℕ) = n - 1 then -1 else 0) := by
    intro j
    have := j.isLt
    simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> omega
  calc rowSum (CartanMatrix.D n) ⟨n - 3, by omega⟩
      = ∑ j ∈ Finset.range n, ((if j = n - 4 then (-1 : ℤ) else 0)
          + (if j = n - 3 then 2 else 0) + (if j = n - 2 then -1 else 0)
          + (if j = n - 1 then -1 else 0)) := by
        rw [← Fin.sum_univ_eq_sum_range (fun j ↦ (if j = n - 4 then (-1 : ℤ) else 0)
          + (if j = n - 3 then 2 else 0) + (if j = n - 2 then -1 else 0)
          + (if j = n - 1 then -1 else 0)) n]
        exact Finset.sum_congr rfl fun j _ ↦ key j
    _ = -1 := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
          sum_range_ite, sum_range_ite, sum_range_ite, sum_range_ite]
        split_ifs <;> omega

/-- The two nodes of the fork of a type `D` diagram, at Bourbaki indices `n - 2` and `n - 1`, are
leaves: each meets only the branch node. -/
private lemma rowSum_cartanMatrix_D_fork {n m : ℕ} (hn : 4 ≤ n) (hm : n - 2 ≤ m) (hmn : m < n) :
    rowSum (CartanMatrix.D n) ⟨m, hmn⟩ = 1 := by
  have key : ∀ j : Fin n, CartanMatrix.D n ⟨m, hmn⟩ j
      = (if (j : ℕ) = n - 3 then (-1 : ℤ) else 0) + (if (j : ℕ) = m then 2 else 0) := by
    intro j
    have := j.isLt
    simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> omega
  calc rowSum (CartanMatrix.D n) ⟨m, hmn⟩
      = ∑ j ∈ Finset.range n,
          ((if j = n - 3 then (-1 : ℤ) else 0) + (if j = m then 2 else 0)) := by
        rw [← Fin.sum_univ_eq_sum_range
          (fun j ↦ (if j = n - 3 then (-1 : ℤ) else 0) + (if j = m then 2 else 0)) n]
        exact Finset.sum_congr rfl fun j _ ↦ key j
    _ = 1 := by
        rw [Finset.sum_add_distrib, sum_range_ite, sum_range_ite]
        split_ifs <;> omega

private lemma not_hasRowSumNegOne_A (n : ℕ) : ¬ HasRowSumNegOne (A n).cartanMatrix := by
  rintro ⟨i, hi⟩
  rw [cartanMatrix_A] at hi
  have hin : (i : ℕ) < n := i.isLt
  have h : (if (i : ℕ) = 0 then (0 : ℤ) else -1) + 2 + (if (i : ℕ) + 1 < n then -1 else 0) = -1 :=
    (rowSum_cartanMatrix_A hin).symm.trans hi
  split_ifs at h <;> omega

private lemma not_hasRowSumNegOne_C (n : ℕ) : ¬ HasRowSumNegOne (C n).cartanMatrix := by
  rintro ⟨i, hi⟩
  rw [cartanMatrix_C] at hi
  have hin : (i : ℕ) < n := i.isLt
  have h : (if (i : ℕ) = 0 then (0 : ℤ) else if (i : ℕ) = n - 1 then -2 else -1) + 2
      + (if (i : ℕ) + 1 < n then -1 else 0) = -1 :=
    (rowSum_cartanMatrix_C hin).symm.trans hi
  split_ifs at h <;> omega

private lemma not_hasLeafDoubleEdge_C {n : ℕ} (hn : 3 ≤ n) :
    ¬ HasLeafDoubleEdge (C n).cartanMatrix := by
  rintro ⟨j, hj, i, hi⟩
  rw [Finset.mem_filter, cartanMatrix_C] at hi
  obtain ⟨-, hi⟩ := hi
  have hin : (i : ℕ) < n := i.isLt
  have hjn : (j : ℕ) < n := j.isLt
  rw [cartanMatrix_C] at hj
  -- The only `-2` of a type `C` matrix is in the last row, so its column is the node `n - 2`.
  have hjval : (j : ℕ) = n - 2 := by
    have hi' : CartanMatrix.C n ⟨(i : ℕ), hin⟩ ⟨(j : ℕ), hjn⟩ = -2 := hi
    simp only [CartanMatrix.C, Matrix.of_apply, Fin.ext_iff] at hi'
    split_ifs at hi' <;> omega
  have h : (if (j : ℕ) = 0 then (0 : ℤ) else if (j : ℕ) = n - 1 then -2 else -1) + 2
      + (if (j : ℕ) + 1 < n then -1 else 0) = 1 :=
    (rowSum_cartanMatrix_C hjn).symm.trans hj
  split_ifs at h <;> omega

/-- The double edge of a type `B` diagram runs from the node `n - 2` to the last node. -/
private lemma cartanMatrix_B_apply_last {n : ℕ} (hn : 2 ≤ n) :
    CartanMatrix.B n ⟨n - 2, by omega⟩ ⟨n - 1, by omega⟩ = -2 := by
  simp only [CartanMatrix.B, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

/-- The two edges of the fork of a type `D` diagram leave its branch node `n - 3`. -/
private lemma cartanMatrix_D_apply_fork {n m : ℕ} (hn : 4 ≤ n) (hm : n - 2 ≤ m) (hmn : m < n) :
    CartanMatrix.D n ⟨n - 3, by omega⟩ ⟨m, hmn⟩ = -1 := by
  simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

private lemma hasLeafDoubleEdge_B {n : ℕ} (hn : 2 ≤ n) : HasLeafDoubleEdge (B n).cartanMatrix := by
  refine ⟨⟨n - 1, by rw [rank_B]; omega⟩, ?_, ⟨⟨n - 2, by rw [rank_B]; omega⟩, ?_⟩⟩
  · rw [cartanMatrix_B]
    exact rowSum_cartanMatrix_B_last hn
  · rw [Finset.mem_filter, cartanMatrix_B]
    exact ⟨Finset.mem_univ _, cartanMatrix_B_apply_last hn⟩

private lemma hasRowSumNegOne_D {n : ℕ} (hn : 4 ≤ n) : HasRowSumNegOne (D n).cartanMatrix :=
  ⟨⟨n - 3, by rw [rank_D]; omega⟩, by rw [cartanMatrix_D]; exact rowSum_cartanMatrix_D_branch hn⟩

private lemma hasBranchWithTwoLeaves_D {n : ℕ} (hn : 4 ≤ n) :
    HasBranchWithTwoLeaves (D n).cartanMatrix := by
  suffices h : HasBranchWithTwoLeaves (CartanMatrix.D n) by rwa [← cartanMatrix_D] at h
  refine ⟨⟨n - 3, by omega⟩, rowSum_cartanMatrix_D_branch hn, ?_⟩
  -- The two nodes of the fork are two leaves adjacent to the branch node.
  have hsub : ({⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩} : Finset (Fin n)) ⊆
      {j ∈ (Finset.univ : Finset (Fin n)) |
        CartanMatrix.D n ⟨n - 3, by omega⟩ j ≠ 0 ∧ rowSum (CartanMatrix.D n) j = 1} := by
    intro j hj
    rw [Finset.mem_insert, Finset.mem_singleton] at hj
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
    · rcases hj with rfl | rfl
      · rw [cartanMatrix_D_apply_fork hn le_rfl (by omega)]
        norm_num
      · rw [cartanMatrix_D_apply_fork hn (by omega) (by omega)]
        norm_num
    · rcases hj with rfl | rfl
      · exact rowSum_cartanMatrix_D_fork hn le_rfl (by omega)
      · exact rowSum_cartanMatrix_D_fork hn (by omega) (by omega)
  calc (2 : ℕ) = ({⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩} : Finset (Fin n)).card := by
        rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_singleton, Fin.ext_iff]; omega),
          Finset.card_singleton]
    _ ≤ _ := Finset.card_le_card hsub

private lemma hasRowSumNegOne_E6 : HasRowSumNegOne CartanMatrix.E₆ := by decide
private lemma hasRowSumNegOne_E7 : HasRowSumNegOne CartanMatrix.E₇ := by decide
private lemma hasRowSumNegOne_E8 : HasRowSumNegOne CartanMatrix.E₈ := by decide
private lemma hasRowSumNegOne_F4 : HasRowSumNegOne CartanMatrix.F₄ := by decide
private lemma hasRowSumNegOne_G2 : HasRowSumNegOne CartanMatrix.G₂.transpose := by decide

private lemma not_hasBranchWithTwoLeaves_E6 : ¬ HasBranchWithTwoLeaves CartanMatrix.E₆ := by decide
private lemma not_hasBranchWithTwoLeaves_E7 : ¬ HasBranchWithTwoLeaves CartanMatrix.E₇ := by decide
private lemma not_hasBranchWithTwoLeaves_E8 : ¬ HasBranchWithTwoLeaves CartanMatrix.E₈ := by decide

private lemma not_hasLeafDoubleEdge_F4 : ¬ HasLeafDoubleEdge CartanMatrix.F₄ := by decide
private lemma not_hasLeafDoubleEdge_G2 :
    ¬ HasLeafDoubleEdge CartanMatrix.G₂.transpose := by decide

end Values

section Identification

variable {t : DynkinType}

/-- A valid Dynkin type has a multiple edge exactly when it is not simply laced. -/
private lemma hasMultipleEdge_cartanMatrix_iff_of_valid (ht : t.Valid) :
    HasMultipleEdge t.cartanMatrix ↔ ¬ t.IsSimplyLaced := by
  rw [hasMultipleEdge_iff_not_isSimplyLaced fun i j hij ↦ cartanMatrix_apply_le_zero_of_ne t hij,
    isSimplyLaced_cartanMatrix_iff_of_valid ht]

/-- A valid simply-laced type with no row summing to `-1` is a chain: it is of type `A`. -/
private lemma eq_A_of_valid (ht : t.Valid) (hs : t.IsSimplyLaced)
    (hr : ¬ HasRowSumNegOne t.cartanMatrix) : t = A t.rank := by
  cases t with
  | A n => rfl
  | B n => exact absurd hs (not_isSimplyLaced_B n)
  | C n => exact absurd hs (not_isSimplyLaced_C n)
  | D n => exact absurd (hasRowSumNegOne_D (valid_D.mp ht)) hr
  | E6 => exact absurd (cartanMatrix_E6 ▸ hasRowSumNegOne_E6) hr
  | E7 => exact absurd (cartanMatrix_E7 ▸ hasRowSumNegOne_E7) hr
  | E8 => exact absurd (cartanMatrix_E8 ▸ hasRowSumNegOne_E8) hr
  | F4 => exact absurd hs not_isSimplyLaced_F4
  | G2 => exact absurd hs not_isSimplyLaced_G2

/-- A valid simply-laced type with a branch node carrying two leaves is a fork: it is of type `D`.
The exceptional types `E₆`, `E₇`, `E₈` branch too, but only one of the three arms of their branch
node is a single node. -/
private lemma eq_D_of_valid (hs : t.IsSimplyLaced)
    (hf : HasBranchWithTwoLeaves t.cartanMatrix) : t = D t.rank := by
  cases t with
  | A n =>
    obtain ⟨i, hi, -⟩ := hf
    exact absurd ⟨i, hi⟩ (not_hasRowSumNegOne_A n)
  | B n => exact absurd hs (not_isSimplyLaced_B n)
  | C n => exact absurd hs (not_isSimplyLaced_C n)
  | D n => rfl
  | E6 => exact absurd (cartanMatrix_E6 ▸ hf) not_hasBranchWithTwoLeaves_E6
  | E7 => exact absurd (cartanMatrix_E7 ▸ hf) not_hasBranchWithTwoLeaves_E7
  | E8 => exact absurd (cartanMatrix_E8 ▸ hf) not_hasBranchWithTwoLeaves_E8
  | F4 => exact absurd hs not_isSimplyLaced_F4
  | G2 => exact absurd hs not_isSimplyLaced_G2

/-- A valid simply-laced type that branches but has no branch node with two leaves is
exceptional. -/
private lemma isE_of_valid (ht : t.Valid) (hs : t.IsSimplyLaced)
    (hr : HasRowSumNegOne t.cartanMatrix) (hf : ¬ HasBranchWithTwoLeaves t.cartanMatrix) :
    t = E6 ∨ t = E7 ∨ t = E8 := by
  cases t with
  | A n => exact absurd hr (not_hasRowSumNegOne_A n)
  | B n => exact absurd hs (not_isSimplyLaced_B n)
  | C n => exact absurd hs (not_isSimplyLaced_C n)
  | D n => exact absurd (hasBranchWithTwoLeaves_D (valid_D.mp ht)) hf
  | E6 => exact Or.inl rfl
  | E7 => exact Or.inr (Or.inl rfl)
  | E8 => exact Or.inr (Or.inr rfl)
  | F4 => exact absurd hs not_isSimplyLaced_F4
  | G2 => exact absurd hs not_isSimplyLaced_G2

/-- A valid type whose double edge ends at a leaf is of type `B`. This is where the orientation of
the Cartan matrix is used: `Cₙ` is the transpose of `Bₙ`, and transposing moves the leaf to the
other end of the double edge. -/
private lemma eq_B_of_valid (ht : t.Valid) (hs : ¬ t.IsSimplyLaced)
    (h : HasLeafDoubleEdge t.cartanMatrix) : t = B t.rank := by
  cases t with
  | A n => exact absurd (isSimplyLaced_A n) hs
  | B n => rfl
  | C n => exact absurd h (not_hasLeafDoubleEdge_C (valid_C.mp ht))
  | D n => exact absurd (isSimplyLaced_D n) hs
  | E6 => exact absurd isSimplyLaced_E6 hs
  | E7 => exact absurd isSimplyLaced_E7 hs
  | E8 => exact absurd isSimplyLaced_E8 hs
  | F4 => exact absurd (cartanMatrix_F4 ▸ h) not_hasLeafDoubleEdge_F4
  | G2 => exact absurd (cartanMatrix_G2 ▸ h) not_hasLeafDoubleEdge_G2

/-- A valid type with no leaf double edge and no row summing to `-1` is of type `C`. -/
private lemma eq_C_of_valid (ht : t.Valid) (hs : ¬ t.IsSimplyLaced)
    (h : ¬ HasLeafDoubleEdge t.cartanMatrix) (hr : ¬ HasRowSumNegOne t.cartanMatrix) :
    t = C t.rank := by
  cases t with
  | A n => exact absurd (isSimplyLaced_A n) hs
  | B n => exact absurd (hasLeafDoubleEdge_B (valid_B.mp ht)) h
  | C n => rfl
  | D n => exact absurd (isSimplyLaced_D n) hs
  | E6 => exact absurd isSimplyLaced_E6 hs
  | E7 => exact absurd isSimplyLaced_E7 hs
  | E8 => exact absurd isSimplyLaced_E8 hs
  | F4 => exact absurd (cartanMatrix_F4 ▸ hasRowSumNegOne_F4) hr
  | G2 => exact absurd (cartanMatrix_G2 ▸ hasRowSumNegOne_G2) hr

/-- A valid type with no leaf double edge but a row summing to `-1` is `F₄` or `G₂`. -/
private lemma isF4_or_isG2_of_valid (ht : t.Valid) (hs : ¬ t.IsSimplyLaced)
    (h : ¬ HasLeafDoubleEdge t.cartanMatrix) (hr : HasRowSumNegOne t.cartanMatrix) :
    t = F4 ∨ t = G2 := by
  cases t with
  | A n => exact absurd (isSimplyLaced_A n) hs
  | B n => exact absurd (hasLeafDoubleEdge_B (valid_B.mp ht)) h
  | C n => exact absurd hr (not_hasRowSumNegOne_C n)
  | D n => exact absurd (isSimplyLaced_D n) hs
  | E6 => exact absurd isSimplyLaced_E6 hs
  | E7 => exact absurd isSimplyLaced_E7 hs
  | E8 => exact absurd isSimplyLaced_E8 hs
  | F4 => exact Or.inl rfl
  | G2 => exact Or.inr rfl

end Identification

/-- **The Dynkin type of a Cartan matrix is unique among valid types.** If the standard Cartan
matrices of two valid Dynkin types agree after one simultaneous relabelling of rows and columns,
the two types are equal.

Validity is necessary rather than convenient: `CartanMatrix.D_three'` relabels `D 3` to `A 3`, and
`B 1` and `C 1` are `A 1`, so the statement fails for types outside their valid ranges. -/
theorem eq_of_valid_of_cartanMatrix_eq {t t' : DynkinType} (ht : t.Valid) (ht' : t'.Valid)
    (e : Fin t.rank ≃ Fin t'.rank)
    (he : ∀ i j, t.cartanMatrix i j = t'.cartanMatrix (e i) (e j)) :
    t = t' := by
  have hrank : t.rank = t'.rank := by simpa using Fintype.card_congr e
  have hs : t.IsSimplyLaced ↔ t'.IsSimplyLaced := by
    rw [← not_iff_not, ← hasMultipleEdge_cartanMatrix_iff_of_valid ht,
      ← hasMultipleEdge_cartanMatrix_iff_of_valid ht']
    exact hasMultipleEdge_congr e he
  have hleaf := hasLeafDoubleEdge_congr e he
  have hrow := hasRowSumNegOne_congr e he
  have hfork := hasBranchWithTwoLeaves_congr e he
  by_cases hsl : t.IsSimplyLaced
  · by_cases hr : HasRowSumNegOne t.cartanMatrix
    · by_cases hf : HasBranchWithTwoLeaves t.cartanMatrix
      · rw [eq_D_of_valid hsl hf, eq_D_of_valid (hs.mp hsl) (hfork.mp hf), hrank]
      · rcases isE_of_valid ht hsl hr hf with rfl | rfl | rfl <;>
          rcases isE_of_valid ht' (hs.mp hsl) (hrow.mp hr) (fun h ↦ hf (hfork.mpr h)) with
              rfl | rfl | rfl <;>
            first
              | rfl
              | exact absurd hrank (by decide)
    · rw [eq_A_of_valid ht hsl hr, eq_A_of_valid ht' (hs.mp hsl) (fun h ↦ hr (hrow.mpr h)), hrank]
  · by_cases hd : HasLeafDoubleEdge t.cartanMatrix
    · rw [eq_B_of_valid ht hsl hd, eq_B_of_valid ht' (fun h ↦ hsl (hs.mpr h)) (hleaf.mp hd), hrank]
    · by_cases hr : HasRowSumNegOne t.cartanMatrix
      · rcases isF4_or_isG2_of_valid ht hsl hd hr with rfl | rfl <;>
          rcases isF4_or_isG2_of_valid ht' (fun h ↦ hsl (hs.mpr h)) (fun h ↦ hd (hleaf.mpr h))
              (hrow.mp hr) with rfl | rfl <;>
            first
              | rfl
              | exact absurd hrank (by decide)
      · rw [eq_C_of_valid ht hsl hd hr, eq_C_of_valid ht' (fun h ↦ hsl (hs.mpr h))
          (fun h ↦ hd (hleaf.mpr h)) (fun h ↦ hr (hrow.mpr h)), hrank]

/-- **A matrix has at most one valid Dynkin type.** If a matrix agrees entrywise with the standard
Cartan matrices of two valid Dynkin types, each under its own relabelling of the index type, the two
types are equal. This is the form the classification theorems consume, their statements being
`∃! t, t.Valid ∧ ∃ e : α ≃ Fin t.rank, ∀ i j, A i j = t.cartanMatrix (e i) (e j)`. -/
theorem eq_of_valid_of_forall_eq {α : Type*} {A : Matrix α α ℤ} {t t' : DynkinType} (ht : t.Valid)
    (ht' : t'.Valid) (e : α ≃ Fin t.rank) (e' : α ≃ Fin t'.rank)
    (he : ∀ i j, A i j = t.cartanMatrix (e i) (e j))
    (he' : ∀ i j, A i j = t'.cartanMatrix (e' i) (e' j)) : t = t' := by
  refine eq_of_valid_of_cartanMatrix_eq ht ht' (e.symm.trans e') fun i j ↦ ?_
  have h1 := he (e.symm i) (e.symm j)
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h1
  rw [Equiv.trans_apply, Equiv.trans_apply]
  exact h1.symm.trans (he' (e.symm i) (e.symm j))

end DynkinType

section RootPairing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] {b : P.Base} {t t' : DynkinType}

/-- **A base has at most one valid Cartan type.** This is the uniqueness half of the Cartan-Killing
classification; producing a valid type in the first place is the independent existence half. -/
theorem HasCartanType.eq_of_valid (h : HasCartanType P b t) (h' : HasCartanType P b t')
    (ht : t.Valid) (ht' : t'.Valid) : t = t' := by
  obtain ⟨e, he⟩ := (hasCartanType_iff b t).mp h
  obtain ⟨e', he'⟩ := (hasCartanType_iff b t').mp h'
  exact DynkinType.eq_of_valid_of_forall_eq ht ht' e e' he he'

/-- A base of some valid Cartan type has exactly one. -/
theorem HasCartanType.existsUnique_of_valid (h : HasCartanType P b t) (ht : t.Valid) :
    ∃! s : DynkinType, s.Valid ∧ HasCartanType P b s :=
  ⟨t, ⟨ht, h⟩, fun _ hs ↦ hs.2.eq_of_valid h hs.1 ht⟩

end RootPairing

end TauCeti

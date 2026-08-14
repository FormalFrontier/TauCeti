/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import TauCeti.Combinatorics.SimpleGraph.PathGraph
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Diagram
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.DoubleEdge.Classification
import TauCeti.LinearAlgebra.RootSystem.FiniteType.DoubleEdge.Reindex
import TauCeti.LinearAlgebra.RootSystem.FiniteType.TwoDoubleEdges

public section

/-!
# The branchless double-edge case of the finite-type classification

A connected finite-type Cartan diagram of maximum degree two is a path. If one edge of that path
is double, the affine-diagram exclusion in
`TauCeti.IsFiniteType.apply_mul_apply_le_one_of_chain_of_two_le` forces every other edge to be
single. The path can therefore be reindexed onto `TauCeti.doubleEdgeCartanMatrix p q`, and the
double-edge bound leaves precisely the families `B_n`, `C_n`, and the exceptional type `F_4`.

This file discharges the uniqueness hypothesis of
`TauCeti.IsFiniteType.exists_equiv_forall_eq_doubleEdgeCartanMatrix`: the caller need only exhibit
one double edge. Excluding a branch vertex from a connected finite-type diagram containing a
double edge remains the final extraction step before this result applies to the unrestricted
double-edge branch.

## Main results

* `TauCeti.IsFiniteType.exists_equiv_forall_eq_doubleEdgeCartanMatrix_of_degree_le_two`: a
  connected finite-type diagram of maximum degree two containing an oriented double edge is a
  double-edge model with two nonempty arms.
* `TauCeti.IsFiniteType.exists_doubleEdgeCartanMatrix_shape_of_degree_le_two`: the resulting arms
  have exactly one of the `B`, `C`, and `F_4` shapes.

## References

This is the branchless double-edge case of the "classification of finite-type Cartan matrices" in
Layer 5 of `TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`. The exclusion of two
multiple edges is the affine-diagram argument in N. Bourbaki, *Lie Groups and Lie Algebras,
Chapters 4--6*, Chapter VI, section 4, and J. E. Humphreys, *Introduction to Lie Algebras and
Representation Theory*, section 11.4.
-/

namespace TauCeti

open SimpleGraph

variable {B : Type*} [Fintype B] {A : Matrix B B ℤ}

/-! ## A path has at most one multiple edge -/

/-- Starting from a multiple edge at position `a` in a path numbering, every later edge is single.

The proof is strong induction on the distance from `a`. For the edge at `r`, the intervening edges
are single by induction, so `TauCeti.IsFiniteType.apply_mul_apply_le_one_of_chain_of_two_le`
applies to the subpath from `a` through `r + 1`. -/
private theorem apply_mul_apply_eq_one_of_pathEquiv_of_lt (h : IsFiniteType A)
    (k : B ≃ Fin n)
    (hk : ∀ i j, (diagramGraph A).Adj i j ↔
      (k i : ℕ) + 1 = (k j : ℕ) ∨ (k j : ℕ) + 1 = (k i : ℕ))
    {a : ℕ} (ha : a + 1 < n)
    (hfirst : 2 ≤ A (k.symm ⟨a, by omega⟩) (k.symm ⟨a + 1, ha⟩) *
      A (k.symm ⟨a + 1, ha⟩) (k.symm ⟨a, by omega⟩))
    {r : ℕ} (hr : r + 1 < n) (har : a < r) :
    A (k.symm ⟨r, by omega⟩) (k.symm ⟨r + 1, hr⟩) *
      A (k.symm ⟨r + 1, hr⟩) (k.symm ⟨r, by omega⟩) = 1 := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
      let m := r - a - 1
      have hn : 0 < n := by omega
      -- Read the interval from vertex `a` through vertex `r + 1` as a chain of length `m + 3`.
      let v : ℕ → B := fun s =>
        if hs : a + s < n then k.symm ⟨a + s, hs⟩ else k.symm ⟨0, hn⟩
      have hv_apply {s : ℕ} (hs : s < m + 3) : k (v s) = ⟨a + s, by omega⟩ := by
        simp [v, show a + s < n by omega]
      have hv : Set.InjOn v (Set.Iio (m + 3)) := by
        intro s hs t ht hst
        have hks : (k (v s) : ℕ) = a + s := by
          simpa using congrArg Fin.val (hv_apply (Set.mem_Iio.mp hs))
        have hkt : (k (v t) : ℕ) = a + t := by
          simpa using congrArg Fin.val (hv_apply (Set.mem_Iio.mp ht))
        have := congrArg (fun x : B => (k x : ℕ)) hst
        rw [hks, hkt] at this
        omega
      -- Nonconsecutive vertices of the interval are not adjacent in the path.
      have hzero : ∀ s t, s + 1 < t → t < m + 3 → A (v s) (v t) = 0 := by
        intro s t hst ht
        by_contra hne
        have hvs : (k (v s) : ℕ) = a + s := by
          simpa using congrArg Fin.val (hv_apply (s := s) (by omega))
        have hvt : (k (v t) : ℕ) = a + t := by
          simpa using congrArg Fin.val (hv_apply (s := t) ht)
        have hvne : v s ≠ v t := fun heq => by
          have := congrArg (fun x : B => (k x : ℕ)) heq
          rw [hvs, hvt] at this
          omega
        have hadj := h.diagramGraph_adj_iff.mpr ⟨hvne, hne⟩
        rw [hk, hvs, hvt] at hadj
        omega
      -- Every interior edge is closer to `a` than the target edge, hence single by induction.
      have hsimple : ∀ s, 0 < s → s < m + 1 →
          A (v s) (v (s + 1)) * A (v (s + 1)) (v s) = 1 := by
        intro s hs hsm
        have hvs : v s = k.symm ⟨a + s, by omega⟩ := by
          apply k.injective
          rw [hv_apply (by omega), k.apply_symm_apply]
        have hvss : v (s + 1) = k.symm ⟨a + s + 1, by omega⟩ := by
          apply k.injective
          rw [hv_apply (by omega), k.apply_symm_apply]
          rfl
        rw [hvs, hvss]
        exact ih (a + s) (by omega) (by omega) (by omega)
      -- The two-multiple-edge exclusion applied to this interval makes its last edge single.
      have hle := h.apply_mul_apply_le_one_of_chain_of_two_le hv hzero hsimple (m := m) (by
        have hv0 : v 0 = k.symm ⟨a, by omega⟩ := by
          apply k.injective
          rw [hv_apply (by omega), k.apply_symm_apply]
          rfl
        have hv1 : v 1 = k.symm ⟨a + 1, ha⟩ := by
          apply k.injective
          rw [hv_apply (by omega), k.apply_symm_apply]
        simpa [hv0, hv1] using hfirst)
      have hvm1 : v (m + 1) = k.symm ⟨r, by omega⟩ := by
        apply k.injective
        rw [hv_apply (by omega), k.apply_symm_apply]
        congr 1
        omega
      have hvm2 : v (m + 2) = k.symm ⟨r + 1, hr⟩ := by
        apply k.injective
        rw [hv_apply (by omega), k.apply_symm_apply]
        congr 1
        omega
      rw [hvm1, hvm2] at hle
      have hne : A (k.symm ⟨r, by omega⟩) (k.symm ⟨r + 1, hr⟩) ≠ 0 := by
        apply (h.diagramGraph_adj_iff.mp ?_).2
        rw [hk, k.apply_symm_apply, k.apply_symm_apply]
        exact Or.inl rfl
      have hone := h.one_le_apply_mul_apply hne
      omega

/-- In a path numbering, every edge other than a fixed multiple edge has Cartan product one. -/
private theorem apply_mul_apply_eq_one_of_pathEquiv (h : IsFiniteType A) (k : B ≃ Fin n)
    (hk : ∀ i j, (diagramGraph A).Adj i j ↔
      (k i : ℕ) + 1 = (k j : ℕ) ∨ (k j : ℕ) + 1 = (k i : ℕ))
    {u v : B} (huv : (k u : ℕ) + 1 = (k v : ℕ))
    (hfirst : 2 ≤ A u v * A v u) {i j : B} (hij : (diagramGraph A).Adj i j)
    (hne : ¬ ((i = u ∧ j = v) ∨ (i = v ∧ j = u))) : A i j * A j i = 1 := by
  have hpath := (hk i j).mp hij
  let a := (k u : ℕ)
  let r := min (k i : ℕ) (k j : ℕ)
  have ha : a + 1 < n := by rw [huv]; exact (k v).isLt
  have hr : r + 1 < n := by
    rcases hpath with hp | hp
    · simp only [r]
      omega
    · simp only [r]
      omega
  have hbase : 2 ≤ A (k.symm ⟨a, by omega⟩) (k.symm ⟨a + 1, ha⟩) *
      A (k.symm ⟨a + 1, ha⟩) (k.symm ⟨a, by omega⟩) := by
    have hku : k.symm ⟨a, by omega⟩ = u := by
      apply k.injective
      rw [k.apply_symm_apply]
    have hkv : k.symm ⟨a + 1, ha⟩ = v := by
      apply k.injective
      rw [k.apply_symm_apply]
      apply Fin.ext
      exact huv
    simpa only [hku, hkv] using hfirst
  rcases lt_trichotomy a r with har | har | har
  · have hone := apply_mul_apply_eq_one_of_pathEquiv_of_lt h k hk ha hbase hr har
    rcases hpath with hp | hp
    · have hki : k i = ⟨r, by omega⟩ := by apply Fin.ext; simp only [r]; omega
      have hkj : k j = ⟨r + 1, hr⟩ := by apply Fin.ext; simp only [r]; omega
      have hi : k.symm ⟨r, by omega⟩ = i := by rw [← hki, k.symm_apply_apply]
      have hj : k.symm ⟨r + 1, hr⟩ = j := by rw [← hkj, k.symm_apply_apply]
      simpa only [hi, hj] using hone
    · have hkj : k j = ⟨r, by omega⟩ := by apply Fin.ext; simp only [r]; omega
      have hki : k i = ⟨r + 1, hr⟩ := by apply Fin.ext; simp only [r]; omega
      have hj : k.symm ⟨r, by omega⟩ = j := by rw [← hkj, k.symm_apply_apply]
      have hi : k.symm ⟨r + 1, hr⟩ = i := by rw [← hki, k.symm_apply_apply]
      simpa only [hi, hj, mul_comm] using hone
  · exfalso
    rcases hpath with hp | hp
    · have hiu : i = u := k.injective (Fin.ext (by simp only [a, r] at har; omega))
      have hjv : j = v := k.injective (Fin.ext (by simp only [a, r] at har; omega))
      exact hne (Or.inl ⟨hiu, hjv⟩)
    · have hiv : i = v := k.injective (Fin.ext (by simp only [a, r] at har; omega))
      have hju : j = u := k.injective (Fin.ext (by simp only [a, r] at har; omega))
      exact hne (Or.inr ⟨hiv, hju⟩)
  · let k' : B ≃ Fin n := k.trans Fin.revPerm
    have hk' : ∀ x y, (diagramGraph A).Adj x y ↔
        (k' x : ℕ) + 1 = (k' y : ℕ) ∨ (k' y : ℕ) + 1 = (k' x : ℕ) := by
      intro x y
      rw [hk]
      simp only [k', Equiv.trans_apply, Fin.revPerm_apply, Fin.val_rev]
      omega
    have huv' : (k' v : ℕ) + 1 = (k' u : ℕ) := by
      simp only [k', Equiv.trans_apply, Fin.revPerm_apply, Fin.val_rev]
      omega
    let a' := (k' v : ℕ)
    let r' := min (k' i : ℕ) (k' j : ℕ)
    have ha' : a' + 1 < n := by rw [huv']; exact (k' u).isLt
    have hpath' := (hk' i j).mp hij
    have hr' : r' + 1 < n := by
      rcases hpath' with hp | hp <;> simp only [r'] <;> omega
    have har' : a' < r' := by
      rcases hpath with hp | hp <;>
        simp only [a, r, a', r', k', Equiv.trans_apply, Fin.revPerm_apply, Fin.val_rev] at har ⊢ <;>
        omega
    have hbase' : 2 ≤ A (k'.symm ⟨a', by omega⟩) (k'.symm ⟨a' + 1, ha'⟩) *
        A (k'.symm ⟨a' + 1, ha'⟩) (k'.symm ⟨a', by omega⟩) := by
      have hkv : k'.symm ⟨a', by omega⟩ = v := by
        apply k'.injective
        rw [k'.apply_symm_apply]
      have hku : k'.symm ⟨a' + 1, ha'⟩ = u := by
        apply k'.injective
        rw [k'.apply_symm_apply]
        apply Fin.ext
        exact huv'
      simpa only [hkv, hku, mul_comm] using hfirst
    have hone := apply_mul_apply_eq_one_of_pathEquiv_of_lt h k' hk' ha' hbase' hr' har'
    rcases hpath' with hp | hp
    · have hki : k' i = ⟨r', by omega⟩ := by apply Fin.ext; simp only [r']; omega
      have hkj : k' j = ⟨r' + 1, hr'⟩ := by apply Fin.ext; simp only [r']; omega
      have hi : k'.symm ⟨r', by omega⟩ = i := by rw [← hki, k'.symm_apply_apply]
      have hj : k'.symm ⟨r' + 1, hr'⟩ = j := by rw [← hkj, k'.symm_apply_apply]
      simpa only [hi, hj] using hone
    · have hkj : k' j = ⟨r', by omega⟩ := by apply Fin.ext; simp only [r']; omega
      have hki : k' i = ⟨r' + 1, hr'⟩ := by apply Fin.ext; simp only [r']; omega
      have hj : k'.symm ⟨r', by omega⟩ = j := by rw [← hkj, k'.symm_apply_apply]
      have hi : k'.symm ⟨r' + 1, hr'⟩ = i := by rw [← hki, k'.symm_apply_apply]
      simpa only [hi, hj, mul_comm] using hone

/-! ## Reindexing and classification -/

/-- **The branchless double-edge case is a double-edge model.** A connected finite-type diagram
of maximum degree two that contains the oriented double edge `A v u = -2` reindexes to two
nonempty chains joined by that edge.

Unlike `TauCeti.IsFiniteType.exists_equiv_forall_eq_doubleEdgeCartanMatrix`, this theorem does not
assume that every other off-diagonal entry is `-1`. The preceding path argument proves that the
chosen edge is the only multiple edge, and the finite-type sign conditions then determine every
remaining nonzero entry. -/
theorem IsFiniteType.exists_equiv_forall_eq_doubleEdgeCartanMatrix_of_degree_le_two
    [DecidableEq B] (h : IsFiniteType A) (hconn : (diagramGraph A).Connected)
    (hdeg : ∀ i, (diagramGraph A).degree i ≤ 2) {u v : B} (hvu : A v u = -2) :
    ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ ∃ e : B ≃ Fin p ⊕ Fin q,
      ∀ i j, A i j = doubleEdgeCartanMatrix p q (e i) (e j) := by
  have hvu_ne : v ≠ u := by
    rintro rfl
    rw [h.apply_self] at hvu
    omega
  have hAuv : A u v ≠ 0 := fun hz => by
    have := h.apply_eq_zero_symm hz
    rw [hvu] at this
    omega
  have hadj : (diagramGraph A).Adj u v :=
    h.diagramGraph_adj_iff.mpr ⟨hvu_ne.symm, hAuv⟩
  have hAuv_eq : A u v = -1 := by
    have hmem := h.apply_mul_apply_mem_of_ne hvu_ne.symm
    have hnonpos := h.apply_le_zero_of_ne hvu_ne.symm
    rw [hvu] at hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with hzero | hone | htwo | hthree <;> ring_nf at * <;> omega
  have hprod : A u v * A v u = 2 := by rw [hAuv_eq, hvu]; norm_num
  obtain ⟨k⟩ := IsTree.nonempty_iso_pathGraph_of_degree_le_two
    (h.isTree_diagramGraph hconn) hdeg
  have hk : ∀ i j, (diagramGraph A).Adj i j ↔
      (k i : ℕ) + 1 = (k j : ℕ) ∨ (k j : ℕ) + 1 = (k i : ℕ) :=
    fun i j => by simpa only [pathGraph_adj] using k.map_adj_iff.symm
  have hpath := (hk u v).mp hadj
  have hsingle : ∀ {i j : B}, (diagramGraph A).Adj i j →
      ¬ ((i = u ∧ j = v) ∨ (i = v ∧ j = u)) → A i j * A j i = 1 := by
    intro i j hij hne
    rcases hpath with huv | huv
    · exact apply_mul_apply_eq_one_of_pathEquiv h k.toEquiv hk huv (by omega) hij hne
    · exact apply_mul_apply_eq_one_of_pathEquiv h k.toEquiv hk huv
        (by simpa only [mul_comm] using (show 2 ≤ A u v * A v u by omega)) hij (by tauto)
  refine h.exists_equiv_forall_eq_doubleEdgeCartanMatrix hconn hdeg hvu ?_
  intro i j hij hAij
  by_cases hforward : i = v ∧ j = u
  · exact Or.inl hforward
  right
  by_cases hreverse : i = u ∧ j = v
  · rcases hreverse with ⟨rfl, rfl⟩
    exact hAuv_eq
  have hadj' := h.diagramGraph_adj_iff.mpr ⟨hij, hAij⟩
  have hone := hsingle hadj' (by tauto)
  have hnonpos := h.apply_le_zero_of_ne hij
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hone with hpos | hneg
  · exact absurd hpos.1 (by omega)
  · exact hneg.1

/-- **The admissible shapes in the branchless double-edge case.** Under the same hypotheses as
`TauCeti.IsFiniteType.exists_equiv_forall_eq_doubleEdgeCartanMatrix_of_degree_le_two`, the two
nonempty arms have one of the three shapes in the Cartan--Killing list: the second arm is a
singleton (type `C`), the first arm is a singleton (type `B`), or both have two vertices (type
`F_4`). -/
theorem IsFiniteType.exists_doubleEdgeCartanMatrix_shape_of_degree_le_two [DecidableEq B]
    (h : IsFiniteType A) (hconn : (diagramGraph A).Connected)
    (hdeg : ∀ i, (diagramGraph A).degree i ≤ 2) {u v : B} (hvu : A v u = -2) :
    ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ (q = 1 ∨ p = 1 ∨ (p = 2 ∧ q = 2)) ∧
      ∃ e : B ≃ Fin p ⊕ Fin q,
        ∀ i j, A i j = doubleEdgeCartanMatrix p q (e i) (e j) := by
  obtain ⟨p, q, hp, hq, e, he⟩ :=
    h.exists_equiv_forall_eq_doubleEdgeCartanMatrix_of_degree_le_two hconn hdeg hvu
  have hmatrix : doubleEdgeCartanMatrix p q = A.submatrix e.symm e.symm := by
    ext i j
    simpa only [Matrix.submatrix_apply, e.apply_symm_apply] using (he (e.symm i) (e.symm j)).symm
  have hmodel : IsFiniteType (doubleEdgeCartanMatrix p q) := by
    rw [hmatrix]
    exact h.submatrix e.symm.injective
  exact ⟨p, q, hp, hq, eq_one_or_eq_one_or_eq_two_two_of_isFiniteType_doubleEdge hp hq hmodel,
    e, he⟩

end TauCeti

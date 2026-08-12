/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.RootSystem.FiniteType.AffineD
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Diagram

public section

/-!
# A simply-laced finite-type diagram has at most one branch vertex

The simply-laced lane of the finite-type Cartan-matrix classification reduces connected diagrams
to paths and three-armed stars. The graph-theoretic input is that a tree of maximum degree three
cannot have two branch vertices: the path between two such vertices, together with the two unused
edges at either end, is an affine diagram of type `D`.

This file makes that reduction at the matrix level. Given two distinct degree-three vertices in
the same component, `TauCeti.IsFiniteType.exists_doubleFork_submatrix` extracts the corresponding
principal submatrix and identifies it with `TauCeti.doubleForkCartanMatrix`. The latter is not of
finite type, contradicting inheritance of finite type by principal submatrices. Consequently a
connected simply-laced finite-type diagram has a unique branch vertex whenever one exists.

The simple-lacedness hypothesis is essential at this stage: it identifies every edge on the path
with the entry `-1`. The separate multiple-edge elimination in the classification removes this
hypothesis before the final assembly theorem.

## Main results

* `TauCeti.IsFiniteType.exists_doubleFork_submatrix`: two distinct branch vertices in one
  simply-laced component contain an affine `D` principal submatrix.
* `TauCeti.IsFiniteType.eq_of_reachable_of_degree_eq_three`: two reachable degree-three vertices
  coincide.
* `TauCeti.IsFiniteType.eq_of_degree_eq_three`: the connected specialization.

## References

This is the affine-`D` elimination in the “classification of finite-type Cartan matrices” target,
Layer 5 of `TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`. See J. E. Humphreys,
*Introduction to Lie Algebras and Representation Theory*, §11.4, and Bourbaki, *Lie Groups and Lie
Algebras, Chapters 4--6*, Ch. VI, §4.
-/

namespace TauCeti

namespace IsFiniteType

variable {B : Type*} [Fintype B] [DecidableEq B] {A : Matrix B B ℤ}

omit [DecidableEq B] in
private lemma matrix_apply_eq_neg_one_iff_adj (h : IsFiniteType A) (hsl : A.IsSimplyLaced)
    {i j : B} (hij : i ≠ j) :
    A i j = -1 ↔ (diagramGraph A).Adj i j := by
  rw [h.diagramGraph_adj_iff]
  constructor
  · exact fun hij' ↦ ⟨hij, by omega⟩
  · rintro ⟨-, hij'⟩
    rcases hsl hij with hij0 | hij1
    · exact (hij' hij0).elim
    · exact hij1

private lemma not_adj_getVert_of_adj_start {V : Type*} {G : SimpleGraph V} {u v x : V}
    {p : G.Walk u v} (hG : G.IsAcyclic) (hp : p.IsPath) (hux : G.Adj u x)
    (hx : x ≠ p.snd) {i : ℕ} (hi0 : 0 < i) (hi : i ≤ p.length) :
    ¬G.Adj x (p.getVert i) := by
  have hx_support : x ∉ p.support := fun hxmem ↦ hx (hG.eq_snd_of_adj_start hp hux hxmem)
  intro hxy
  let q : G.Walk u (p.getVert i) := p.take i
  have hq : q.IsPath := hp.take i
  have hxq : x ∉ q.support := by
    simp only [q, SimpleGraph.Walk.support_take]
    exact fun hxmem ↦ hx_support (List.take_subset _ _ hxmem)
  let q' : G.Walk x (p.getVert i) := q.cons hux.symm
  have hq' : q'.IsPath := hq.cons hxq
  have heq := hG.subsingleton_path x (p.getVert i) |>.elim
    (⟨q', hq'⟩ : G.Path x (p.getVert i)) (SimpleGraph.Path.singleton hxy)
  have hlen := congrArg (fun r : G.Path x (p.getVert i) ↦ r.val.length) heq
  simp only [q', SimpleGraph.Walk.length_cons, q, SimpleGraph.Walk.take_length,
    Nat.min_eq_left hi, SimpleGraph.Path.singleton_coe, hxy.length_toWalk] at hlen
  omega

private lemma not_adj_getVert_of_adj_end {V : Type*} {G : SimpleGraph V} {u v x : V}
    {p : G.Walk u v} (hG : G.IsAcyclic) (hp : p.IsPath) (hvx : G.Adj v x)
    (hx : x ≠ p.penultimate) {i : ℕ} (hi : i < p.length) :
    ¬G.Adj x (p.getVert i) := by
  have hget : p.reverse.getVert (p.length - i) = p.getVert i := by
    rw [p.getVert_reverse, Nat.sub_sub_self hi.le]
  rw [← hget]
  exact not_adj_getVert_of_adj_start hG hp.reverse hvx
    (by simpa using hx) (Nat.sub_pos_of_lt hi) (by simp)

private lemma adj_getVert_iff_succ {V : Type*} {G : SimpleGraph V} {u v : V}
    {p : G.Walk u v} (hG : G.IsAcyclic) (hp : p.IsPath) {i j : ℕ}
    (hi : i ≤ p.length) (hj : j ≤ p.length) (hij : i ≠ j) :
    G.Adj (p.getVert i) (p.getVert j) ↔ i + 1 = j ∨ j + 1 = i := by
  constructor
  · intro hadj
    rcases lt_or_gt_of_ne hij with hij' | hji'
    · have : ¬i + 1 < j := fun hlt ↦
        not_adj_getVert_of_add_one_lt hG hp hlt hj hadj
      exact Or.inl (by omega)
    · have : ¬j + 1 < i := fun hlt ↦
        not_adj_getVert_of_add_one_lt hG hp hlt hi hadj.symm
      exact Or.inr (by omega)
  · rintro (rfl | rfl)
    · exact p.adj_getVert_succ (by omega)
    · exact (p.adj_getVert_succ (by omega)).symm

/-- **Two distinct branch vertices in one simply-laced finite-type component contain an affine
`D` principal submatrix.** The middle `Fin (n + 2)` is the path between the branch vertices, and
the two outer copies of `Fin 2` enumerate the unused neighbours at either end.

The returned map is injective, so `TauCeti.IsFiniteType.submatrix` applies directly. Its matrix
identity is oriented to match `TauCeti.doubleForkCartanMatrix`, the obstruction proved in
`TauCeti.LinearAlgebra.RootSystem.FiniteType.AffineD`. -/
theorem exists_doubleFork_submatrix (h : IsFiniteType A) (hsl : A.IsSimplyLaced)
    {u v : B} (huv : (diagramGraph A).Reachable u v) (huv_ne : u ≠ v)
    (hu : (diagramGraph A).degree u = 3) (hv : (diagramGraph A).degree v = 3) :
    ∃ (n : ℕ) (e : DoubleForkIndex n → B), Function.Injective e ∧
      A.submatrix e e = doubleForkCartanMatrix n := by
  classical
  let G := diagramGraph A
  let p : G.Path u v := huv.some.toPath
  let q : G.Walk u v := p
  have hq : q.IsPath := p.isPath
  have hqnil : ¬q.Nil := SimpleGraph.Walk.not_nil_of_ne huv_ne
  obtain ⟨n, hn⟩ : ∃ n, q.length = n + 1 := by
    exact Nat.exists_eq_succ_of_ne_zero (SimpleGraph.Walk.length_eq_zero_iff.not.mpr hqnil)
  have hsnd_mem : q.snd ∈ G.neighborFinset u :=
    (G.mem_neighborFinset u q.snd).mpr (q.adj_snd hqnil)
  have hpen_mem : q.penultimate ∈ G.neighborFinset v :=
    (G.mem_neighborFinset v q.penultimate).mpr (q.adj_penultimate hqnil).symm
  let left := (G.neighborFinset u).erase q.snd
  let right := (G.neighborFinset v).erase q.penultimate
  have hleft_card : left.card = 2 := by
    have hu' : G.degree u = 3 := hu
    simp [left, Finset.card_erase_of_mem hsnd_mem, hu']
  have hright_card : right.card = 2 := by
    have hv' : G.degree v = 3 := hv
    simp [right, Finset.card_erase_of_mem hpen_mem, hv']
  let leftEquiv : Fin 2 ≃ left := (Finset.equivFinOfCardEq hleft_card).symm
  let rightEquiv : Fin 2 ≃ right := (Finset.equivFinOfCardEq hright_card).symm
  let e : DoubleForkIndex n → B
    | .inl i => leftEquiv i
    | .inr (.inl i) => q.getVert i
    | .inr (.inr i) => rightEquiv i
  have hleft_adj (i : Fin 2) : G.Adj u (e (.inl i)) := by
    exact (G.mem_neighborFinset u _).mp (Finset.mem_of_mem_erase (leftEquiv i).property)
  have hleft_ne_snd (i : Fin 2) : e (.inl i) ≠ q.snd := by
    exact (Finset.mem_erase.mp (leftEquiv i).property).1
  have hright_adj (i : Fin 2) : G.Adj v (e (.inr (.inr i))) := by
    exact (G.mem_neighborFinset v _).mp (Finset.mem_of_mem_erase (rightEquiv i).property)
  have hright_ne_penultimate (i : Fin 2) : e (.inr (.inr i)) ≠ q.penultimate := by
    exact (Finset.mem_erase.mp (rightEquiv i).property).1
  have hleft_not_mem (i : Fin 2) : e (.inl i) ∉ q.support := fun hi ↦
    hleft_ne_snd i (h.isAcyclic_diagramGraph.eq_snd_of_adj_start hq (hleft_adj i) hi)
  have hright_not_mem (i : Fin 2) : e (.inr (.inr i)) ∉ q.support := fun hi ↦
    hright_ne_penultimate i
      (h.isAcyclic_diagramGraph.eq_penultimate_of_adj_end hq (hright_adj i) hi)
  have hleft_right_ne (i j : Fin 2) : e (.inl i) ≠ e (.inr (.inr j)) := by
    intro hij
    have hp' : (q.cons (hleft_adj i).symm).IsPath := hq.cons (hleft_not_mem i)
    have heq := h.isAcyclic_diagramGraph.subsingleton_path (e (.inl i)) v |>.elim
      (⟨q.cons (hleft_adj i).symm, hp'⟩ : G.Path (e (.inl i)) v)
      (SimpleGraph.Path.singleton (hij ▸ hright_adj j).symm)
    have hlen := congrArg (fun r : G.Path (e (.inl i)) v ↦ r.val.length) heq
    simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Path.singleton_coe,
      (hij ▸ hright_adj j).symm.length_toWalk, hn] at hlen
    omega
  have hleft_right_not_adj (i j : Fin 2) : ¬G.Adj (e (.inl i)) (e (.inr (.inr j))) := by
    have hp' : (q.cons (hleft_adj i).symm).IsPath := hq.cons (hleft_not_mem i)
    have hright_not_mem' : e (.inr (.inr j)) ∉ (q.cons (hleft_adj i).symm).support := by
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons, not_or]
      exact ⟨(hleft_right_ne i j).symm, hright_not_mem j⟩
    have hp'' := hp'.concat hright_not_mem' (hright_adj j)
    intro hadj
    have heq := h.isAcyclic_diagramGraph.subsingleton_path
      (e (.inl i)) (e (.inr (.inr j))) |>.elim
        (⟨(q.cons (hleft_adj i).symm).concat (hright_adj j), hp''⟩ :
          G.Path (e (.inl i)) (e (.inr (.inr j))))
        (SimpleGraph.Path.singleton hadj)
    have hlen := congrArg
      (fun r : G.Path (e (.inl i)) (e (.inr (.inr j))) ↦ r.val.length) heq
    simp only [SimpleGraph.Walk.length_concat, SimpleGraph.Walk.length_cons,
      SimpleGraph.Path.singleton_coe, hadj.length_toWalk, hn] at hlen
    omega
  have he : Function.Injective e := by
    intro i j hij
    rcases i with i | i | i <;> rcases j with j | j | j
    · exact congrArg Sum.inl (leftEquiv.injective (Subtype.ext hij))
    · exact (hleft_not_mem i (hij ▸ q.getVert_mem_support j)).elim
    · exact (hleft_right_ne i j hij).elim
    · exact (hleft_not_mem j (hij.symm ▸ q.getVert_mem_support i)).elim
    · apply congrArg (Sum.inr ∘ Sum.inl)
      apply Fin.ext
      exact hq.getVert_injOn (by simp only [Set.mem_ofPred_eq, hn]; omega)
        (by simp only [Set.mem_ofPred_eq, hn]; omega) hij
    · exact (hright_not_mem j (hij.symm ▸ q.getVert_mem_support i)).elim
    · exact (hleft_right_ne j i hij.symm).elim
    · exact (hright_not_mem i (hij ▸ q.getVert_mem_support j)).elim
    · exact congrArg (Sum.inr ∘ Sum.inr) (rightEquiv.injective (Subtype.ext hij))
  refine ⟨n, e, he, Matrix.ext fun i j ↦ ?_⟩
  rcases eq_or_ne i j with rfl | hij
  · simp only [Matrix.submatrix_apply, h.apply_self, doubleForkCartanMatrix_diag]
  have hentry : A (e i) (e j) = -1 ↔ G.Adj (e i) (e j) :=
    matrix_apply_eq_neg_one_iff_adj h hsl (fun heq ↦ hij (he heq))
  have hzero : A (e i) (e j) = 0 ↔ ¬G.Adj (e i) (e j) := by
    constructor
    · exact fun hz hadj ↦ (h.diagramGraph_adj_iff.mp hadj).2 hz
    · intro hadj
      rcases hsl (fun heq ↦ hij (he heq)) with hz | hone
      · exact hz
      · exact (hadj (hentry.mp hone)).elim
  rcases i with i | i | i <;> rcases j with j | j | j
  · simp only [Matrix.submatrix_apply, doubleForkCartanMatrix_inl_inl]
    split_ifs with hij'
    · exact (hij (congrArg Sum.inl hij')).elim
    · apply hzero.mpr
      intro hadj
      have hzero' := h.apply_eq_zero_of_apply_ne_zero (hleft_adj i).ne
        (hleft_adj j).ne (fun heq ↦ hij' (leftEquiv.injective (Subtype.ext heq)))
        (h.diagramGraph_adj_iff.mp (hleft_adj i)).2
        (h.diagramGraph_adj_iff.mp (hleft_adj j)).2
      exact (h.diagramGraph_adj_iff.mp hadj).2 hzero'
  · simp only [Matrix.submatrix_apply, doubleForkCartanMatrix_inl_inr_inl]
    split_ifs with hj
    · apply hentry.mpr
      simpa [e, q, hj] using (hleft_adj i).symm
    · apply hzero.mpr
      simp only [e]
      exact not_adj_getVert_of_adj_start h.isAcyclic_diagramGraph hq (hleft_adj i)
        (hleft_ne_snd i) (by omega) (by omega)
  · simp only [Matrix.submatrix_apply, doubleForkCartanMatrix_inl_inr_inr]
    exact hzero.mpr (hleft_right_not_adj i j)
  · simp only [Matrix.submatrix_apply, doubleForkCartanMatrix_inr_inl_inl]
    split_ifs with hi
    · apply hentry.mpr
      simpa [e, q, hi] using hleft_adj j
    · apply hzero.mpr
      simp only [e]
      exact fun hadj ↦ not_adj_getVert_of_adj_start h.isAcyclic_diagramGraph hq (hleft_adj j)
        (hleft_ne_snd j) (by omega) (by omega) hadj.symm
  · have hij' : i ≠ j := fun h' ↦ hij (congrArg (Sum.inr ∘ Sum.inl) h')
    simp only [Matrix.submatrix_apply, doubleForkCartanMatrix_inr_inl_inr_inl, e]
    split_ifs with heq hadj
    · exact (hij' heq).elim
    · exact hentry.mpr ((adj_getVert_iff_succ h.isAcyclic_diagramGraph hq (by omega)
        (by omega) fun h' ↦ hij' (Fin.ext h')).mpr (by omega))
    · apply hzero.mpr
      exact fun h' ↦ hadj ((adj_getVert_iff_succ h.isAcyclic_diagramGraph hq (by omega)
        (by omega) fun h'' ↦ hij' (Fin.ext h'')).mp h')
  · simp only [Matrix.submatrix_apply, doubleForkCartanMatrix_inr_inl_inr_inr]
    split_ifs with hi
    · apply hentry.mpr
      have : i = Fin.last (n + 1) := Fin.ext (by simp only [Fin.val_last]; omega)
      have hlast : q.getVert (n + 1) = v := by simpa only [← hn] using q.getVert_length
      simpa only [e, this, Fin.val_last, hlast] using hright_adj j
    · apply hzero.mpr
      simp only [e]
      exact fun hadj ↦ not_adj_getVert_of_adj_end h.isAcyclic_diagramGraph hq (hright_adj j)
        (hright_ne_penultimate j) (i := i) (by omega) hadj.symm
  · simp only [Matrix.submatrix_apply, doubleForkCartanMatrix_inr_inr_inl]
    exact hzero.mpr fun hadj ↦ hleft_right_not_adj j i hadj.symm
  · simp only [Matrix.submatrix_apply, doubleForkCartanMatrix_inr_inr_inr_inl]
    split_ifs with hj
    · apply hentry.mpr
      have : j = Fin.last (n + 1) := Fin.ext (by simp only [Fin.val_last]; omega)
      have hlast : q.getVert (n + 1) = v := by simpa only [← hn] using q.getVert_length
      simpa only [e, this, Fin.val_last, hlast] using (hright_adj i).symm
    · apply hzero.mpr
      simp only [e]
      exact not_adj_getVert_of_adj_end h.isAcyclic_diagramGraph hq (hright_adj i)
        (hright_ne_penultimate i) (i := j) (by omega)
  · simp only [Matrix.submatrix_apply, doubleForkCartanMatrix_inr_inr_inr_inr]
    split_ifs with hij'
    · exact (hij (congrArg (Sum.inr ∘ Sum.inr) hij')).elim
    · apply hzero.mpr
      intro hadj
      have hzero' := h.apply_eq_zero_of_apply_ne_zero (hright_adj i).ne
        (hright_adj j).ne (fun heq ↦ hij' (rightEquiv.injective (Subtype.ext heq)))
        (h.diagramGraph_adj_iff.mp (hright_adj i)).2
        (h.diagramGraph_adj_iff.mp (hright_adj j)).2
      exact (h.diagramGraph_adj_iff.mp hadj).2 hzero'

/-- **Reachable degree-three vertices of a simply-laced finite-type diagram coincide.** Otherwise
`TauCeti.IsFiniteType.exists_doubleFork_submatrix` produces an affine `D` principal submatrix,
contradicting `TauCeti.not_isFiniteType_doubleForkCartanMatrix`. -/
theorem eq_of_reachable_of_degree_eq_three (h : IsFiniteType A) (hsl : A.IsSimplyLaced)
    {u v : B} (huv : (diagramGraph A).Reachable u v)
    (hu : (diagramGraph A).degree u = 3) (hv : (diagramGraph A).degree v = 3) :
    u = v := by
  by_contra huv_ne
  obtain ⟨n, e, he, hmatrix⟩ := h.exists_doubleFork_submatrix hsl huv huv_ne hu hv
  have hfinite := h.submatrix he
  rw [hmatrix] at hfinite
  exact not_isFiniteType_doubleForkCartanMatrix n hfinite

/-- **A connected simply-laced finite-type diagram has at most one branch vertex.** This is the
connected form used when extracting the `D` and `E` Dynkin diagrams from a finite-type matrix. -/
theorem eq_of_degree_eq_three (h : IsFiniteType A) (hsl : A.IsSimplyLaced)
    (hconn : (diagramGraph A).Connected) {u v : B}
    (hu : (diagramGraph A).degree u = 3) (hv : (diagramGraph A).degree v = 3) :
    u = v :=
  h.eq_of_reachable_of_degree_eq_three hsl (hconn u v) hu hv

end IsFiniteType

end TauCeti

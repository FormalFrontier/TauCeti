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
to paths and three-armed stars. Two branch vertices in a tree determine a double-fork subtree: the
path between them, together with the two unused edges at either end, has affine type `D`, whose
Cartan matrix is incompatible with finite type.

This file makes that reduction at the matrix level. Given two distinct degree-three vertices in
the same component, `TauCeti.IsFiniteType.exists_doubleFork_submatrix` extracts the corresponding
principal submatrix and identifies it with `TauCeti.doubleForkCartanMatrix`. The latter is not of
finite type, contradicting inheritance of finite type by principal submatrices. Consequently a
connected simply-laced finite-type diagram has a unique branch vertex whenever one exists.

The simple-lacedness hypothesis is essential at this stage: it identifies every edge on the path
with the entry `-1`. The componentwise results impose it only on the vertices reachable from the
first branch vertex, which is where the whole extracted submatrix lives. The separate
multiple-edge elimination in the classification removes this hypothesis before the final assembly
theorem.

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
private lemma matrix_apply_eq_neg_one_iff_adj (h : IsFiniteType A) {i j : B} (hij : i ≠ j)
    (hsl : A i j = 0 ∨ A i j = -1) :
    A i j = -1 ↔ (diagramGraph A).Adj i j := by
  rw [h.diagramGraph_adj_iff]
  constructor
  · exact fun hij' ↦ ⟨hij, by omega⟩
  · rintro ⟨-, hij'⟩
    rcases hsl with hij0 | hij1
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
    · have : ¬i + 1 < j := fun hlt ↦ hG.not_adj_getVert_of_add_one_lt hp hlt hj hadj
      exact Or.inl (by omega)
    · have : ¬j + 1 < i := fun hlt ↦ hG.not_adj_getVert_of_add_one_lt hp hlt hi hadj.symm
      exact Or.inr (by omega)
  · rintro (rfl | rfl)
    · exact p.adj_getVert_succ (by omega)
    · exact (p.adj_getVert_succ (by omega)).symm

/-- Embed the two left leaves, the path, and the two right leaves in their corresponding
summands. -/
private def doubleForkEmbedding {V : Type*} {G : SimpleGraph V} {u v : V} {n : ℕ}
    (q : G.Walk u v) (left right : Fin 2 → V) : DoubleForkIndex n → V
  | .inl i => left i
  | .inr (.inl i) => q.getVert i
  | .inr (.inr i) => right i

/-- The double-fork embedding is injective once the two leaf pairs lie off the path and are
disjoint from each other. -/
private lemma doubleForkEmbedding_injective {V : Type*} {G : SimpleGraph V} {u v : V}
    {q : G.Walk u v} (hq : q.IsPath) {n : ℕ} (hn : q.length = n + 1)
    (left right : Fin 2 → V) (hleft_inj : Function.Injective left)
    (hright_inj : Function.Injective right) (hleft_not_mem : ∀ i, left i ∉ q.support)
    (hright_not_mem : ∀ i, right i ∉ q.support)
    (hleft_right_ne : ∀ i j, left i ≠ right j) :
    Function.Injective (doubleForkEmbedding (n := n) q left right) := by
  intro i j hij
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    simp only [doubleForkEmbedding] at hij
  · exact congrArg Sum.inl (hleft_inj hij)
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
  · exact congrArg (Sum.inr ∘ Sum.inr) (hright_inj hij)

omit [DecidableEq B] in
/-- The matrix on a double-fork embedding is the affine-`D` Cartan matrix when the entries along
the embedding are simply laced and the leaves have exactly the endpoint adjacencies and no
cross-edge. -/
private lemma submatrix_doubleForkEmbedding_eq (h : IsFiniteType A)
    {u v : B} {q : (diagramGraph A).Walk u v} (hq : q.IsPath) {n : ℕ}
    (hn : q.length = n + 1) (left right : Fin 2 → B)
    (he : Function.Injective (doubleForkEmbedding (n := n) q left right))
    (hsl : ∀ i j : DoubleForkIndex n, i ≠ j →
      A (doubleForkEmbedding q left right i) (doubleForkEmbedding q left right j) = 0 ∨
        A (doubleForkEmbedding q left right i) (doubleForkEmbedding q left right j) = -1)
    (hleft_inj : Function.Injective left) (hright_inj : Function.Injective right)
    (hleft_adj : ∀ i, (diagramGraph A).Adj u (left i))
    (hleft_ne_snd : ∀ i, left i ≠ q.snd)
    (hright_adj : ∀ i, (diagramGraph A).Adj v (right i))
    (hright_ne_penultimate : ∀ i, right i ≠ q.penultimate)
    (hleft_right_not_adj : ∀ i j, ¬(diagramGraph A).Adj (left i) (right j)) :
    A.submatrix (doubleForkEmbedding (n := n) q left right)
      (doubleForkEmbedding (n := n) q left right) =
      doubleForkCartanMatrix n := by
  let G := diagramGraph A
  set e : DoubleForkIndex n → B := doubleForkEmbedding (n := n) q left right with he_def
  apply Matrix.ext
  intro i j
  rcases eq_or_ne i j with rfl | hij
  · simp only [Matrix.submatrix_apply, h.apply_self, doubleForkCartanMatrix_diag]
  have hentry : A (e i) (e j) = -1 ↔ G.Adj (e i) (e j) :=
    matrix_apply_eq_neg_one_iff_adj h (fun heq ↦ hij (he heq)) (hsl i j hij)
  have hzero : A (e i) (e j) = 0 ↔ ¬G.Adj (e i) (e j) := by
    constructor
    · exact fun hz hadj ↦ (h.diagramGraph_adj_iff.mp hadj).2 hz
    · intro hadj
      rcases hsl i j hij with hz | hone
      · exact hz
      · exact (hadj (hentry.mp hone)).elim
  -- The nine cases are the row-major left/path/right blocks of the double-fork matrix.
  -- Endpoint blocks use the supplied leaf adjacencies; the middle block uses path chordlessness.
  rcases i with i | i | i <;> rcases j with j | j | j
  · simp only [Matrix.submatrix_apply, doubleForkCartanMatrix_inl_inl]
    split_ifs with hij'
    · exact (hij (congrArg Sum.inl hij')).elim
    · apply hzero.mpr
      intro hadj
      have hzero' := h.apply_eq_zero_of_apply_ne_zero (hleft_adj i).ne
        (hleft_adj j).ne (fun heq ↦ hij' (hleft_inj heq))
        (h.diagramGraph_adj_iff.mp (hleft_adj i)).2
        (h.diagramGraph_adj_iff.mp (hleft_adj j)).2
      exact (h.diagramGraph_adj_iff.mp hadj).2 hzero'
  · simp only [Matrix.submatrix_apply, doubleForkCartanMatrix_inl_inr_inl]
    split_ifs with hj
    · apply hentry.mpr
      simp only [he_def, doubleForkEmbedding]
      have hj0 : (j : ℕ) = 0 := by omega
      rw [hj0, q.getVert_zero]
      exact (hleft_adj i).symm
    · apply hzero.mpr
      simp only [he_def, doubleForkEmbedding]
      exact not_adj_getVert_of_adj_start h.isAcyclic_diagramGraph hq (hleft_adj i)
        (hleft_ne_snd i) (by omega) (by omega)
  · simp only [Matrix.submatrix_apply, doubleForkCartanMatrix_inl_inr_inr]
    exact hzero.mpr (hleft_right_not_adj i j)
  · simp only [Matrix.submatrix_apply, doubleForkCartanMatrix_inr_inl_inl]
    split_ifs with hi
    · apply hentry.mpr
      simp only [he_def, doubleForkEmbedding]
      have hi0 : (i : ℕ) = 0 := by omega
      rw [hi0, q.getVert_zero]
      exact hleft_adj j
    · apply hzero.mpr
      simp only [he_def, doubleForkEmbedding]
      exact fun hadj ↦ not_adj_getVert_of_adj_start h.isAcyclic_diagramGraph hq (hleft_adj j)
        (hleft_ne_snd j) (by omega) (by omega) hadj.symm
  · have hij' : i ≠ j := fun h' ↦ hij (congrArg (Sum.inr ∘ Sum.inl) h')
    simp only [Matrix.submatrix_apply, doubleForkCartanMatrix_inr_inl_inr_inl, he_def,
      doubleForkEmbedding]
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
      simpa only [he_def, doubleForkEmbedding, this, Fin.val_last, hlast] using hright_adj j
    · apply hzero.mpr
      simp only [he_def, doubleForkEmbedding]
      exact fun hadj ↦ not_adj_getVert_of_adj_end h.isAcyclic_diagramGraph hq (hright_adj j)
        (hright_ne_penultimate j) (i := i) (by omega) hadj.symm
  · simp only [Matrix.submatrix_apply, doubleForkCartanMatrix_inr_inr_inl]
    exact hzero.mpr fun hadj ↦ hleft_right_not_adj j i hadj.symm
  · simp only [Matrix.submatrix_apply, doubleForkCartanMatrix_inr_inr_inr_inl]
    split_ifs with hj
    · apply hentry.mpr
      have : j = Fin.last (n + 1) := Fin.ext (by simp only [Fin.val_last]; omega)
      have hlast : q.getVert (n + 1) = v := by simpa only [← hn] using q.getVert_length
      simpa only [he_def, doubleForkEmbedding, this, Fin.val_last, hlast] using (hright_adj i).symm
    · apply hzero.mpr
      simp only [he_def, doubleForkEmbedding]
      exact not_adj_getVert_of_adj_end h.isAcyclic_diagramGraph hq (hright_adj i)
        (hright_ne_penultimate i) (i := j) (by omega)
  · simp only [Matrix.submatrix_apply, doubleForkCartanMatrix_inr_inr_inr_inr]
    split_ifs with hij'
    · exact (hij (congrArg (Sum.inr ∘ Sum.inr) hij')).elim
    · apply hzero.mpr
      intro hadj
      have hzero' := h.apply_eq_zero_of_apply_ne_zero (hright_adj i).ne
        (hright_adj j).ne (fun heq ↦ hij' (hright_inj heq))
        (h.diagramGraph_adj_iff.mp (hright_adj i)).2
        (h.diagramGraph_adj_iff.mp (hright_adj j)).2
      exact (h.diagramGraph_adj_iff.mp hadj).2 hzero'

/-- **Two distinct branch vertices in one simply-laced finite-type component contain an affine
`D` principal submatrix.** The middle `Fin (n + 2)` is the path between the branch vertices, and
the two outer copies of `Fin 2` enumerate the unused neighbours at either end.

Only the component of `u` is constrained: `hsl` asks for simple-lacedness on the vertices
reachable from `u`, which is where every selected vertex lives, so components carrying a multiple
edge do not obstruct the conclusion.

The returned map is injective, so `TauCeti.IsFiniteType.submatrix` applies directly. Its matrix
identity is oriented to match `TauCeti.doubleForkCartanMatrix`, the obstruction proved in
`TauCeti.LinearAlgebra.RootSystem.FiniteType.AffineD`. -/
theorem exists_doubleFork_submatrix (h : IsFiniteType A) {u v : B}
    (huv : (diagramGraph A).Reachable u v)
    (hsl : {w | (diagramGraph A).Reachable u w}.Pairwise fun i j ↦ A i j = 0 ∨ A i j = -1)
    (huv_ne : u ≠ v)
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
  let leftVertex : Fin 2 → B := fun i ↦ leftEquiv i
  let rightVertex : Fin 2 → B := fun i ↦ rightEquiv i
  have hleft_inj : Function.Injective leftVertex := fun _ _ hij ↦
    leftEquiv.injective (Subtype.ext hij)
  have hright_inj : Function.Injective rightVertex := fun _ _ hij ↦
    rightEquiv.injective (Subtype.ext hij)
  have hleft_adj (i : Fin 2) : G.Adj u (leftVertex i) := by
    exact (G.mem_neighborFinset u _).mp (Finset.mem_of_mem_erase (leftEquiv i).property)
  have hleft_ne_snd (i : Fin 2) : leftVertex i ≠ q.snd := by
    exact (Finset.mem_erase.mp (leftEquiv i).property).1
  have hright_adj (i : Fin 2) : G.Adj v (rightVertex i) := by
    exact (G.mem_neighborFinset v _).mp (Finset.mem_of_mem_erase (rightEquiv i).property)
  have hright_ne_penultimate (i : Fin 2) : rightVertex i ≠ q.penultimate := by
    exact (Finset.mem_erase.mp (rightEquiv i).property).1
  have hleft_not_mem (i : Fin 2) : leftVertex i ∉ q.support := fun hi ↦
    hleft_ne_snd i (h.isAcyclic_diagramGraph.eq_snd_of_adj_start hq (hleft_adj i) hi)
  have hright_not_mem (i : Fin 2) : rightVertex i ∉ q.support := fun hi ↦
    hright_ne_penultimate i
      (h.isAcyclic_diagramGraph.eq_penultimate_of_adj_end hq (hright_adj i) hi)
  have hleft_right_ne (i j : Fin 2) : leftVertex i ≠ rightVertex j :=
    h.isAcyclic_diagramGraph.ne_of_adj_start_of_adj_end huv_ne hq
      (hleft_adj i) (hleft_not_mem i) (hright_adj j)
  have hleft_right_not_adj (i j : Fin 2) : ¬G.Adj (leftVertex i) (rightVertex j) :=
    h.isAcyclic_diagramGraph.not_adj_of_adj_start_of_adj_end hq
      (hleft_adj i) (hleft_not_mem i) (hright_adj j) (hright_not_mem j)
  have he' := doubleForkEmbedding_injective hq hn leftVertex rightVertex hleft_inj hright_inj
    hleft_not_mem hright_not_mem hleft_right_ne
  -- Every vertex of the double fork lies in the component of `u`, so `hsl` applies to it.
  have hreach : ∀ i : DoubleForkIndex n,
      G.Reachable u (doubleForkEmbedding q leftVertex rightVertex i) := by
    rintro (i | i | i) <;> simp only [doubleForkEmbedding]
    · exact (hleft_adj i).reachable
    · exact (q.take i).reachable
    · exact huv.trans (hright_adj i).reachable
  have hslE (i j : DoubleForkIndex n) (hij : i ≠ j) :
      A (doubleForkEmbedding q leftVertex rightVertex i)
          (doubleForkEmbedding q leftVertex rightVertex j) = 0 ∨
        A (doubleForkEmbedding q leftVertex rightVertex i)
          (doubleForkEmbedding q leftVertex rightVertex j) = -1 :=
    hsl (hreach i) (hreach j) fun heq ↦ hij (he' heq)
  have hmatrix' := submatrix_doubleForkEmbedding_eq h hq hn leftVertex rightVertex he' hslE
    hleft_inj hright_inj hleft_adj hleft_ne_snd hright_adj hright_ne_penultimate
    hleft_right_not_adj
  let e : DoubleForkIndex n → B := doubleForkEmbedding q leftVertex rightVertex
  have he : Function.Injective e := by simpa only [e] using he'
  have hmatrix : A.submatrix e e = doubleForkCartanMatrix n := by
    simpa only [e] using hmatrix'
  exact ⟨n, e, he, hmatrix⟩

/-- **Reachable degree-three vertices of a simply-laced finite-type diagram coincide.** As in
`TauCeti.IsFiniteType.exists_doubleFork_submatrix`, simple-lacedness is needed only on the
component of `u`. Otherwise that theorem produces an affine `D` principal submatrix,
contradicting `TauCeti.not_isFiniteType_doubleForkCartanMatrix`. -/
theorem eq_of_reachable_of_degree_eq_three (h : IsFiniteType A) {u v : B}
    (huv : (diagramGraph A).Reachable u v)
    (hsl : {w | (diagramGraph A).Reachable u w}.Pairwise fun i j ↦ A i j = 0 ∨ A i j = -1)
    (hu : (diagramGraph A).degree u = 3) (hv : (diagramGraph A).degree v = 3) :
    u = v := by
  by_contra huv_ne
  obtain ⟨n, e, he, hmatrix⟩ := h.exists_doubleFork_submatrix huv hsl huv_ne hu hv
  have hfinite := h.submatrix he
  rw [hmatrix] at hfinite
  exact not_isFiniteType_doubleForkCartanMatrix n hfinite

/-- **A connected simply-laced finite-type diagram has at most one branch vertex.** This is the
connected form used when extracting the `D` and `E` Dynkin diagrams from a finite-type matrix. -/
theorem eq_of_degree_eq_three (h : IsFiniteType A) (hsl : A.IsSimplyLaced)
    (hconn : (diagramGraph A).Connected) {u v : B}
    (hu : (diagramGraph A).degree u = 3) (hv : (diagramGraph A).degree v = 3) :
    u = v :=
  h.eq_of_reachable_of_degree_eq_three (hconn u v) (fun _ _ _ _ hij ↦ hsl hij) hu hv

end IsFiniteType

end TauCeti

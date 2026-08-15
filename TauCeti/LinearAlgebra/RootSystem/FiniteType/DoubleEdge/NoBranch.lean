/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.RootSystem.FiniteType.DoubleEdge.Branchless
import TauCeti.LinearAlgebra.RootSystem.FiniteType.ForkedDoubleEdge
import TauCeti.LinearAlgebra.RootSystem.FiniteType.TwoDoubleEdges

public section

/-!
# A finite-type component with a double edge has no branch vertex

The double-edge branch of the Cartan--Killing classification is already classified once its
diagram is known to be a path.  This file supplies the missing global extraction: a connected
finite-type diagram containing a double edge has maximum degree two.

Suppose instead that `c` has degree three.  Follow the unique path from `c` to the farther endpoint
of the double edge and retain two unused neighbours of `c`.  These vertices have the shape of the
affine diagram `B̃ₗ`, or its transpose according to the orientation of the double edge.  The
selected principal submatrix need not equal the affine Cartan matrix: intervening edges might
still be multiple.  What is enough, and avoids assuming their uniqueness, is that it is entrywise
at most the affine matrix.  The positive comark vector `TauCeti.affineBComark` is therefore
subdominant for the selected matrix, contradicting finite type.

Combining the degree bound with the existing branchless theorem gives the unrestricted
classification of the double-edge case into the `B`, `C`, and `F₄` shapes.

## Main results

* `TauCeti.IsFiniteType.degree_le_two_of_apply_mul_apply_eq_two`: a connected finite-type
  component containing a double edge has no branch vertex.
* `TauCeti.IsFiniteType.exists_equiv_forall_eq_doubleEdgeCartanMatrix_of_apply_mul_apply_eq_two`:
  the component is a double-edge chain of type `B`, `C`, or `F₄`.

## References

This is the multiple-edge extraction step in Layer 5 of
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`.  The affine-diagram exclusion is the
argument in J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Section
11.4, and N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Chapter VI, Section 4.
-/

namespace TauCeti

open SimpleGraph

namespace IsFiniteType

variable {B : Type*} [Fintype B] [DecidableEq B] {A : Matrix B B ℤ}

omit [Fintype B] [DecidableEq B] in
/-- Transposing a matrix does not change its unoriented diagram. -/
private lemma diagramGraph_transpose (A : Matrix B B ℤ) :
    diagramGraph A.transpose = diagramGraph A := by
  ext i j
  simp only [diagramGraph_adj, Matrix.transpose_apply]
  tauto

omit [DecidableEq B] in
/-- Along an edge of a finite-type diagram, the corresponding Cartan entry is at most `-1`. -/
private lemma apply_le_neg_one_of_adj (h : IsFiniteType A) {i j : B}
    (hij : (diagramGraph A).Adj i j) : A i j ≤ -1 := by
  have hij' := h.diagramGraph_adj_iff.mp hij
  have hle := h.apply_le_zero_of_ne hij'.1
  omega

/-- Add an off-path vertex to a path, using `none` for the extra vertex. -/
private def forkedPathEmbedding {u v x : B} {n : ℕ} (r : (diagramGraph A).Walk u v) :
    Option (Fin (n + 3)) → B
  | none => x
  | some i => r.getVert i

omit [Fintype B] [DecidableEq B] in
/-- The forked-path indexing is injective when the extra vertex lies off the path. -/
private lemma forkedPathEmbedding_injective {u v x : B} {n : ℕ}
    {r : (diagramGraph A).Walk u v} (hr : r.IsPath) (hlen : r.length = n + 2)
    (hx : x ∉ r.support) :
    Function.Injective (forkedPathEmbedding (A := A) (x := x) (n := n) r) := by
  intro i j hij
  rcases i with _ | i <;> rcases j with _ | j
  · rfl
  · simp only [forkedPathEmbedding] at hij
    exact (hx (hij ▸ r.getVert_mem_support j)).elim
  · simp only [forkedPathEmbedding] at hij
    exact (hx (hij.symm ▸ r.getVert_mem_support i)).elim
  · apply congrArg some
    apply Fin.ext
    simp only [forkedPathEmbedding] at hij
    have hi := i.isLt
    have hj := j.isLt
    have hi' : (i : ℕ) ≤ n + 2 := by omega
    have hj' : (j : ℕ) ≤ n + 2 := by omega
    exact hr.getVert_injOn (by simpa only [Set.mem_ofPred_eq, hlen] using hi')
      (by simpa only [Set.mem_ofPred_eq, hlen] using hj') hij

omit [DecidableEq B] in
/-- A forked path ending in an oriented double edge is bounded above by the affine `B` matrix. -/
private lemma submatrix_forkedPath_le_affineBCartanMatrix
    (h : IsFiniteType A) {u v x : B} {n : ℕ} {r : (diagramGraph A).Walk u v}
    (hr : r.IsPath) (hlen : r.length = n + 2) (hx : x ∉ r.support)
    (hx1 : (diagramGraph A).Adj x (r.getVert 1))
    (hlast : A (r.getVert (n + 1)) (r.getVert (n + 2)) = -2) :
    ∀ i j, A.submatrix (forkedPathEmbedding (A := A) (x := x) (n := n) r)
      (forkedPathEmbedding (A := A) (x := x) (n := n) r) i j
        ≤ affineBCartanMatrix n i j := by
  let e := forkedPathEmbedding (A := A) (x := x) (n := n) r
  have he : Function.Injective e := forkedPathEmbedding_injective hr hlen hx
  intro i j
  rcases i with _ | i <;> rcases j with _ | j
  · simp only [Matrix.submatrix_apply, forkedPathEmbedding,
      affineBCartanMatrix_diag, h.apply_self]
    norm_num
  · simp only [Matrix.submatrix_apply, forkedPathEmbedding,
      affineBCartanMatrix_none_some]
    split_ifs with hj
    · have : j = ⟨1, by omega⟩ := Fin.ext hj
      rw [this]
      exact h.apply_le_neg_one_of_adj hx1
    · have hne : x ≠ r.getVert j := fun hEq ↦ hx (hEq ▸ r.getVert_mem_support j)
      exact h.apply_le_zero_of_ne hne
  · simp only [Matrix.submatrix_apply, forkedPathEmbedding,
      affineBCartanMatrix_some_none]
    split_ifs with hi
    · have : i = ⟨1, by omega⟩ := Fin.ext hi
      rw [this]
      exact h.apply_le_neg_one_of_adj hx1.symm
    · have hne : r.getVert i ≠ x := fun hEq ↦ hx (hEq.symm ▸ r.getVert_mem_support i)
      exact h.apply_le_zero_of_ne hne
  · rw [affineBCartanMatrix_some_some, ← chainBEntry_eq_cartanMatrix_B,
      chainBEntry_def]
    simp only [Matrix.submatrix_apply, forkedPathEmbedding]
    split_ifs with hij hsucc hlastIdx hpred
    · have : i = j := Fin.ext hij
      subst j
      exact le_of_eq (h.apply_self _)
    · have hi : (i : ℕ) = n + 1 := by omega
      have hj : (j : ℕ) = n + 2 := by omega
      simpa only [hi, hj] using le_of_eq hlast
    · have hijLt : (i : ℕ) < r.length := by rw [hlen]; omega
      simpa only [hsucc] using h.apply_le_neg_one_of_adj (r.adj_getVert_succ hijLt)
    · have hijLt : (j : ℕ) < r.length := by omega
      simpa only [hpred] using h.apply_le_neg_one_of_adj (r.adj_getVert_succ hijLt).symm
    · apply h.apply_le_zero_of_ne
      exact fun hEq ↦ hij (congrArg Fin.val (Option.some.inj (he hEq)))

/-- A branch vertex and a directed double edge produce a forbidden affine dominated submatrix. -/
private lemma false_of_degree_eq_three_of_dist_eq_add_one_of_apply_eq_neg_two
    (h : IsFiniteType A) (hconn : (diagramGraph A).Connected) {c near far : B}
    (hc : (diagramGraph A).degree c = 3) (hnf : (diagramGraph A).Adj near far)
    (hdist : (diagramGraph A).dist c far = (diagramGraph A).dist c near + 1)
    (hnfEntry : A near far = -2) : False := by
  let G := diagramGraph A
  obtain ⟨p, hp, hpdist⟩ := hconn.exists_path_of_dist c near
  have hfar : far ∉ p.support := by
    intro hfarMem
    have hdistLe := SimpleGraph.dist_le (p.takeUntil far hfarMem)
    have hlengthLe := p.length_takeUntil_le_length hfarMem
    rw [hpdist] at hlengthLe
    omega
  let q : G.Walk c far := p.concat hnf
  have hq : q.IsPath := hp.concat hfar hnf
  have hqpos : 0 < q.length := by simp [q]
  obtain ⟨n, hn⟩ : ∃ n, q.length = n + 1 := Nat.exists_eq_succ_of_ne_zero hqpos.ne'
  have hsndMem : q.snd ∈ G.neighborFinset c :=
    (G.mem_neighborFinset c q.snd).mpr
      (q.adj_snd (SimpleGraph.Walk.not_nil_iff_lt_length.mpr hqpos))
  let unused := (G.neighborFinset c).erase q.snd
  have hunusedCard : unused.card = 2 := by
    calc
      unused.card = G.degree c - 1 := by
        simp only [unused, Finset.card_erase_of_mem hsndMem, card_neighborFinset_eq_degree]
      _ = 2 := by rw [hc]
  let unusedEquiv : Fin 2 ≃ unused := (Finset.equivFinOfCardEq hunusedCard).symm
  let unusedVertex : Fin 2 → B := fun i ↦ unusedEquiv i
  have hunusedInj : Function.Injective unusedVertex := fun _ _ hij ↦
    unusedEquiv.injective (Subtype.ext hij)
  have hunusedAdj (i : Fin 2) : G.Adj c (unusedVertex i) :=
    (G.mem_neighborFinset c _).mp (Finset.mem_of_mem_erase (unusedEquiv i).property)
  have hunusedNeSnd (i : Fin 2) : unusedVertex i ≠ q.snd :=
    (Finset.mem_erase.mp (unusedEquiv i).property).1
  have hunusedOff (i : Fin 2) : unusedVertex i ∉ q.support := fun hi ↦
    hunusedNeSnd i (h.isAcyclic_diagramGraph.eq_snd_of_adj_start hq (hunusedAdj i) hi)
  let r : G.Walk (unusedVertex 1) far := q.cons (hunusedAdj 1).symm
  have hr : r.IsPath := by simpa only [r] using hq.cons (hunusedOff 1)
  have hrlen : r.length = n + 2 := by simp [r, hn]
  have hxoff : unusedVertex 0 ∉ r.support := by
    intro hmem
    simp only [r, SimpleGraph.Walk.support_cons, List.mem_cons] at hmem
    rcases hmem with hEq | hmem
    · exact (by decide : (0 : Fin 2) ≠ 1) (hunusedInj hEq)
    · exact hunusedOff 0 hmem
  have hx1 : G.Adj (unusedVertex 0) (r.getVert 1) := by
    simpa [r] using (hunusedAdj 0).symm
  have hlast : A (r.getVert (n + 1)) (r.getVert (n + 2)) = -2 := by
    have hpen : q.penultimate = near := by simp [q]
    have hfirst : q.getVert n = near := by
      have hindex : q.length - 1 = n := by omega
      calc
        q.getVert n = q.getVert (q.length - 1) := by rw [hindex]
        _ = near := hpen
    have hsecond : q.getVert (n + 1) = far := by rw [← hn, q.getVert_length]
    simpa only [r, SimpleGraph.Walk.getVert_cons_succ, hfirst, hsecond] using hnfEntry
  let e := forkedPathEmbedding (A := A) (x := unusedVertex 0) (n := n) r
  have he : Function.Injective e := forkedPathEmbedding_injective hr hrlen hxoff
  have hle := submatrix_forkedPath_le_affineBCartanMatrix h hr hrlen hxoff hx1 hlast
  have hsub : IsFiniteType (A.submatrix e e) := h.submatrix he
  have hzero := hsub.eq_zero_of_forall_mul_sum_apply_mul_nonpos
      (x := affineBComark n) fun i ↦ by
    have hrow : ∑ j, ((A.submatrix e e i j : ℤ) : ℚ) * affineBComark n j ≤ 0 := by
      calc
        _ ≤ ∑ j, ((affineBCartanMatrix n i j : ℤ) : ℚ) * affineBComark n j := by
          exact Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_right
            (by exact_mod_cast hle i j) (affineBComark_pos n j).le
        _ = 0 := sum_affineBCartanMatrix_mul_affineBComark_eq_zero n i
    exact mul_nonpos_of_nonneg_of_nonpos (affineBComark_pos n i).le hrow
  exact (affineBComark_pos n none).ne' (congrFun hzero none)

/-- **A connected finite-type diagram containing a double edge has maximum degree two.**

Thus the component has no branch vertex.  This is the extraction step that makes the branchless
double-edge classification apply without an extra shape hypothesis. -/
theorem degree_le_two_of_apply_mul_apply_eq_two (h : IsFiniteType A)
    (hconn : (diagramGraph A).Preconnected) {u v : B} (huv : A u v * A v u = 2) (c : B) :
    (diagramGraph A).degree c ≤ 2 := by
  let _ : Nonempty B := ⟨u⟩
  have hconn' : (diagramGraph A).Connected := ⟨hconn⟩
  by_contra hdeg
  have hc : (diagramGraph A).degree c = 3 := by
    have := h.degree_le_three c
    omega
  have huvNe : u ≠ v := by
    rintro rfl
    rw [h.apply_self] at huv
    norm_num at huv
  have huvAdj : (diagramGraph A).Adj u v := h.diagramGraph_adj_iff.mpr
    ⟨huvNe, fun hzero ↦ by rw [hzero] at huv; norm_num at huv⟩
  have htree := h.isTree_diagramGraph hconn'
  have hgraph := diagramGraph_transpose A
  let hgraphIso : diagramGraph A.transpose ≃g diagramGraph A :=
    ⟨Equiv.refl B, by intro a b; simp only [hgraph, Equiv.refl_apply]⟩
  have hdegree : (diagramGraph A.transpose).degree c = (diagramGraph A).degree c := by
    have hdegree := hgraphIso.symm.degree_eq c
    change (diagramGraph A.transpose).degree c = (diagramGraph A).degree c at hdegree
    exact hdegree
  rcases htree.dist_eq_dist_add_one_of_adj c huvAdj with hdist | hdist
  · rcases eq_neg_one_and_eq_neg_two_or_of_mul_eq_two (h.apply_le_zero_of_ne huvNe) huv with
      ⟨huvEntry, hvuEntry⟩ | ⟨huvEntry, hvuEntry⟩
    · exact false_of_degree_eq_three_of_dist_eq_add_one_of_apply_eq_neg_two
        (c := c) (near := v) (far := u) h hconn' hc huvAdj.symm hdist hvuEntry
    · exact false_of_degree_eq_three_of_dist_eq_add_one_of_apply_eq_neg_two
        (c := c) (near := v) (far := u) h.transpose
        (by rw [hgraph]; exact hconn') (by rw [hdegree]; exact hc)
        (by rw [hgraph]; exact huvAdj.symm) (by rw [hgraph]; exact hdist)
        (by simpa using huvEntry)
  · rcases eq_neg_one_and_eq_neg_two_or_of_mul_eq_two (h.apply_le_zero_of_ne huvNe) huv with
      ⟨huvEntry, hvuEntry⟩ | ⟨huvEntry, hvuEntry⟩
    · exact false_of_degree_eq_three_of_dist_eq_add_one_of_apply_eq_neg_two h.transpose
        (c := c) (near := u) (far := v)
        (by rw [hgraph]; exact hconn') (by rw [hdegree]; exact hc)
        (by rw [hgraph]; exact huvAdj) (by rw [hgraph]; exact hdist)
        (by simpa using hvuEntry)
    · exact false_of_degree_eq_three_of_dist_eq_add_one_of_apply_eq_neg_two
        (c := c) (near := u) (far := v) h hconn' hc huvAdj hdist huvEntry

omit [DecidableEq B] in
/-- **Classification of the double-edge case.** A connected finite-type diagram containing a
double edge reindexes to two nonempty chains of one of the admissible shapes: type `C` (the second
chain is a singleton), type `B` (the first is a singleton), or type `F₄` (both have two vertices).
-/
theorem exists_equiv_forall_eq_doubleEdgeCartanMatrix_of_apply_mul_apply_eq_two
    (h : IsFiniteType A) (hconn : (diagramGraph A).Preconnected)
    {u v : B} (huv : A u v * A v u = 2) :
    ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ (q = 1 ∨ p = 1 ∨ (p = 2 ∧ q = 2)) ∧
      ∃ e : B ≃ Fin p ⊕ Fin q,
        ∀ i j, A i j = doubleEdgeCartanMatrix p q (e i) (e j) :=
  by
    classical
    exact h.exists_equiv_forall_eq_doubleEdgeCartanMatrix_eq_one_or_eq_one_or_eq_two_two
      hconn (h.degree_le_two_of_apply_mul_apply_eq_two hconn huv) huv

end IsFiniteType

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.AffineDynkinType.Basic

/-!
# The form of an affine simply-laced diagram is positive semidefinite

The generalized Cartan matrix `C` of an affine simply-laced diagram is symmetric, so the
symmetrizing diagonal matrix of the diagram is the identity and `C` itself, read over `ℝ`, is the
symmetrized bilinear form of the diagram. This file proves that this form is positive semidefinite
and computes its radical: it is the line spanned by the marks, the positive null vector `δ`
normalized to `1` at the affine node.

Away from `A₁` the matrix is `2I - A` for the adjacency matrix of the underlying graph, the marks
are a positive additive function on that graph
(`TauCeti.AffineDynkinType.sum_marks_neighborFinset_eq_two_mul`), and the graph is connected, so
both statements are instances of `TauCeti.posSemidef_graphCartanMatrix` and
`TauCeti.ker_mulVecLin_graphCartanMatrix`. The diagram `A₁`, whose matrix `!![2, -2; -2, 2]`
records a double edge and is not `2I - A` for any simple graph, is handled separately, but still
by a Laplacian: its graph is the single edge, which is `1`-regular, so `D - A` there is
`!![1, -1; -1, 1]` and the `A₁` matrix is twice it. Mathlib's `SimpleGraph.posSemidef_lapMatrix`
and `SimpleGraph.lapMatrix_mulVec_eq_zero_iff_forall_adj` therefore cover `A₁` directly.

This completes the radical statement of the affine family: the marks were already known to be a
positive null vector, and what is added here is that they span the whole null space, together
with the semidefiniteness that makes the null space the radical of the form.

## Main definitions

* `TauCeti.AffineDynkinType.realCartanMatrix`: the generalized Cartan matrix over `ℝ`.

## Main results

* `TauCeti.AffineDynkinType.realCartanMatrix_eq_graphCartanMatrix`: away from `A₁` the form is the
  matrix `2I - A` of the underlying graph.
* `TauCeti.AffineDynkinType.realCartanMatrix_mulVec_cast_marks_eq_zero`: the marks are a null
  vector of the real form.
* `TauCeti.AffineDynkinType.posSemidef_realCartanMatrix`: the symmetrized form of a valid affine
  simply-laced diagram is positive semidefinite.
* `TauCeti.AffineDynkinType.ker_mulVecLin_realCartanMatrix`: its radical is the line spanned by
  the marks.
* `TauCeti.AffineDynkinType.dotProduct_realCartanMatrix_mulVec_eq_zero_iff_mem_span_marks`: the
  form vanishes at a vector exactly when that vector is a multiple of the marks.
* `TauCeti.AffineDynkinType.finrank_ker_mulVecLin_realCartanMatrix`: that radical is
  one-dimensional.

## References

This is the positive-semidefiniteness and radical clause of Layer 0 of
`TauCetiRoadmap/ZigzagPreprojective/README.md`. See V. Kac, *Infinite dimensional Lie algebras*,
3rd ed., Theorem 4.3 and Chapter 4, where the affine diagrams are exactly the connected diagrams
of this semidefinite type.
-/

public section

namespace TauCeti

open Finset _root_.Matrix

namespace AffineDynkinType

variable {t : AffineDynkinType}

/-- The generalized Cartan matrix of an affine simply-laced diagram, over `ℝ`. A simply-laced
Cartan matrix is symmetric (`TauCeti.AffineDynkinType.isSymm_cartanMatrix`), so the symmetrizing
diagonal matrix is the identity and this matrix is already the symmetrized bilinear form of the
diagram. -/
noncomputable def realCartanMatrix (t : AffineDynkinType) :
    Matrix (Fin t.nodes) (Fin t.nodes) ℝ :=
  t.cartanMatrix.map ((↑) : ℤ → ℝ)

/-- The symmetrized form spelled out as a matrix, for a consumer outside this file: the body of
`TauCeti.AffineDynkinType.realCartanMatrix` is not exposed. -/
theorem realCartanMatrix_eq_map (t : AffineDynkinType) :
    t.realCartanMatrix = t.cartanMatrix.map ((↑) : ℤ → ℝ) :=
  (rfl)

@[simp]
theorem realCartanMatrix_apply (t : AffineDynkinType) (i j : Fin t.nodes) :
    t.realCartanMatrix i j = (t.cartanMatrix i j : ℝ) :=
  (rfl)

/-- The symmetrized form of an affine simply-laced diagram is symmetric, `A₁` included. -/
theorem isHermitian_realCartanMatrix (t : AffineDynkinType) : t.realCartanMatrix.IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, realCartanMatrix,
    ← Matrix.transpose_map, (isSymm_cartanMatrix t).eq]

/-- **Away from `A₁` the symmetrized form is the matrix `2I - A` of the underlying graph.** -/
theorem realCartanMatrix_eq_graphCartanMatrix (hg : t.IsGraphical) :
    t.realCartanMatrix = graphCartanMatrix t.graph ℝ := by
  rw [realCartanMatrix_eq_map, cartanMatrix_eq_graphCartanMatrix hg]
  exact graphCartanMatrix_map t.graph (Int.castRingHom ℝ)

/-- The marks are positive as real numbers. -/
theorem cast_marks_pos {t : AffineDynkinType} (i : Fin t.nodes) : 0 < (t.marks i : ℝ) := by
  exact_mod_cast marks_pos i

/-- **The marks are an additive function on the underlying graph**: at every node, the marks of
the neighbours sum to twice the mark of the node. This is
`TauCeti.AffineDynkinType.sum_marks_neighborFinset_eq_two_mul` over `ℝ`. -/
theorem sum_cast_marks_neighborFinset_eq_two_mul (ht : t.Valid) (hg : t.IsGraphical)
    (i : Fin t.nodes) :
    ∑ j ∈ t.graph.neighborFinset i, (t.marks j : ℝ) = 2 * (t.marks i : ℝ) := by
  have h := sum_marks_neighborFinset_eq_two_mul ht hg i
  exact_mod_cast congrArg (fun z : ℤ ↦ (z : ℝ)) h

/-! ### The diagram `A₁` -/

/-- The graph of `A₁` is the complete graph on its two nodes: it is `SimpleGraph.cycleGraph 2`,
which is `⊤`. -/
private theorem graph_A_one : (A 1).graph = ⊤ := by
  rw [graph_A]
  exact SimpleGraph.cycleGraph_two_eq_top

/-- Two nodes of `A₁` are adjacent exactly when they are distinct. -/
private theorem adj_graph_A_one (i j : Fin (A 1).nodes) : (A 1).graph.Adj i j ↔ i ≠ j := by
  rw [graph_A_one]
  exact SimpleGraph.top_adj i j

/-- Both nodes of `A₁` have degree `1`: the graph is the single edge. -/
private theorem degree_graph_A_one (v : Fin (A 1).nodes) : (A 1).graph.degree v = 1 := by
  have hnbr : (A 1).graph.neighborFinset v = {v}ᶜ := by
    ext w
    rw [SimpleGraph.mem_neighborFinset, adj_graph_A_one, Finset.mem_compl, Finset.mem_singleton,
      ne_comm]
  rw [SimpleGraph.degree, hnbr, Finset.card_compl, Finset.card_singleton, Fintype.card_fin,
    nodes_A]

/-- **The symmetrized form of `A₁` is twice the Laplacian of its graph.** `A₁` is the one affine
simply-laced diagram whose matrix is not `2I - A`, but its graph is the single edge
(`graph_A_one`), which is `1`-regular, so `D - A` there is `!![1, -1; -1, 1]` and the
multiplicity-two matrix `!![2, -2; -2, 2]` is twice it. This is what brings `A₁` inside the reach
of Mathlib's Laplacian results. -/
private theorem realCartanMatrix_A_one_eq_two_smul_lapMatrix :
    (A 1).realCartanMatrix = (2 : ℝ) • (A 1).graph.lapMatrix ℝ := by
  ext i j
  rw [realCartanMatrix_apply, _root_.Matrix.smul_apply, SimpleGraph.lapMatrix,
    _root_.Matrix.sub_apply, SimpleGraph.degMatrix, _root_.Matrix.diagonal_apply,
    SimpleGraph.adjMatrix_apply, degree_graph_A_one]
  simp only [adj_graph_A_one]
  rcases eq_or_ne i j with rfl | hij
  · norm_num
  · rw [cartanMatrix_A_one_apply]
    norm_num [hij]

/-- The symmetrized form of `A₁` is positive semidefinite: it is a positive multiple of a
Laplacian. -/
private theorem posSemidef_realCartanMatrix_A_one : (A 1).realCartanMatrix.PosSemidef :=
  .of_dotProduct_mulVec_nonneg (isHermitian_realCartanMatrix _) fun x ↦ by
    rw [star_trivial, realCartanMatrix_A_one_eq_two_smul_lapMatrix,
      _root_.Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    have h := (SimpleGraph.posSemidef_lapMatrix ℝ (A 1).graph).dotProduct_mulVec_nonneg x
    rw [star_trivial] at h
    exact mul_nonneg (by norm_num) h

/-- The null vectors of the form of `A₁` are the vectors constant along its single edge. -/
private theorem realCartanMatrix_A_one_mulVec_eq_zero_iff (x : Fin (A 1).nodes → ℝ) :
    (A 1).realCartanMatrix *ᵥ x = 0 ↔ ∀ i j : Fin (A 1).nodes, i ≠ j → x i = x j := by
  rw [realCartanMatrix_A_one_eq_two_smul_lapMatrix, _root_.Matrix.smul_mulVec, smul_eq_zero,
    SimpleGraph.lapMatrix_mulVec_eq_zero_iff_forall_adj]
  simp only [adj_graph_A_one]
  exact or_iff_right (two_ne_zero)

/-- The marks of `A₁` are the all-ones vector. -/
private theorem cast_marks_A_one : (fun i ↦ ((A 1).marks i : ℝ)) = fun _ ↦ (1 : ℝ) := by
  funext i
  simp

/-- The null space of the symmetrized form of `A₁` is spanned by its marks. -/
private theorem ker_mulVecLin_realCartanMatrix_A_one :
    LinearMap.ker (_root_.Matrix.mulVecLin (A 1).realCartanMatrix) =
      Submodule.span ℝ {fun i ↦ ((A 1).marks i : ℝ)} := by
  rw [cast_marks_A_one]
  refine le_antisymm (fun x hx ↦ ?_) ?_
  · rw [LinearMap.mem_ker, _root_.Matrix.mulVecLin_apply,
      realCartanMatrix_A_one_mulVec_eq_zero_iff] at hx
    refine Submodule.mem_span_singleton.2 ⟨x 0, funext fun i ↦ ?_⟩
    rw [Pi.smul_apply, smul_eq_mul, mul_one]
    rcases eq_or_ne (0 : Fin (A 1).nodes) i with rfl | h
    · rfl
    · exact hx 0 i h
  · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker,
      _root_.Matrix.mulVecLin_apply, realCartanMatrix_A_one_mulVec_eq_zero_iff]
    exact fun _ _ _ ↦ rfl

/-- The only affine simply-laced diagram which is not graphical is `A₁`. -/
private theorem eq_A_one_of_not_isGraphical (hg : ¬ t.IsGraphical) : t = A 1 := by
  by_contra h
  exact hg (isGraphical_iff_ne_A_one.2 h)

/-! ### The general statements -/

/-- **The marks are a null vector of the real Cartan matrix**: `Cδ = 0`. -/
theorem realCartanMatrix_mulVec_cast_marks_eq_zero (ht : t.Valid) :
    t.realCartanMatrix *ᵥ (fun i ↦ (t.marks i : ℝ)) = 0 := by
  funext i
  simp only [_root_.Matrix.mulVec_apply, dotProduct, _root_.Matrix.row_apply,
    realCartanMatrix_apply]
  have h := congrFun (cartanMatrix_mulVec_marks_eq_zero ht) i
  simp only [_root_.Matrix.mulVec_apply, dotProduct, _root_.Matrix.row_apply] at h
  norm_cast
  simpa only [Pi.zero_apply, Int.cast_zero] using congrArg (fun z : ℤ ↦ (z : ℝ)) h

/-- **The symmetrized form of a valid affine simply-laced diagram is positive semidefinite.**
Away from `A₁` this is the semidefiniteness of `2I - A` for a graph carrying a positive additive
function, the marks; at `A₁` the matrix is twice the Laplacian of the single edge. -/
theorem posSemidef_realCartanMatrix (ht : t.Valid) : t.realCartanMatrix.PosSemidef := by
  by_cases hg : t.IsGraphical
  · rw [realCartanMatrix_eq_graphCartanMatrix hg]
    exact posSemidef_graphCartanMatrix t.graph cast_marks_pos
      (sum_cast_marks_neighborFinset_eq_two_mul ht hg)
  · rw [eq_A_one_of_not_isGraphical hg]
    exact posSemidef_realCartanMatrix_A_one

/-- **The radical of the symmetrized form of a valid affine simply-laced diagram is the line
spanned by its marks.** Together with
`TauCeti.AffineDynkinType.posSemidef_realCartanMatrix` this is the semidefinite description of an
affine diagram: the form is positive semidefinite with a one-dimensional radical, spanned by the
positive vector `δ` that `TauCeti.AffineDynkinType.marks_affineNode` normalizes at the affine
node. -/
theorem ker_mulVecLin_realCartanMatrix (ht : t.Valid) :
    LinearMap.ker (_root_.Matrix.mulVecLin t.realCartanMatrix) =
      Submodule.span ℝ {fun i ↦ (t.marks i : ℝ)} := by
  by_cases hg : t.IsGraphical
  · rw [realCartanMatrix_eq_graphCartanMatrix hg]
    exact ker_mulVecLin_graphCartanMatrix t.graph (graph_connected ht) cast_marks_pos
      (sum_cast_marks_neighborFinset_eq_two_mul ht hg)
  · rw [eq_A_one_of_not_isGraphical hg]
    exact ker_mulVecLin_realCartanMatrix_A_one

/-- **The symmetrized form of a valid affine simply-laced diagram vanishes exactly on the
multiples of its marks.** For a positive semidefinite form the isotropic vectors are the radical,
so this is `TauCeti.AffineDynkinType.ker_mulVecLin_realCartanMatrix` read on the quadratic
form. -/
theorem dotProduct_realCartanMatrix_mulVec_eq_zero_iff_mem_span_marks (ht : t.Valid)
    (x : Fin t.nodes → ℝ) :
    x ⬝ᵥ (t.realCartanMatrix *ᵥ x) = 0 ↔ x ∈ Submodule.span ℝ {fun i ↦ (t.marks i : ℝ)} := by
  rw [← ker_mulVecLin_realCartanMatrix ht, LinearMap.mem_ker, _root_.Matrix.mulVecLin_apply,
    ← (posSemidef_realCartanMatrix ht).dotProduct_mulVec_zero_iff x, star_trivial]

/-- **The radical of a valid affine simply-laced diagram is one-dimensional**: the marks are a
nonzero vector spanning it. So the symmetrized form of an affine diagram is positive semidefinite
of corank one, which is what distinguishes the affine diagrams from the finite ones, whose form is
positive definite. -/
theorem finrank_ker_mulVecLin_realCartanMatrix (ht : t.Valid) :
    Module.finrank ℝ (LinearMap.ker (_root_.Matrix.mulVecLin t.realCartanMatrix)) = 1 := by
  rw [ker_mulVecLin_realCartanMatrix ht]
  refine finrank_span_singleton fun h ↦ ?_
  have h0 := congrFun h ⟨0, t.nodes_pos⟩
  exact absurd h0 (cast_marks_pos ⟨0, t.nodes_pos⟩).ne'

end AffineDynkinType

end TauCeti

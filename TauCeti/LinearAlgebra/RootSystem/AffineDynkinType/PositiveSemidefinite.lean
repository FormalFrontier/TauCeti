/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.AdditiveFunction
public import TauCeti.LinearAlgebra.RootSystem.AffineDynkinType

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
records a double edge and is not read off a simple graph, is handled separately: its form is
`2 (x₀ - x₁)²`.

This completes the radical statement of the affine family: the marks were already known to be a
positive null vector, and what is added here is that they span the whole null space, together
with the semidefiniteness that makes the null space the radical of the form.

## Main definitions

* `TauCeti.AffineDynkinType.realCartanMatrix`: the generalized Cartan matrix over `ℝ`.

## Main results

* `TauCeti.AffineDynkinType.posSemidef_realCartanMatrix`: the symmetrized form of a valid affine
  simply-laced diagram is positive semidefinite.
* `TauCeti.AffineDynkinType.ker_mulVecLin_realCartanMatrix`: its radical is the line spanned by
  the marks.
* `TauCeti.AffineDynkinType.dotProduct_realCartanMatrix_mulVec_eq_zero_iff`: the form vanishes at
  a vector exactly when that vector is a multiple of the marks.
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
  ext i j
  rw [realCartanMatrix_apply, cartanMatrix_apply hg, graphCartanMatrix_apply]
  split_ifs <;> norm_num

/-- The marks are positive as real numbers. -/
theorem cast_marks_pos (t : AffineDynkinType) (i : Fin t.nodes) : 0 < (t.marks i : ℝ) := by
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

/-- Expanding a sum over the two nodes of `A₁`. -/
private theorem sum_univ_A_one {M : Type*} [AddCommMonoid M] (y : Fin (A 1).nodes → M) :
    ∑ i, y i = y 0 + y 1 :=
  Fin.sum_univ_two y

/-- The entries of the symmetrized form of `A₁`, the one affine diagram whose matrix is not read
off a simple graph: `2` on the diagonal, and the multiplicity-two `-2` off it. -/
private theorem realCartanMatrix_A_one_apply (i j : Fin (A 1).nodes) :
    (A 1).realCartanMatrix i j = if i = j then 2 else -2 := by
  rw [realCartanMatrix_apply, cartanMatrix_A_one_apply]
  split_ifs <;> norm_num

/-- **The quadratic form of `A₁` is `2 (x₀ - x₁)²`.** The double edge doubles the off-diagonal
entry, so this is twice the form of a single edge. -/
private theorem dotProduct_realCartanMatrix_A_one_mulVec (x : Fin (A 1).nodes → ℝ) :
    x ⬝ᵥ ((A 1).realCartanMatrix *ᵥ x) = 2 * (x 0 - x 1) ^ 2 := by
  simp only [dotProduct, _root_.Matrix.mulVec, sum_univ_A_one, realCartanMatrix_A_one_apply]
  norm_num
  ring

/-- The symmetrized form of `A₁` is positive semidefinite. -/
private theorem posSemidef_realCartanMatrix_A_one : (A 1).realCartanMatrix.PosSemidef :=
  .of_dotProduct_mulVec_nonneg (isHermitian_realCartanMatrix _) fun x ↦ by
    rw [star_trivial, dotProduct_realCartanMatrix_A_one_mulVec]
    positivity

/-- The null vectors of the form of `A₁` are the vectors with equal coordinates. -/
private theorem mulVec_realCartanMatrix_A_one_eq_zero_iff (x : Fin (A 1).nodes → ℝ) :
    (A 1).realCartanMatrix *ᵥ x = 0 ↔ x 0 = x 1 := by
  rw [← posSemidef_realCartanMatrix_A_one.dotProduct_mulVec_zero_iff x, star_trivial,
    dotProduct_realCartanMatrix_A_one_mulVec]
  constructor
  · intro h
    have hsq : (x 0 - x 1) ^ 2 = 0 := by linarith
    have hzero : x 0 - x 1 = 0 := sq_eq_zero_iff.1 hsq
    linarith
  · intro h
    rw [h]
    ring

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
      mulVec_realCartanMatrix_A_one_eq_zero_iff] at hx
    refine Submodule.mem_span_singleton.2 ⟨x 0, funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩)⟩
    · change x 0 * 1 = x 0
      rw [mul_one]
    · change x 0 * 1 = x 1
      rw [mul_one]
      exact hx
  · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker,
      _root_.Matrix.mulVecLin_apply, mulVec_realCartanMatrix_A_one_eq_zero_iff]

/-- The only affine simply-laced diagram which is not graphical is `A₁`. -/
private theorem eq_A_one_of_not_isGraphical (hg : ¬ t.IsGraphical) : t = A 1 := by
  by_contra h
  exact hg (isGraphical_iff_ne_A_one.2 h)

/-! ### The general statements -/

/-- **The symmetrized form of a valid affine simply-laced diagram is positive semidefinite.**
Away from `A₁` this is the semidefiniteness of `2I - A` for a graph carrying a positive additive
function, the marks; at `A₁` the form is `2 (x₀ - x₁)²`. -/
theorem posSemidef_realCartanMatrix (ht : t.Valid) : t.realCartanMatrix.PosSemidef := by
  by_cases hg : t.IsGraphical
  · rw [realCartanMatrix_eq_graphCartanMatrix hg]
    exact posSemidef_graphCartanMatrix t.graph (fun i ↦ cast_marks_pos t i)
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
    exact ker_mulVecLin_graphCartanMatrix t.graph (graph_connected ht)
      (fun i ↦ cast_marks_pos t i) (sum_cast_marks_neighborFinset_eq_two_mul ht hg)
  · rw [eq_A_one_of_not_isGraphical hg]
    exact ker_mulVecLin_realCartanMatrix_A_one

/-- **The symmetrized form of a valid affine simply-laced diagram vanishes exactly on the
multiples of its marks.** For a positive semidefinite form the isotropic vectors are the radical,
so this is `TauCeti.AffineDynkinType.ker_mulVecLin_realCartanMatrix` read on the quadratic
form. -/
theorem dotProduct_realCartanMatrix_mulVec_eq_zero_iff (ht : t.Valid) (x : Fin t.nodes → ℝ) :
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
  exact absurd h0 (cast_marks_pos t ⟨0, t.nodes_pos⟩).ne'

end AffineDynkinType

end TauCeti

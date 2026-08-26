/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.LapMatrix

/-!
# The Cartan matrix of a graph carrying a positive additive function

For a finite simple graph `G` with adjacency matrix `A`, the matrix `2I - A` is the generalized
Cartan matrix of `G` read as a simply-laced diagram. This file proves that `2I - A` is positive
semidefinite as soon as `G` carries a positive *additive function*, a vector `δ` with

`∑_{j ∼ i} δ j = 2 * δ i`

at every node, and that for a connected `G` the radical of the associated form is then exactly the
line spanned by `δ`.

The proof is a weighted version of the Laplacian identity
`SimpleGraph.lapMatrix_toLinearMap₂'`. Writing a vector as `x = δ * y`, the additive condition
turns the quadratic form into a sum of squares over the oriented edges,

`2 * (δy)ᵀ (2I - A) (δy) = ∑_i ∑_{j ∼ i} δ i * δ j * (y i - y j)²`

(`TauCeti.two_mul_dotProduct_graphCartanMatrix_mulVec`). Nonnegativity is immediate, and the form
vanishes exactly when `y` is constant along edges, hence — on a connected graph — constant. Note
that `2I - A` is *not* the Laplacian `D - A` unless `G` is `2`-regular, so Mathlib's Laplacian
results do not apply directly: the additive function replaces `2`-regularity, and `δ i * δ j` is
the edge weight it induces.

Kac calls such a `δ` an additive function, and a connected simple graph admits a positive one
exactly when it is a graphical affine diagram (so excluding the multiplicity-two diagram `A₁`).
That classification is not proved here; the results below take `δ` as given.

## Main definitions

* `TauCeti.graphCartanMatrix`: the matrix `2I - A` of a simple graph.

## Main results

* `TauCeti.graphCartanMatrix_mulVec_eq_zero`: an additive function is a null vector.
* `TauCeti.two_mul_dotProduct_graphCartanMatrix_mulVec`: the sum-of-squares identity.
* `TauCeti.dotProduct_graphCartanMatrix_mulVec_eq_zero_iff_forall_adj` and
  `TauCeti.graphCartanMatrix_mulVec_eq_zero_iff_forall_adj`: the vanishing criterion, in
  quadratic-form and in null-vector shape.
* `TauCeti.posSemidef_graphCartanMatrix`: `2I - A` is positive semidefinite.
* `TauCeti.ker_mulVecLin_graphCartanMatrix`: on a connected graph the null space of `2I - A` is
  the line spanned by the additive function.

## References

This is the graph-theoretic half of the positive-semidefiniteness clause in Layer 0 of
`TauCetiRoadmap/ZigzagPreprojective/README.md`. See V. Kac, *Infinite dimensional Lie algebras*,
3rd ed., Chapter 4, where positive additive functions single out the affine diagrams.

Adapted from `Mathlib/Combinatorics/SimpleGraph/LapMatrix.lean` (Adrian Wüthrich, Apache-2.0): the
development of this file follows it declaration for declaration, with the additive-function weight
`δ i * δ j` replacing `2`-regularity. In particular `TauCeti.graphCartanMatrix`,
`TauCeti.graphCartanMatrix_mulVec_apply`, `TauCeti.isSymm_graphCartanMatrix` and
`TauCeti.graphCartanMatrix_mulVec_eq_zero` mirror `SimpleGraph.lapMatrix`,
`SimpleGraph.lapMatrix_mulVec_apply`, `SimpleGraph.isSymm_lapMatrix` and
`SimpleGraph.lapMatrix_mulVec_const_eq_zero`, while the proofs of
`TauCeti.posSemidef_graphCartanMatrix`, `TauCeti.graphCartanMatrix_mulVec_eq_zero_iff_forall_adj`
and the private `eq_of_forall_adj` are adapted from `SimpleGraph.posSemidef_lapMatrix`,
`SimpleGraph.lapMatrix_mulVec_eq_zero_iff_forall_adj` and the walk induction inside
`SimpleGraph.lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_reachable`.
-/

public section

namespace TauCeti

open Finset Matrix

section Auxiliary

variable {V : Type*}

/-- A function constant along the edges of a preconnected graph is constant: walk from one node to
the other. -/
private theorem eq_of_forall_adj {W : Type*} {G : SimpleGraph V} {f : V → W}
    (hG : G.Preconnected) (h : ∀ i j, G.Adj i j → f i = f j) (i j : V) : f i = f j := by
  obtain ⟨w⟩ := hG i j
  induction w with
  | nil => rfl
  | cons hadj _ ih => exact (h _ _ hadj).trans ih

/-- Summing over the neighbours of a node and then over the nodes is the same as summing over the
nodes and then over the neighbours: the adjacency relation is symmetric. -/
private theorem sum_sum_neighborFinset_comm [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {R : Type*} [AddCommMonoid R] (f : V → V → R) :
    ∑ i, ∑ j ∈ G.neighborFinset i, f i j = ∑ j, ∑ i ∈ G.neighborFinset j, f i j :=
  Finset.sum_comm' fun i j ↦ by
    simp only [Finset.mem_univ, true_and, and_true, SimpleGraph.mem_neighborFinset]
    exact ⟨fun h ↦ h.symm, fun h ↦ h.symm⟩

/-- Every vector is `δ * y` for `y i = x i / δ i`, as soon as `δ` is nowhere zero. -/
private theorem mul_div_self_eq {R : Type*} [Field R] {δ : V → R} (hδ : ∀ i, δ i ≠ 0)
    (x : V → R) : δ * (fun i ↦ x i / δ i) = x :=
  funext fun i ↦ mul_div_cancel₀ (x i) (hδ i)

end Auxiliary

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The **generalized Cartan matrix `2I - A` of a simple graph**, read as a simply-laced diagram:
`2` on the diagonal, `-1` at an edge and `0` elsewhere. Unlike the Laplacian
`SimpleGraph.lapMatrix`, whose diagonal records the degrees, this matrix has a constant
diagonal. -/
def graphCartanMatrix (R : Type*) [Ring R] : Matrix V V R := (2 : R) • 1 - G.adjMatrix R

variable {R : Type*}

/-- `2I - A` spelled out as a matrix, for a consumer outside this file: the body of
`TauCeti.graphCartanMatrix` is not exposed. -/
theorem graphCartanMatrix_eq_two_smul_one_sub_adjMatrix [Ring R] :
    graphCartanMatrix G R = (2 : R) • 1 - G.adjMatrix R := by rw [graphCartanMatrix]

/-- The entries of `2I - A`: `2` on the diagonal, `-1` at an edge and `0` elsewhere. -/
@[simp]
theorem graphCartanMatrix_apply [Ring R] (i j : V) :
    graphCartanMatrix G R i j = if i = j then 2 else if G.Adj i j then -1 else 0 := by
  rw [graphCartanMatrix]
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    SimpleGraph.adjMatrix_apply]
  rcases eq_or_ne i j with rfl | hij
  · simp
  · rw [ite_eq_right hij, ite_eq_right hij]
    split_ifs <;> simp

/-- `2I - A` is compatible with a change of coefficient ring. -/
@[simp]
theorem graphCartanMatrix_map {S : Type*} [Ring R] [Ring S] (f : R →+* S) :
    (graphCartanMatrix G R).map f = graphCartanMatrix G S := by
  ext i j
  rw [Matrix.map_apply, graphCartanMatrix_apply, graphCartanMatrix_apply]
  split_ifs
  · exact map_ofNat f 2
  · rw [map_neg, map_one]
  · exact map_zero f

/-- `2I - A` is symmetric. -/
theorem isSymm_graphCartanMatrix [Ring R] : (graphCartanMatrix G R).IsSymm := by
  rw [graphCartanMatrix]
  exact (Matrix.isSymm_one.smul (2 : R)).sub (SimpleGraph.isSymm_adjMatrix _)

variable [Fintype V]

/-- Multiplying a vector by `2I - A` doubles it and subtracts the sum over its neighbours. -/
theorem graphCartanMatrix_mulVec_apply [Ring R] (x : V → R) (i : V) :
    (graphCartanMatrix G R *ᵥ x) i = 2 * x i - ∑ j ∈ G.neighborFinset i, x j := by
  rw [graphCartanMatrix, Matrix.sub_mulVec]
  simp [Matrix.smul_mulVec, SimpleGraph.adjMatrix_mulVec_apply]

/-- **An additive function is a null vector of `2I - A`.** Positivity is not needed: the balance
condition alone says that `2 δ i` is the sum of the neighbouring values. -/
theorem graphCartanMatrix_mulVec_eq_zero [Ring R] {δ : V → R}
    (hδ : ∀ i, ∑ j ∈ G.neighborFinset i, δ j = 2 * δ i) : graphCartanMatrix G R *ᵥ δ = 0 := by
  funext i
  rw [graphCartanMatrix_mulVec_apply, hδ i, sub_self, Pi.zero_apply]

/-- **The sum-of-squares identity for a graph with an additive function.** After the substitution
`x = δ * y`, twice the quadratic form of `2I - A` at `x` is the sum, over the oriented edges, of
`δ i * δ j * (y i - y j) ²`. This is the weighted analogue of
`SimpleGraph.lapMatrix_toLinearMap₂'`, with the edge weight `δ i * δ j` in place of `1`, and it is
where the additive condition on `δ` enters. -/
theorem two_mul_dotProduct_graphCartanMatrix_mulVec [CommRing R] {δ : V → R}
    (hδ : ∀ i, ∑ j ∈ G.neighborFinset i, δ j = 2 * δ i) (y : V → R) :
    2 * ((δ * y) ⬝ᵥ (graphCartanMatrix G R *ᵥ (δ * y))) =
      ∑ i, ∑ j ∈ G.neighborFinset i, δ i * δ j * (y i - y j) ^ 2 := by
  have expand : ∑ i, ∑ j ∈ G.neighborFinset i, δ i * δ j * (y i - y j) ^ 2 =
      (∑ i, ∑ j ∈ G.neighborFinset i, δ i * y i ^ 2 * δ j) +
        (∑ i, ∑ j ∈ G.neighborFinset i, δ i * (δ j * y j ^ 2)) -
          ∑ i, ∑ j ∈ G.neighborFinset i, 2 * (δ i * y i * (δ j * y j)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  have s₁ : ∑ i, ∑ j ∈ G.neighborFinset i, δ i * y i ^ 2 * δ j = ∑ i, 2 * (δ i * y i) ^ 2 := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Finset.mul_sum, hδ i]
    ring
  have s₂ : ∑ i, ∑ j ∈ G.neighborFinset i, δ i * (δ j * y j ^ 2) = ∑ i, 2 * (δ i * y i) ^ 2 := by
    rw [sum_sum_neighborFinset_comm G fun i j ↦ δ i * (δ j * y j ^ 2)]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← Finset.sum_mul, hδ j]
    ring
  have s₃ : ∑ i, ∑ j ∈ G.neighborFinset i, 2 * (δ i * y i * (δ j * y j)) =
      ∑ i, 2 * (δ i * y i * ∑ j ∈ G.neighborFinset i, δ j * y j) := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.mul_sum, Finset.mul_sum]
  have hdot : (δ * y) ⬝ᵥ (graphCartanMatrix G R *ᵥ (δ * y)) =
      ∑ i, δ i * y i * (2 * (δ i * y i) - ∑ j ∈ G.neighborFinset i, δ j * y j) := by
    rw [dotProduct]
    exact Finset.sum_congr rfl fun i _ ↦ by
      rw [graphCartanMatrix_mulVec_apply]
      simp only [Pi.mul_apply]
  rw [expand, s₁, s₂, s₃, hdot, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

section Ordered

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R] {δ : V → R}

/-- **The quadratic form of `2I - A` is nonnegative** on a graph with a positive additive
function. -/
theorem dotProduct_graphCartanMatrix_mulVec_nonneg (hpos : ∀ i, 0 < δ i)
    (hδ : ∀ i, ∑ j ∈ G.neighborFinset i, δ j = 2 * δ i) (x : V → R) :
    0 ≤ x ⬝ᵥ (graphCartanMatrix G R *ᵥ x) := by
  have hx := two_mul_dotProduct_graphCartanMatrix_mulVec G hδ fun i ↦ x i / δ i
  rw [mul_div_self_eq fun i ↦ (hpos i).ne'] at hx
  have hnonneg : 0 ≤ ∑ i, ∑ j ∈ G.neighborFinset i, δ i * δ j * (x i / δ i - x j / δ j) ^ 2 :=
    Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
      mul_nonneg (mul_nonneg (hpos i).le (hpos j).le) (sq_nonneg _)
  linarith

/-- **The quadratic form of `2I - A` vanishes exactly on the vectors proportional to `δ` along
every edge.** The stated condition is `x i / δ i = x j / δ j` cleared of denominators. -/
theorem dotProduct_graphCartanMatrix_mulVec_eq_zero_iff_forall_adj (hpos : ∀ i, 0 < δ i)
    (hδ : ∀ i, ∑ j ∈ G.neighborFinset i, δ j = 2 * δ i) (x : V → R) :
    x ⬝ᵥ (graphCartanMatrix G R *ᵥ x) = 0 ↔ ∀ i j, G.Adj i j → x i * δ j = x j * δ i := by
  have hx := two_mul_dotProduct_graphCartanMatrix_mulVec G hδ fun i ↦ x i / δ i
  rw [mul_div_self_eq fun i ↦ (hpos i).ne'] at hx
  have hiff : x ⬝ᵥ (graphCartanMatrix G R *ᵥ x) = 0 ↔
      ∑ i, ∑ j ∈ G.neighborFinset i, δ i * δ j * (x i / δ i - x j / δ j) ^ 2 = 0 := by
    rw [← hx]
    constructor
    · intro h; rw [h, mul_zero]
    · intro h; linarith
  rw [hiff, Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
    mul_nonneg (mul_nonneg (hpos i).le (hpos j).le) (sq_nonneg _)]
  constructor
  · intro h i j hij
    have hj := (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦
        mul_nonneg (mul_nonneg (hpos i).le (hpos j).le)
          (sq_nonneg (x i / δ i - x j / δ j))).1 (h i (Finset.mem_univ i)) j
      ((SimpleGraph.mem_neighborFinset ..).2 hij)
    have hdiv : x i / δ i = x j / δ j :=
      sub_eq_zero.1 (sq_eq_zero_iff.1
        ((mul_eq_zero.1 hj).resolve_left (mul_pos (hpos i) (hpos j)).ne'))
    rwa [div_eq_div_iff (hpos i).ne' (hpos j).ne'] at hdiv
  · intro h i _
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    have hij := (SimpleGraph.mem_neighborFinset ..).1 hj
    have hzero : x i / δ i - x j / δ j = 0 := by
      rw [div_sub_div _ _ (hpos i).ne' (hpos j).ne', h i j hij, mul_comm (δ i) (x j), sub_self,
        zero_div]
    rw [hzero]
    ring

/-- **`2I - A` is positive semidefinite** on a graph with a positive additive function. -/
theorem posSemidef_graphCartanMatrix [StarRing R] [TrivialStar R] (hpos : ∀ i, 0 < δ i)
    (hδ : ∀ i, ∑ j ∈ G.neighborFinset i, δ j = 2 * δ i) :
    (graphCartanMatrix G R).PosSemidef := by
  refine .of_dotProduct_mulVec_nonneg ?_ fun x ↦ ?_
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial,
      isSymm_graphCartanMatrix]
  · rw [star_trivial]
    exact dotProduct_graphCartanMatrix_mulVec_nonneg G hpos hδ x

/-- The null vectors of `2I - A`, in edge-local form. -/
theorem graphCartanMatrix_mulVec_eq_zero_iff_forall_adj (hpos : ∀ i, 0 < δ i)
    (hδ : ∀ i, ∑ j ∈ G.neighborFinset i, δ j = 2 * δ i) (x : V → R) :
    graphCartanMatrix G R *ᵥ x = 0 ↔ ∀ i j, G.Adj i j → x i * δ j = x j * δ i := by
  constructor
  · intro hx
    apply (dotProduct_graphCartanMatrix_mulVec_eq_zero_iff_forall_adj G hpos hδ x).1
    rw [hx, dotProduct_zero]
  · intro hx
    funext i
    rw [graphCartanMatrix_mulVec_apply, Pi.zero_apply]
    have hsum : δ i * (∑ j ∈ G.neighborFinset i, x j) = δ i * (2 * x i) := by
      calc
        δ i * (∑ j ∈ G.neighborFinset i, x j) =
            ∑ j ∈ G.neighborFinset i, δ i * x j := Finset.mul_sum ..
        _ = ∑ j ∈ G.neighborFinset i, x i * δ j :=
          Finset.sum_congr rfl fun j hj ↦ by
            simpa only [mul_comm] using (hx i j ((SimpleGraph.mem_neighborFinset ..).1 hj)).symm
        _ = x i * (∑ j ∈ G.neighborFinset i, δ j) := (Finset.mul_sum ..).symm
        _ = x i * (2 * δ i) := by rw [hδ i]
        _ = δ i * (2 * x i) := by ring
    rw [mul_left_cancel₀ (hpos i).ne' hsum, sub_self]

/-- **On a connected graph the null space of `2I - A` is the line spanned by the additive
function.** Since `2I - A` is positive semidefinite, this is the radical of its bilinear form. -/
theorem ker_mulVecLin_graphCartanMatrix (hG : G.Connected) (hpos : ∀ i, 0 < δ i)
    (hδ : ∀ i, ∑ j ∈ G.neighborFinset i, δ j = 2 * δ i) :
    LinearMap.ker (Matrix.mulVecLin (graphCartanMatrix G R)) = Submodule.span R {δ} := by
  refine le_antisymm (fun x hx ↦ ?_) ?_
  · rw [LinearMap.mem_ker, Matrix.mulVecLin_apply,
      graphCartanMatrix_mulVec_eq_zero_iff_forall_adj G hpos hδ] at hx
    obtain ⟨i₀⟩ := hG.nonempty
    refine Submodule.mem_span_singleton.2 ⟨x i₀ / δ i₀, ?_⟩
    funext i
    have hconst : x i / δ i = x i₀ / δ i₀ :=
      eq_of_forall_adj hG.preconnected
        (fun a b hab ↦ by rw [div_eq_div_iff (hpos a).ne' (hpos b).ne', hx a b hab]) i i₀
    rw [Pi.smul_apply, smul_eq_mul, ← hconst, div_mul_cancel₀ _ (hpos i).ne']
  · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker,
      Matrix.mulVecLin_apply]
    exact graphCartanMatrix_mulVec_eq_zero G hδ

end Ordered

end TauCeti

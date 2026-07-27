/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import TauCeti.LowDimTopology.Plumbing.NegativeDefinite

/-!
# A diagonal-dominance criterion for negative-definite plumbings

Némethi's lattice homology takes as its standing hypothesis a **negative-definite** plumbing
graph: the intersection form of the plumbed four-manifold must be negative definite on the whole
lattice. Checking this directly means diagonalizing (or completing the square on) the intersection
matrix, which is what `NegativeDefinite.lean` does by hand for the `A₂` plumbing. This file
supplies a general, purely combinatorial sufficient condition that avoids that work.

The condition is **strict diagonal dominance** of the negated intersection matrix `-A`: for every
sphere `i`, the framing is more negative than the number of neighbours,

`degree i < - weight i`.

Since the off-diagonal entries of `-A` are minus the adjacency indicators, the row sum of their
absolute values off the diagonal is exactly `degree i`, so the displayed inequality says that the
diagonal entry `- weight i` strictly dominates that row sum. The standard arithmetic-geometric
bound `2 (x i)(x j) ≤ (x i)² + (x j)²` on each edge then gives, for every lattice vector `x`,

`x · x ≤ ∑ i, (weight i + degree i) · (x i)²`,

whose right-hand side is a sum of nonpositive terms that is strictly negative once `x ≠ 0`. Hence
the intersection form is strictly negative away from the origin, which is the self-pairing form of
negative-definiteness. This recovers `a2Plumbing_isNegativeDefinite` (each vertex of the `A₂`
plumbing has degree `1` and framing `-2`) as a one-line instance, and, more usefully, certifies
negative-definiteness of every plumbing whose framings are sufficiently negative — the generic
Seifert-fibred examples — without any per-graph square completion.

## Main results

* `TauCeti.PlumbingGraph.intersectionForm_self_le_weight_add_degree`: the diagonal-dominance upper
  bound `x · x ≤ ∑ i, (weight i + degree i) · (x i)²`.
* `TauCeti.PlumbingGraph.isNegativeDefinite_of_degree_lt_neg_weight`: strict diagonal dominance
  `degree i < - weight i` for all `i` implies the plumbing is negative definite.

## References

This supplies a prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane L
("lattice homology"), whose standing hypothesis is a negative-definite plumbing. The
diagonal-dominance sufficient condition is the elementary certificate used throughout Némethi,
[arXiv:0709.0841](https://arxiv.org/abs/0709.0841), after Ozsváth--Szabó,
[arXiv:math/0203265](https://arxiv.org/abs/math/0203265).
-/

open scoped Matrix

public section

namespace TauCeti

namespace PlumbingGraph

variable {V : Type*} [DecidableEq V] [Fintype V] (P : PlumbingGraph V)

omit [DecidableEq V] in
/-- The adjacency cross-term sum of the intersection form is bounded above by the degree-weighted
sum of squares: applying `2 (x i)(x j) ≤ (x i)² + (x j)²` on each edge and summing over the two
endpoints turns each edge into a diagonal contribution to both of its endpoints. -/
private theorem sum_adj_mul_le_degree_mul_sq (x : V → ℤ) :
    (∑ i, ∑ j, if P.toSimpleGraph.Adj i j then x i * x j else 0) ≤
      ∑ i, (P.toSimpleGraph.degree i : ℤ) * x i ^ 2 := by
  classical
  let y : V → ℚ := fun i => x i
  have hlap := (SimpleGraph.posSemidef_lapMatrix ℚ P.toSimpleGraph).dotProduct_mulVec_nonneg y
  rw [star_trivial, SimpleGraph.lapMatrix, Matrix.sub_mulVec, dotProduct_sub,
    SimpleGraph.dotProduct_mulVec_degMatrix,
    SimpleGraph.dotProduct_mulVec_adjMatrix] at hlap
  rw [sub_nonneg] at hlap
  dsimp [y] at hlap
  simp only [pow_two]
  have hlap' :
      (∑ i, ∑ j, if P.toSimpleGraph.Adj i j then (x i : ℚ) * x j else 0) ≤
        ∑ i, (P.toSimpleGraph.degree i : ℚ) * ((x i : ℚ) * x i) := by
    simpa only [mul_assoc] using hlap
  exact_mod_cast hlap'

/-- The diagonal-dominance upper bound on the intersection form: the self-pairing is at most the
sum, over spheres, of `(weight i + degree i)` times `(x i)²`. This is the quadratic-form estimate
underlying the negative-definiteness criterion. -/
theorem intersectionForm_self_le_weight_add_degree (x : V → ℤ) :
    P.intersectionForm x x ≤
      ∑ i, (P.weight i + P.toSimpleGraph.degree i) * x i ^ 2 := by
  rw [P.intersectionForm_self]
  have hle := P.sum_adj_mul_le_degree_mul_sq x
  have hcombine :
      (∑ i, P.weight i * x i ^ 2) + ∑ i, (P.toSimpleGraph.degree i : ℤ) * x i ^ 2 =
        ∑ i, (P.weight i + P.toSimpleGraph.degree i) * x i ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  linarith [hcombine]

/-- **Strict diagonal dominance implies negative-definiteness.** If every sphere's framing is more
negative than its number of neighbours, `degree i < - weight i`, then the plumbing is negative
definite.

The row-sum condition makes each coefficient `weight i + degree i` strictly negative, so the
diagonal-dominance bound `intersectionForm_self_le_weight_add_degree` expresses `x · x` as at most
a sum of nonpositive terms; picking a coordinate where `x` is nonzero makes that sum strictly
negative. -/
theorem isNegativeDefinite_of_degree_lt_neg_weight
    (h : ∀ i, (P.toSimpleGraph.degree i : ℤ) < -P.weight i) : P.IsNegativeDefinite := by
  rw [P.isNegativeDefinite_iff_forall_intersectionForm_self_neg]
  intro x hx
  refine lt_of_le_of_lt (P.intersectionForm_self_le_weight_add_degree x) ?_
  -- Every coefficient is strictly negative, so every summand is nonpositive.
  have hcoeff : ∀ i, P.weight i + (P.toSimpleGraph.degree i : ℤ) < 0 := fun i => by
    have := h i; linarith
  have hnonpos : ∀ i ∈ Finset.univ,
      (P.weight i + (P.toSimpleGraph.degree i : ℤ)) * x i ^ 2 ≤ 0 := fun i _ =>
    mul_nonpos_of_nonpos_of_nonneg (hcoeff i).le (sq_nonneg _)
  -- Some coordinate is nonzero, and there its summand is strictly negative.
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
  have hsq : (1 : ℤ) ≤ x i₀ ^ 2 := by
    have : x i₀ ^ 2 ≠ 0 := pow_ne_zero 2 hi₀
    have : (0 : ℤ) < x i₀ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm this)
    omega
  have hstrict : (P.weight i₀ + (P.toSimpleGraph.degree i₀ : ℤ)) * x i₀ ^ 2 < 0 := by
    have hc := hcoeff i₀
    nlinarith [hc, hsq]
  exact Finset.sum_neg' hnonpos ⟨i₀, Finset.mem_univ i₀, hstrict⟩

end PlumbingGraph

/-- The triangle plumbing on three spheres, each with framing `-3`: its underlying graph is the
complete graph `K₃`, so every vertex has degree `2`, and `2 < 3`. A self-validating instance of
the diagonal-dominance criterion whose graph carries edges (so the adjacency bound is genuinely
used), where hand square-completion would be more laborious than for `A₂`. -/
private def triangleMinusThreePlumbing : PlumbingGraph (Fin 3) where
  toSimpleGraph := ⊤
  decidableAdj := inferInstance
  weight := fun _ => -3

private theorem triangleMinusThreePlumbing_degree (i : Fin 3) :
    triangleMinusThreePlumbing.toSimpleGraph.degree i = 2 := by
  unfold triangleMinusThreePlumbing
  rw [SimpleGraph.IsRegularOfDegree.top i]
  simp

example : triangleMinusThreePlumbing.IsNegativeDefinite := by
  refine triangleMinusThreePlumbing.isNegativeDefinite_of_degree_lt_neg_weight fun i => ?_
  have hdeg := triangleMinusThreePlumbing_degree i
  have hw : triangleMinusThreePlumbing.weight i = -3 := rfl
  rw [hdeg, hw]
  norm_num

end TauCeti

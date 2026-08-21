/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Plumbing graphs and their intersection forms

This file opens the lattice-homology lane of the combinatorial Heegaard Floer roadmap. A
plumbing graph records the combinatorial data of a plumbing of disk bundles over spheres: a
simple graph whose vertices are the spheres, whose edges record which spheres are plumbed, and
an integer weight on each vertex giving its self-intersection (the framing / Euler number).

The fundamental algebraic object attached to this data is the **intersection form**, the
symmetric `ℤ`-bilinear form on `V → ℤ` whose matrix is the framing on the diagonal and the
adjacency indicator off the diagonal. This is the lattice on which Némethi's lattice homology
of a (negative-definite) plumbed three-manifold is built. Here we set up the matrix, its
entry formulas and symmetry, the bilinear form and its self-pairing expansion as a quadratic
form, and the negative-definiteness predicate, recording that a negative-definite plumbing has
every framing negative.

We model the underlying combinatorics with a `SimpleGraph`: one edge between two distinct
spheres, no edge multiplicities or signs. The matrix-level definitions make sense for any
vertex type; the lattice form used for Lane L is introduced under `[Fintype V]`, matching the
finite plumbing graphs in the roadmap. This is the standard starting point (the plumbing trees
of Seifert-fibred examples), with edge multiplicities a later refinement.

## Main definitions

* `TauCeti.PlumbingGraph`: a simple graph with an integer weight on each vertex.
* `TauCeti.PlumbingGraph.intersectionMatrix`: the framing-diagonal adjacency matrix.
* `TauCeti.PlumbingGraph.intersectionForm`: the associated symmetric `ℤ`-bilinear form.
* `TauCeti.PlumbingGraph.IsNegativeDefinite`: negative-definiteness of the intersection matrix.

## Main results

* `TauCeti.PlumbingGraph.intersectionMatrix_diag` and
  `TauCeti.PlumbingGraph.intersectionMatrix_apply_of_ne`: the diagonal entry is the framing and
  an off-diagonal entry is the adjacency indicator.
* `TauCeti.PlumbingGraph.intersectionMatrix_isSymm`,
  `TauCeti.PlumbingGraph.intersectionForm_isSymm`: the intersection form is symmetric.
* `TauCeti.PlumbingGraph.intersectionForm_apply_weight_add_adj`: the bilinear form expanded
  as framing terms plus adjacency terms.
* `TauCeti.PlumbingGraph.intersectionForm_self`: the self-pairing as a quadratic form, the
  framing-weighted sum of squares plus the adjacency cross terms.
* `TauCeti.PlumbingGraph.IsNegativeDefinite.weight_neg`: a negative-definite plumbing has every
  framing negative.
* `TauCeti.PlumbingGraph.intersectionForm_self_add`: a symmetric-pairing expansion for the
  intersection form on a sum.
* `TauCeti.PlumbingGraph.intersectionForm_self_smul`: the self-pairing scales by the square of the
  multiplier.
* `TauCeti.PlumbingGraph.intersectionForm_single_right_eq_mulVec_apply`: pairing against a basis
  sphere
  reads off one coordinate of the matrix-vector product.
* `TauCeti.PlumbingGraph.intersectionForm_adjugate_mulVec_right`: pairing against the covector
  `adjugate A *ᵥ k` computes `det A` times the linear form `⟪k, -⟫`.

## References

This supplies the first prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`,
Lane L ("lattice homology"), whose opening data is "plumbing trees/graphs and their lattices …
from lattice points and weight functions … finite combinatorics plus bilinear forms". The
intersection form of a plumbing graph follows Némethi,
[arXiv:0709.0841](https://arxiv.org/abs/0709.0841), after Ozsváth--Szabó,
[arXiv:math/0203265](https://arxiv.org/abs/math/0203265).
-/

public section

namespace TauCeti

/-- A plumbing graph: a simple graph together with an integer weight on each vertex.

The vertices are the plumbed spheres, the edges record which pairs of spheres are plumbed
together, and `weight v` is the self-intersection number (the framing / Euler number) of the
sphere `v`. The combinatorics is modelled by a `SimpleGraph`: at most one edge between two
distinct vertices, and no self-loops. The finite lattice API is provided by declarations that
assume `[Fintype V]`. -/
structure PlumbingGraph (V : Type*) where
  /-- The underlying simple graph: an edge for each pair of plumbed spheres. -/
  toSimpleGraph : SimpleGraph V
  /-- Adjacency in the underlying graph is decidable, so the adjacency matrix is available. -/
  decidableAdj : DecidableRel toSimpleGraph.Adj
  /-- The framing (self-intersection / Euler number) of each sphere. -/
  weight : V → ℤ

attribute [instance] PlumbingGraph.decidableAdj

namespace PlumbingGraph

variable {V : Type*} [DecidableEq V] (P : PlumbingGraph V)

/-- The intersection matrix of a plumbing graph: the framing on the diagonal and the adjacency
indicator off the diagonal.

This is the matrix of the intersection form of the plumbed four-manifold in the basis of
spheres: a sphere meets itself in its framing and meets a plumbed neighbour once. -/
def intersectionMatrix : Matrix V V ℤ :=
  Matrix.diagonal P.weight + P.toSimpleGraph.adjMatrix ℤ

/-- The entry of the intersection matrix: the framing when on the diagonal plus one for each
adjacency. -/
theorem intersectionMatrix_apply (i j : V) :
    P.intersectionMatrix i j =
      (if i = j then P.weight i else 0) + (if P.toSimpleGraph.Adj i j then 1 else 0) := by
  simp only [intersectionMatrix, Matrix.add_apply, Matrix.diagonal_apply,
    SimpleGraph.adjMatrix_apply]

/-- The diagonal entry of the intersection matrix is the framing: a sphere has no self-loop, so
the adjacency term vanishes. -/
@[simp]
theorem intersectionMatrix_diag (i : V) : P.intersectionMatrix i i = P.weight i := by
  rw [intersectionMatrix_apply, ite_eq_left rfl, ite_eq_right (P.toSimpleGraph.irrefl), add_zero]

/-- Off the diagonal the intersection matrix is the adjacency indicator. -/
theorem intersectionMatrix_apply_of_ne {i j : V} (h : i ≠ j) :
    P.intersectionMatrix i j = if P.toSimpleGraph.Adj i j then 1 else 0 := by
  rw [intersectionMatrix_apply, ite_eq_right h, zero_add]

/-- Two plumbed spheres meet once: an adjacency contributes the entry one. -/
theorem intersectionMatrix_of_adj {i j : V} (h : P.toSimpleGraph.Adj i j) :
    P.intersectionMatrix i j = 1 := by
  rw [P.intersectionMatrix_apply_of_ne h.ne, ite_eq_left h]

/-- Distinct non-adjacent spheres are disjoint: the entry is zero. -/
theorem intersectionMatrix_of_not_adj {i j : V} (hij : i ≠ j) (h : ¬ P.toSimpleGraph.Adj i j) :
    P.intersectionMatrix i j = 0 := by
  rw [P.intersectionMatrix_apply_of_ne hij, ite_eq_right h]

/-- The intersection matrix is symmetric: the diagonal framing matrix and the adjacency matrix
are each symmetric. -/
theorem intersectionMatrix_isSymm : P.intersectionMatrix.IsSymm :=
  (Matrix.isSymm_diagonal P.weight).add
    (SimpleGraph.isSymm_adjMatrix (α := ℤ) P.toSimpleGraph)

/-- A plumbing graph is **negative definite** when its intersection matrix is negative
definite, equivalently when the negated intersection matrix is positive definite. For finite
plumbed three-manifolds this is the standing hypothesis under which lattice homology computes
the Heegaard Floer invariant. -/
def IsNegativeDefinite : Prop :=
  (-P.intersectionMatrix).PosDef

/-- The defining matrix characterization of a negative-definite plumbing graph. -/
@[grind =]
theorem isNegativeDefinite_iff : P.IsNegativeDefinite ↔ (-P.intersectionMatrix).PosDef :=
  Iff.rfl

/-- A negative-definite plumbing graph has every framing negative: a diagonal entry of the
positive-definite negated intersection matrix is the negated framing. -/
theorem IsNegativeDefinite.weight_neg (h : P.IsNegativeDefinite) (i : V) : P.weight i < 0 := by
  have key : 0 < (-P.intersectionMatrix) i i := h.diag_pos
  rw [Matrix.neg_apply, intersectionMatrix_diag] at key
  linarith

section Form

variable [Fintype V]

/-- The intersection form of a plumbing graph: the symmetric `ℤ`-bilinear form on `V → ℤ` with
matrix `intersectionMatrix`. -/
noncomputable def intersectionForm : LinearMap.BilinForm ℤ (V → ℤ) :=
  Matrix.toBilin' P.intersectionMatrix

/-- The intersection form expanded as a double sum over the intersection matrix entries. -/
theorem intersectionForm_apply (x y : V → ℤ) :
    P.intersectionForm x y = ∑ i, ∑ j, x i * P.intersectionMatrix i j * y j :=
  Matrix.toBilin'_apply _ x y

/-- The intersection form pairs the basis sphere classes by the intersection matrix entries. -/
@[simp]
theorem intersectionForm_single (i j : V) :
    P.intersectionForm (Pi.single i 1) (Pi.single j 1) = P.intersectionMatrix i j :=
  Matrix.toBilin'_single _ i j

/-- The intersection form is symmetric. -/
theorem intersectionForm_isSymm : P.intersectionForm.IsSymm :=
  Matrix.isSymm_toBilin'_iff_isSymm.mpr P.intersectionMatrix_isSymm

/-- The intersection form on a sum expands by the symmetric polarization: the cross term appears
twice because the form is symmetric. -/
theorem intersectionForm_self_add (x y : V → ℤ) :
    P.intersectionForm (x + y) (x + y) =
      P.intersectionForm x x + 2 * P.intersectionForm x y + P.intersectionForm y y :=
  by
    simp only [map_add, LinearMap.add_apply]
    rw [P.intersectionForm_isSymm.eq y x]
    ring

/-- The self-pairing of a rescaled lattice point scales by the square of the multiplier: the
intersection form is quadratic along every ray through the origin. -/
theorem intersectionForm_self_smul (c : ℤ) (x : V → ℤ) :
    P.intersectionForm (c • x) (c • x) = c ^ 2 * P.intersectionForm x x := by
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- The intersection pairing of a lattice point against a basis sphere is the corresponding column
sum of the intersection matrix. -/
theorem intersectionForm_single_right (x : V → ℤ) (v : V) :
    P.intersectionForm x (Pi.single v 1) = ∑ i, x i * P.intersectionMatrix i v := by
  rw [intersectionForm_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single v
    (fun j _ hj => by rw [Pi.single_eq_of_ne hj, mul_zero])
    (fun hv => absurd (Finset.mem_univ v) hv), Pi.single_eq_same, mul_one]

/-- The linear pairing of the covector `A m` against a lattice point `x` is the intersection
pairing `A(x, m)`: summing `intersectionMatrix.mulVec m` against `x` is the dot product
`(A m) ⬝ᵥ x`, which the symmetry of the dot product turns into the bilinear form `A(x, m)`. -/
theorem sum_intersectionMatrix_mulVec_mul (m x : V → ℤ) :
    ∑ v, (P.intersectionMatrix.mulVec m) v * x v = P.intersectionForm x m := by
  rw [intersectionForm, Matrix.toBilin'_apply']
  exact dotProduct_comm _ _

/-- The intersection pairing of a lattice point against a basis sphere is the corresponding
coordinate of the matrix-vector product `A x`: this is how a single coordinate of `A x` is read
off as a pairing, so that facts about the form transfer to the coordinates. -/
theorem intersectionForm_single_right_eq_mulVec_apply (x : V → ℤ) (v : V) :
    P.intersectionForm x (Pi.single v 1) = P.intersectionMatrix.mulVec x v := by
  rw [P.intersectionForm_single_right x v, Matrix.mulVec_apply_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [P.intersectionMatrix_isSymm.apply i v, mul_comm]

/-- Pairing a lattice point against the covector `adjugate A *ᵥ k` computes `det A` times the
linear form `⟪k, -⟫`.

This is the integral substitute for "`k` is `A` applied to a rational vector": multiplying by the
adjugate clears the denominators, at the cost of the factor `det A`. -/
theorem intersectionForm_adjugate_mulVec_right (k x : V → ℤ) :
    P.intersectionForm x (P.intersectionMatrix.adjugate.mulVec k) =
      P.intersectionMatrix.det * ∑ v, k v * x v := by
  rw [← P.sum_intersectionMatrix_mulVec_mul (P.intersectionMatrix.adjugate.mulVec k) x]
  have hmul : P.intersectionMatrix.mulVec (P.intersectionMatrix.adjugate.mulVec k) =
      P.intersectionMatrix.det • k := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [hmul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun v _ => by
    rw [Pi.smul_apply, smul_eq_mul, mul_assoc]

/-- The intersection pairing of a lattice point against a finite sum of basis spheres, as a sum of
the individual column sums. -/
theorem intersectionForm_sum_single_right (x : V → ℤ) (S : Finset V) :
    P.intersectionForm x (∑ v ∈ S, Pi.single v 1) =
      ∑ v ∈ S, ∑ i, x i * P.intersectionMatrix i v := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun v _ => P.intersectionForm_single_right x v

/-- The self-pairing of a finite sum of basis spheres is the double sum of the intersection-matrix
entries over the chosen directions. -/
theorem intersectionForm_sum_single_self (S : Finset V) :
    P.intersectionForm (∑ v ∈ S, Pi.single v 1) (∑ w ∈ S, Pi.single w 1) =
      ∑ v ∈ S, ∑ w ∈ S, P.intersectionMatrix v w := by
  rw [map_sum P.intersectionForm, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [map_sum]
  exact Finset.sum_congr rfl fun w _ => P.intersectionForm_single v w

/-- The intersection form expanded into its framing contribution and adjacency contribution. -/
theorem intersectionForm_apply_weight_add_adj (x y : V → ℤ) :
    P.intersectionForm x y =
      (∑ i, P.weight i * x i * y i) +
        ∑ i, ∑ j, if P.toSimpleGraph.Adj i j then x i * y j else 0 := by
  rw [intersectionForm_apply]
  have hsplit : ∀ i j : V, x i * P.intersectionMatrix i j * y j =
      x i * Matrix.diagonal P.weight i j * y j +
        x i * (P.toSimpleGraph.adjMatrix ℤ) i j * y j := by
    intro i j
    rw [intersectionMatrix, Matrix.add_apply]; ring
  simp_rw [hsplit, Finset.sum_add_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · rw [Matrix.diagonal_apply_eq]; ring
    · intro j _ hj
      rw [Matrix.diagonal_apply_ne _ (Ne.symm hj)]; ring
    · intro hi; exact absurd (Finset.mem_univ i) hi
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [SimpleGraph.adjMatrix_apply]
    split_ifs <;> ring

/-- The intersection form as a quadratic form: its value on a single class is the
framing-weighted sum of squares together with the adjacency cross terms. -/
theorem intersectionForm_self (x : V → ℤ) :
    P.intersectionForm x x =
      (∑ i, P.weight i * x i ^ 2) +
        ∑ i, ∑ j, if P.toSimpleGraph.Adj i j then x i * x j else 0 := by
  rw [intersectionForm_apply_weight_add_adj]
  congr 1
  refine Finset.sum_congr rfl fun i _ => by ring

end Form

end PlumbingGraph

/-- The two-vertex plumbing with a single edge and both framings `-2`: the `A₂` plumbing, whose
intersection form is the negative of the `A₂` Cartan matrix. A self-validating example for the
entry formulas. -/
def a2Plumbing : PlumbingGraph (Fin 2) where
  toSimpleGraph := ⊤
  decidableAdj := inferInstance
  weight := fun _ => -2

/-- The intersection matrix of the `A₂` plumbing is the standard `[-2, 1; 1, -2]` matrix. -/
@[simp]
theorem a2Plumbing_intersectionMatrix :
    a2Plumbing.intersectionMatrix = !![(-2 : ℤ), 1; 1, -2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [a2Plumbing, PlumbingGraph.intersectionMatrix_apply, SimpleGraph.top_adj]

end TauCeti

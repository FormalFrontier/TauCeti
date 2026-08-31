/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import TauCeti.KnotTheory.Grid.Differential.Square.Support
public import TauCeti.KnotTheory.Grid.Rectangle.Swap

/-!
# Two-step rectangle decompositions

A two-step term in the square of the grid differential consists of a rectangle from `x` to an
intermediate grid state and a second rectangle from that state to `z`. This file packages such a
factorization as `GridRectangleDecomposition`, the shared object on which the disjoint,
overlapping and annular cases of the square-zero argument all operate.

Such a factorization is determined by the ordered side columns of its two rectangles: the
intermediate state is the source with the first pair of columns swapped, and an oriented rectangle
between two given states is determined by its side columns.

## Main definitions

* `TauCeti.GridRectangleDecomposition`: two composable oriented grid rectangles.
* `TauCeti.GridRectangleDecomposition.decompositionsOf`: composable pairs drawn from any family
  of finite rectangle sets.

## Main results

* `TauCeti.GridRectangleDecomposition.ext`: a decomposition is determined by the ordered side
  columns of its two rectangles.
* `TauCeti.GridRectangleDecomposition.orderedSideColumns_injective`: the same statement as
  injectivity of the ordered quadruple of side columns.
* `TauCeti.GridRectangleDecomposition.target_apply_of_notMem_sideColumns`: away from the four
  side columns the target of a decomposition agrees with its source.
* `TauCeti.GridRectangleDecomposition.target_mem_twoStepColumnSwapNeighbors`: the target of a
  decomposition is reached from its source by two nontrivial column transpositions.

## References

This supplies the shared two-step bookkeeping for
`TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.3, "The complexes and `∂² = 0`".
The decomposition pairing follows Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*,
Chapter 4.6.
-/

public section

namespace TauCeti

/-- A decomposition of a two-step rectangle domain from `x` to `z` through an intermediate grid
state. -/
structure GridRectangleDecomposition {n : ℕ} (x z : GridState n) where
  /-- The grid state between the two rectangle moves. -/
  middle : GridState n
  /-- The first oriented rectangle, from the source to the intermediate state. -/
  first : GridRectangleBetween x middle
  /-- The second oriented rectangle, from the intermediate state to the target. -/
  second : GridRectangleBetween middle z

namespace GridRectangleDecomposition

variable {n : ℕ} {x z : GridState n}

/-- Two rectangle decompositions are equal when their ordered side columns agree: the first pair
already determines the intermediate state. -/
@[ext]
theorem ext {D E : GridRectangleDecomposition x z}
    (hfirstLeft : D.first.left = E.first.left)
    (hfirstRight : D.first.right = E.first.right)
    (hsecondLeft : D.second.left = E.second.left)
    (hsecondRight : D.second.right = E.second.right) : D = E := by
  have hmiddle : D.middle = E.middle := by
    rw [D.first.target_eq_swapColumns, hfirstLeft, hfirstRight,
      ← E.first.target_eq_swapColumns]
  cases D with
  | mk Dmiddle Dfirst Dsecond =>
      cases E with
      | mk Emiddle Efirst Esecond =>
          dsimp only at hmiddle
          subst Emiddle
          have hfirst : Dfirst = Efirst :=
            GridRectangleBetween.eq_of_sides hfirstLeft hfirstRight
          subst Efirst
          have hsecond : Dsecond = Esecond :=
            GridRectangleBetween.eq_of_sides hsecondLeft hsecondRight
          subst Esecond
          rfl

/-- A two-step rectangle decomposition is determined by the ordered quadruple of side columns of
its two rectangles. -/
theorem orderedSideColumns_injective (x z : GridState n) :
    Function.Injective fun D : GridRectangleDecomposition x z =>
      (D.first.left, D.first.right, D.second.left, D.second.right) := by
  intro D E h
  simp only [Prod.mk.injEq] at h
  exact ext h.1 h.2.1 h.2.2.1 h.2.2.2

/-- Two-step rectangle decompositions between fixed states have decidable equality: such a
decomposition is determined by its four side columns. -/
instance : DecidableEq (GridRectangleDecomposition x z) :=
  (orderedSideColumns_injective x z).decidableEq

/-- Away from the four side columns of a two-step decomposition, its target state agrees with its
source state: neither rectangle moves such a column. -/
theorem target_apply_of_notMem_sideColumns (D : GridRectangleDecomposition x z) {c : Fin n}
    (h₁ : c ∉ D.first.sideColumns) (h₂ : c ∉ D.second.sideColumns) : z c = x c := by
  rw [D.first.mem_sideColumns] at h₁
  rw [D.second.mem_sideColumns] at h₂
  rw [not_or] at h₁ h₂
  rw [D.second.map_of_ne c h₂.1 h₂.2, D.first.map_of_ne c h₁.1 h₁.2]

/-- The target of a two-step rectangle decomposition is a two-step column-swap neighbour of its
source: each of the two rectangles transposes its pair of distinct side columns. -/
theorem target_mem_twoStepColumnSwapNeighbors (D : GridRectangleDecomposition x z) :
    z ∈ x.twoStepColumnSwapNeighbors :=
  GridState.mem_twoStepColumnSwapNeighbors.mpr
    ⟨D.middle,
      GridState.mem_columnSwapNeighbors.mpr
        ⟨D.first.left, D.first.right, D.first.left_ne_right, D.first.target_eq_swapColumns⟩,
      GridState.mem_columnSwapNeighbors.mpr
        ⟨D.second.left, D.second.right, D.second.left_ne_right, D.second.target_eq_swapColumns⟩⟩

private def decompositionSigmaEquiv (x z : GridState n) :
    GridRectangleDecomposition x z ≃
      (Σ y : GridState n,
        Σ _first : GridRectangleBetween x y, GridRectangleBetween y z) where
  toFun D := ⟨D.middle, D.first, D.second⟩
  invFun D := ⟨D.1, D.2.1, D.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The finite set of two-step decompositions whose two rectangles belong to a prescribed family
of finite rectangle sets. -/
noncomputable def decompositionsOf
    (S : ∀ u v : GridState n, Finset (GridRectangleBetween u v))
    (x z : GridState n) : Finset (GridRectangleDecomposition x z) :=
  (((Finset.univ : Finset (GridState n)).sigma fun y =>
      (S x y).sigma fun _first => S y z).map
    (decompositionSigmaEquiv x z).symm.toEmbedding)

/-- A decomposition belongs to `decompositionsOf S` exactly when each rectangle belongs to the
corresponding set in `S`. -/
@[simp]
theorem mem_decompositionsOf
    (S : ∀ u v : GridState n, Finset (GridRectangleBetween u v))
    (x z : GridState n) (D : GridRectangleDecomposition x z) :
    D ∈ decompositionsOf S x z ↔
      D.first ∈ S x D.middle ∧ D.second ∈ S D.middle z := by
  classical
  simp [decompositionsOf, decompositionSigmaEquiv]

/-- The cardinality of `decompositionsOf S x z` is the sum, over intermediate states, of the
product of the two rectangle-set cardinalities. -/
theorem card_decompositionsOf
    (S : ∀ u v : GridState n, Finset (GridRectangleBetween u v))
    (x z : GridState n) :
    (decompositionsOf S x z).card = ∑ y, (S x y).card * (S y z).card := by
  classical
  simp [decompositionsOf, Finset.card_sigma]

/-- Summing over `decompositionsOf` is the corresponding iterated sum over the intermediate state
and the two selected rectangles. -/
theorem sum_decompositionsOf {M : Type*} [AddCommMonoid M]
    (S : ∀ u v : GridState n, Finset (GridRectangleBetween u v))
    (x z : GridState n)
    (w : ∀ y, GridRectangleBetween x y → GridRectangleBetween y z → M) :
    ∑ D ∈ decompositionsOf S x z, w D.middle D.first D.second =
      ∑ y, ∑ r₁ ∈ S x y, ∑ r₂ ∈ S y z, w y r₁ r₂ := by
  classical
  simp [decompositionsOf, decompositionSigmaEquiv, Finset.sum_sigma']

end GridRectangleDecomposition

end TauCeti

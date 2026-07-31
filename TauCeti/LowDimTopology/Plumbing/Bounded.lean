/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LowDimTopology.Plumbing.ChainComplex

/-!
# Boundedness of the lattice chain complex

The cubical degree of a plumbing-lattice generator is the cardinality of its finite set of
directions. For a plumbing graph on `V`, this degree is therefore at most `Fintype.card V`.
The grading-level bounds are established in `Grading.lean`. This file turns them into the
corresponding categorical facts about Némethi's lattice complex: its chain objects are zero
precisely above the number of vertices, the complex is exact there, and its homology vanishes in
every degree above that bound.

The characterization of the zero chain groups is sharp. In every degree at most
`Fintype.card V`, a subset of the vertex set of that cardinality supplies a cube generator and
hence a nonzero chain. This rules out obtaining boundedness from a degenerate chain model and
makes the result useful when reducing explicit lattice-homology computations to finitely many
cubical degrees.

## Main results

* `TauCeti.PlumbingGraph.isZero_latticeChainComplex_X_iff_card_lt`: the categorical chain object
  has the same sharp vanishing range.
* `TauCeti.PlumbingGraph.isZero_latticeChainHomology_of_card_lt`: lattice homology vanishes
  above the number of plumbing vertices.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane L, which asks for
Némethi's lattice homology from lattice points and weight functions, including computations for
explicit plumbings. The cubical complex and its grading follow A. Némethi,
[arXiv:0709.0841](https://arxiv.org/abs/0709.0841), Section 3.
-/

public section

namespace TauCeti

open CategoryTheory Limits

namespace PlumbingGraph

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- A chain object in the cubically graded lattice complex is zero exactly above the number of
plumbing vertices. -/
theorem isZero_latticeChainComplex_X_iff_card_lt
    (P : PlumbingGraph V) (k : P.characteristicVectors) (q : ℕ) :
    IsZero ((P.latticeChainComplex k).X q) ↔ Fintype.card V < q := by
  rw [P.latticeChainComplex_X k q, ModuleCat.isZero_iff_subsingleton,
    Submodule.subsingleton_iff_eq_bot, PlumbingChain.degreePart_eq_bot_iff_card_lt]

/-- The cubically graded lattice complex is exact in every degree above the number of plumbing
vertices because its chain object there is zero. -/
theorem latticeChainComplex_exactAt_of_card_lt
    (P : PlumbingGraph V) (k : P.characteristicVectors) (q : ℕ)
    (hq : Fintype.card V < q) :
    (P.latticeChainComplex k).ExactAt q :=
  HomologicalComplex.ExactAt.of_isZero
    ((P.isZero_latticeChainComplex_X_iff_card_lt k q).mpr hq)

/-- Lattice homology vanishes in every cubical degree above the number of plumbing vertices. -/
theorem isZero_latticeChainHomology_of_card_lt
    (P : PlumbingGraph V) (k : P.characteristicVectors) (q : ℕ)
    (hq : Fintype.card V < q) :
    IsZero (P.latticeChainHomology k q) := by
  rw [P.latticeChainHomology_def k q]
  exact (P.latticeChainComplex_exactAt_of_card_lt k q hq).isZero_homology

end PlumbingGraph

end TauCeti

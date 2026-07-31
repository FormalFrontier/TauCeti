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
This file turns that elementary bound into the corresponding structural facts about Némethi's
lattice complex: its degree pieces are zero precisely above the number of vertices, its chain
maps with source above that range are zero, and its homology vanishes in every degree above that
bound.

The characterization of the zero chain groups is sharp. In every degree at most
`Fintype.card V`, a subset of the vertex set of that cardinality supplies a cube generator and
hence a nonzero chain. This rules out obtaining boundedness from a degenerate chain model and
makes the result useful when reducing explicit lattice-homology computations to finitely many
cubical degrees.

## Main results

* `TauCeti.PlumbingChain.degreePart_eq_bot_iff_card_lt`: the degree-`q` chain group is zero
  exactly when the plumbing graph has fewer than `q` vertices.
* `TauCeti.PlumbingGraph.latticeDifferentialDegree_eq_zero_of_card_le`: no differential leaves
  an impossible source degree above the number of vertices.
* `TauCeti.PlumbingGraph.latticeChainComplex_X_isZero_iff_card_lt`: the categorical chain object
  has the same sharp vanishing range.
* `TauCeti.PlumbingGraph.latticeChainHomology_isZero_of_card_lt`: lattice homology vanishes
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

namespace PlumbingChain

variable (V : Type*) [Fintype V]

/-- The degree-`q` part of the plumbing chain module is zero exactly when `q` is larger than the
number of plumbing vertices. -/
theorem degreePart_eq_bot_iff_card_lt (q : ℕ) :
    degreePart V q = ⊥ ↔ Fintype.card V < q := by
  classical
  constructor
  · intro hzero
    by_contra hq
    obtain ⟨S, _hSsub, hScard⟩ :=
      Finset.exists_subset_card_eq (s := (Finset.univ : Finset V)) (Nat.le_of_not_gt hq)
    let C : PlumbingCube V := { base := 0, directions := S }
    have hsingle : Finsupp.single C (1 : PlumbingCoefficient) ∈ degreePart V q :=
      single_mem_degreePart V C 1 (by simpa [C] using hScard)
    rw [hzero, Submodule.mem_bot] at hsingle
    exact one_ne_zero (Finsupp.single_eq_zero.mp hsingle)
  · intro hq
    refine le_antisymm ?_ bot_le
    intro c hc
    rw [mem_degreePart] at hc
    apply Finsupp.ext
    intro C
    by_cases hC : C ∈ c.support
    · have hdim := hc C hC
      have hle : C.dimension ≤ Fintype.card V := C.dimension_le_card
      omega
    · exact Finsupp.notMem_support_iff.mp hC

/-- The degree-`q` part of the plumbing chain module is nonzero exactly in the possible cubical
range. -/
theorem degreePart_ne_bot_iff_le_card (q : ℕ) :
    degreePart V q ≠ ⊥ ↔ q ≤ Fintype.card V := by
  rw [ne_eq, degreePart_eq_bot_iff_card_lt]
  omega

end PlumbingChain

namespace PlumbingGraph

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- The degreewise differential is zero once its source degree `q + 1` lies above the number of
plumbing vertices. -/
theorem latticeDifferentialDegree_eq_zero_of_card_le
    (P : PlumbingGraph V) (k : P.characteristicVectors) (q : ℕ)
    (hq : Fintype.card V ≤ q) :
    P.latticeDifferentialDegree k q = 0 := by
  have hsource :=
    (PlumbingChain.degreePart_eq_bot_iff_card_lt V (q + 1)).mpr (Nat.lt_succ_of_le hq)
  haveI : Subsingleton (PlumbingChain.degreePart V (q + 1)) := by
    rw [hsource]
    infer_instance
  ext c
  rw [Subsingleton.elim c 0]
  simp

/-- The differential from the first impossible cubical degree into the top possible degree is
zero. -/
@[simp]
theorem latticeDifferentialDegree_card_eq_zero
    (P : PlumbingGraph V) (k : P.characteristicVectors) :
    P.latticeDifferentialDegree k (Fintype.card V) = 0 :=
  P.latticeDifferentialDegree_eq_zero_of_card_le k _ le_rfl

/-- A chain object in the cubically graded lattice complex is zero exactly above the number of
plumbing vertices. -/
theorem latticeChainComplex_X_isZero_iff_card_lt
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
  ShortComplex.exact_of_isZero_X₂ _
    ((P.latticeChainComplex_X_isZero_iff_card_lt k q).mpr hq)

/-- Lattice homology vanishes in every cubical degree above the number of plumbing vertices. -/
theorem latticeChainHomology_isZero_of_card_lt
    (P : PlumbingGraph V) (k : P.characteristicVectors) (q : ℕ)
    (hq : Fintype.card V < q) :
    IsZero (P.latticeChainHomology k q) := by
  rw [P.latticeChainHomology_def k q]
  exact (P.latticeChainComplex_exactAt_of_card_lt k q hq).isZero_homology

end PlumbingGraph

end TauCeti

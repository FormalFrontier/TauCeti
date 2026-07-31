/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.LowDimTopology.Plumbing.Grading

/-!
# The cubically graded lattice chain complex

This file assembles the cubical-degree pieces of the plumbing chain module into an
`ℕ`-indexed chain complex. In degree `q` its object is the free submodule supported on
`q`-dimensional plumbing cubes, and its differential is the restriction of Némethi's weighted
lattice differential from degree `q + 1` to degree `q`.

The degreewise square-zero result from `Grading.lean` is exactly the compatibility required by
Mathlib's `ChainComplex.of`. Consequently the standard homology API for homological complexes is
available without introducing a parallel quotient construction. The homology in cubical degree
`q` is named `latticeHomologyDegree`.

## Main definitions

* `TauCeti.PlumbingGraph.latticeChainComplex`: the cubically graded lattice chain complex over
  `𝔽₂[U]`.
* `TauCeti.PlumbingGraph.latticeHomologyDegree`: its homology in a specified cubical degree.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane L, which asks for
Némethi's lattice homology `ℍ⁻` as a graded `ℤ[U]`-module built from lattice points and weight
functions. This is the roadmap's characteristic-two first stage. The cubical chain complex is
the complex of A. Némethi, [arXiv:0709.0841](https://arxiv.org/abs/0709.0841), Section 3.
-/

public section

namespace TauCeti

open CategoryTheory

namespace PlumbingGraph

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- The cubically graded lattice chain complex of a plumbing graph and a characteristic
covector. Its degree-`q` object consists of chains supported on `q`-dimensional cubes. -/
noncomputable def latticeChainComplex
    (P : PlumbingGraph V) (k : P.characteristicVectors) :
    ChainComplex (ModuleCat PlumbingCoefficient) ℕ :=
  ChainComplex.of
    (fun q => ModuleCat.of PlumbingCoefficient (PlumbingChain.degreePart V q))
    (fun q => ModuleCat.ofHom (R := PlumbingCoefficient) (P.latticeDifferentialDegree k q))
    fun q => by
      rw [← ModuleCat.ofHom_comp, P.latticeDifferentialDegree_comp k q,
        ModuleCat.ofHom_zero]

/-- The object in cubical degree `q` is the submodule of chains supported on
`q`-dimensional cubes. -/
@[simp]
theorem latticeChainComplex_X
    (P : PlumbingGraph V) (k : P.characteristicVectors) (q : ℕ) :
    (P.latticeChainComplex k).X q =
      ModuleCat.of PlumbingCoefficient (PlumbingChain.degreePart V q) :=
  (rfl)

/-- The differential from cubical degree `q + 1` to degree `q` is the restriction of the total
lattice differential. -/
@[simp]
theorem latticeChainComplex_d
    (P : PlumbingGraph V) (k : P.characteristicVectors) (q : ℕ) :
    HEq ((P.latticeChainComplex k).d (q + 1) q)
      (ModuleCat.ofHom (P.latticeDifferentialDegree k q) :
        ModuleCat.of PlumbingCoefficient (PlumbingChain.degreePart V (q + 1)) ⟶
          ModuleCat.of PlumbingCoefficient (PlumbingChain.degreePart V q)) :=
  by
    rw [latticeChainComplex]
    exact heq_of_eq (ChainComplex.of_d
      (fun r => ModuleCat.of PlumbingCoefficient (PlumbingChain.degreePart V r))
      (fun r => ModuleCat.ofHom (R := PlumbingCoefficient) (P.latticeDifferentialDegree k r))
      q)

/-- The characteristic-two lattice homology in cubical degree `q`, obtained from Mathlib's
canonical homology object of the graded lattice chain complex. -/
noncomputable def latticeHomologyDegree
    (P : PlumbingGraph V) (k : P.characteristicVectors) (q : ℕ) :
    ModuleCat PlumbingCoefficient :=
  (P.latticeChainComplex k).homology q

/-- Degreewise lattice homology is the canonical homology object of the cubically graded lattice
chain complex. -/
@[simp]
theorem latticeHomologyDegree_def
    (P : PlumbingGraph V) (k : P.characteristicVectors) (q : ℕ) :
    P.latticeHomologyDegree k q = (P.latticeChainComplex k).homology q :=
  (rfl)

end PlumbingGraph

end TauCeti

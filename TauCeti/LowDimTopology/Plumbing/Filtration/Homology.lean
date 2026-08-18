/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ShortComplex.Colimit
public import TauCeti.LowDimTopology.Plumbing.Filtration.Colimit

/-!
# The lattice-homology weight filtration

The characteristic-weight sublevel complexes form a filtered diagram whose colimit is the full
lattice chain complex. This file passes that presentation through homology: in every cubical degree,
the homology of the full complex is the filtered colimit of the sublevel homology modules. When the
plumbing is negative definite, the sublevel chain groups are finitely generated, so this result is
the bridge from finite sublevel calculations to the untruncated invariant.

The proof uses Mathlib's AB5 theorem for module categories. Exactness of filtered colimits makes
homology commute with the integer-indexed colimit. The definitions work for vertex types in any
universe; the final colimit theorem requires a universe-zero vertex type because Mathlib's AB5
instance for `ModuleCat.{u} R` requires the ring `R` to lie in the same universe `u`.

## Main definitions

* `TauCeti.PlumbingGraph.latticeWeightSublevelHomology`: homology of one weight sublevel.
* `TauCeti.PlumbingGraph.latticeWeightSublevelHomologyFunctor`: the filtered diagram of sublevel
  homology modules.
* `TauCeti.PlumbingGraph.latticeWeightSublevelHomologyCocone`: the canonical cocone into full
  lattice homology.
* `TauCeti.PlumbingGraph.latticeWeightSublevelHomologyCoconeIsColimit`: full lattice homology is
  the colimit of the sublevel homologies.

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane L, which asks for
Némethi's lattice homology from lattice points and weight functions and for computations of
concrete negative-definite plumbings. The weight-sublevel presentation follows A. Némethi,
[arXiv:0709.0841](https://arxiv.org/abs/0709.0841), Section 3.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

namespace PlumbingGraph

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- The homology in cubical degree `q` of the characteristic-weight sublevel complex at level
`N`. Each chain group of this complex is finitely generated when the plumbing is negative
definite. -/
noncomputable def latticeWeightSublevelHomology (P : PlumbingGraph V)
    (k : P.characteristicVectors) (N : ℤ) (q : ℕ) : ModuleCat PlumbingCoefficient :=
  (P.latticeWeightSublevelComplex k N).homology q

/-- Weight-sublevel homology is the canonical homology object of the corresponding sublevel
chain complex. -/
@[simp]
theorem latticeWeightSublevelHomology_def (P : PlumbingGraph V)
    (k : P.characteristicVectors) (N : ℤ) (q : ℕ) :
    P.latticeWeightSublevelHomology k N q =
      (P.latticeWeightSublevelComplex k N).homology q :=
  (rfl)

/-- The integer-indexed diagram of characteristic-weight sublevel homology modules in cubical
degree `q`. Its transition maps are induced by the inclusions of weight sublevel complexes. -/
noncomputable def latticeWeightSublevelHomologyFunctor (P : PlumbingGraph V)
    (k : P.characteristicVectors) (q : ℕ) : Functor ℤ (ModuleCat PlumbingCoefficient) :=
  P.latticeWeightSublevelFunctor k ⋙
    HomologicalComplex.homologyFunctor (ModuleCat PlumbingCoefficient) (ComplexShape.down ℕ) q

/-- The object at level `N` of the weight-sublevel homology diagram is the homology of the
level-`N` subcomplex. -/
@[simp]
theorem latticeWeightSublevelHomologyFunctor_obj (P : PlumbingGraph V)
    (k : P.characteristicVectors) (q : ℕ) (N : ℤ) :
    (P.latticeWeightSublevelHomologyFunctor k q).obj N =
      P.latticeWeightSublevelHomology k N q := by
  rw [latticeWeightSublevelHomologyFunctor, Functor.comp_obj,
    HomologicalComplex.homologyFunctor_obj, P.latticeWeightSublevelFunctor_obj,
    latticeWeightSublevelHomology_def]

/-- The canonical cocone from weight-sublevel homology modules to the homology of the full lattice
chain complex. Its legs are the maps on homology induced by inclusion of sublevel complexes. -/
noncomputable def latticeWeightSublevelHomologyCocone (P : PlumbingGraph V)
    (k : P.characteristicVectors) (q : ℕ) :
    Cocone (P.latticeWeightSublevelHomologyFunctor k q) :=
  (HomologicalComplex.homologyFunctor (ModuleCat PlumbingCoefficient)
    (ComplexShape.down ℕ) q).mapCocone (P.latticeWeightSublevelCocone k)

/-- The point of the weight-sublevel homology cocone is the cubical-degree homology of the full
lattice chain complex. -/
@[simp]
theorem latticeWeightSublevelHomologyCocone_pt (P : PlumbingGraph V)
    (k : P.characteristicVectors) (q : ℕ) :
    (P.latticeWeightSublevelHomologyCocone k q).pt = P.latticeChainHomology k q := by
  rw [latticeWeightSublevelHomologyCocone, Functor.mapCocone_pt,
    HomologicalComplex.homologyFunctor_obj, P.latticeWeightSublevelCocone_pt,
    latticeChainHomology_def]

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Cubical-degree lattice homology is the filtered colimit of the homology modules of the
characteristic-weight sublevel complexes. The universe-zero restriction on `V` comes from the
available AB5 instance for the coefficient module category. -/
noncomputable def latticeWeightSublevelHomologyCoconeIsColimit (P : PlumbingGraph V)
    (k : P.characteristicVectors) (q : ℕ) :
    IsColimit (P.latticeWeightSublevelHomologyCocone k q) := by
  let _ := homologicalComplexHomologyFunctor_preservesColimitsOfShape
    (R := PlumbingCoefficient) (ComplexShape.down ℕ) q
  exact isColimitOfPreserves
    (HomologicalComplex.homologyFunctor (ModuleCat PlumbingCoefficient)
      (ComplexShape.down ℕ) q)
    (P.latticeWeightSublevelCoconeIsColimit k)

end PlumbingGraph

end TauCeti

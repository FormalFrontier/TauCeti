/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Topology.Homology
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import TauCeti.Topology.Algebra.Module.Quotient

/-!
# Homology in `TopModuleCat` as a concrete subquotient

Mathlib proves that `TopModuleCat R` is a `CategoryWithHomology` by exhibiting, for a short
complex `S`, the kernel `TopModuleCat.ker S.g` with its subspace topology and the cokernel
`TopModuleCat.coker` with its quotient topology as left and right homology data. On the cycles
side the resulting identification is available generically, as
`ShortComplex.isoCyclesOfIsLimit (TopModuleCat.isLimitKer S.g) : TopModuleCat.ker S.g ≅ S.cycles`;
on the homology side there is no such generic statement, so this file names it:
`ShortComplex.homologyIsoCoker` identifies `S.homology` with the honest cokernel of `S.toCycles`.
Mathlib's `ShortComplex.homologyIsoCokernelLift` is the analogous statement for the *categorical*
`cokernel`, which says nothing about which topology that object carries; the point of the
isomorphism below is that the topology is the quotient topology on a cokernel.

The consequence recorded here is that homology in `TopModuleCat R` inherits discreteness: a short
complex whose middle term is discrete has discrete cycles and discrete homology, and likewise
degreewise for a homological complex. This is what makes continuous cohomology of a discrete
representation of a compact group an isomorphism problem between *discrete* topological modules
rather than between the quotient topologies the cochain spaces happen to carry.
-/

public section

open CategoryTheory Limits

namespace CategoryTheory.ShortComplex

variable {R : Type*} [Ring R] [TopologicalSpace R] (S : ShortComplex (TopModuleCat R))

/-- The homology of a short complex of topological modules is the cokernel of `S.toCycles`,
carrying the quotient topology. -/
noncomputable def homologyIsoCoker : S.homology ≅ TopModuleCat.coker S.toCycles :=
  IsColimit.coconePointUniqueUpToIso S.homologyIsCokernel (TopModuleCat.isColimitCoker S.toCycles)

/-- `homologyIsoCoker` identifies the projection `S.homologyπ` onto homology with the projection
`TopModuleCat.cokerπ` onto the concrete cokernel. -/
@[reassoc (attr := simp)]
theorem homologyπ_comp_homologyIsoCoker_hom :
    S.homologyπ ≫ (homologyIsoCoker S).hom = TopModuleCat.cokerπ S.toCycles :=
  IsColimit.comp_coconePointUniqueUpToIso_hom S.homologyIsCokernel
    (TopModuleCat.isColimitCoker S.toCycles) WalkingParallelPair.one

/-- The form of `homologyπ_comp_homologyIsoCoker_hom` facing the inverse isomorphism: the
projection onto the concrete cokernel, followed back into homology, is `S.homologyπ`. -/
@[reassoc (attr := simp)]
theorem cokerπ_comp_homologyIsoCoker_inv :
    TopModuleCat.cokerπ S.toCycles ≫ (homologyIsoCoker S).inv = S.homologyπ :=
  IsColimit.comp_coconePointUniqueUpToIso_inv S.homologyIsCokernel
    (TopModuleCat.isColimitCoker S.toCycles) WalkingParallelPair.one

/-- The cycles of a short complex of topological modules with discrete middle term are discrete. -/
theorem discreteTopology_cycles [DiscreteTopology S.X₂] : DiscreteTopology S.cycles :=
  -- the point of the kernel fork is `TopModuleCat.ker S.g` by definition, but not syntactically,
  -- so the ascription is what lets the subtype topology be found by instance search
  let e : S.cycles ≅ TopModuleCat.ker S.g :=
    (S.isoCyclesOfIsLimit (TopModuleCat.isLimitKer S.g)).symm
  e.toContinuousLinearEquiv.toHomeomorph.isEmbedding.discreteTopology

/-- The homology of a short complex of topological modules with discrete middle term is
discrete. -/
theorem discreteTopology_homology [DiscreteTopology S.X₂] : DiscreteTopology S.homology :=
  have := discreteTopology_cycles S
  (homologyIsoCoker S).toContinuousLinearEquiv.toHomeomorph.isEmbedding.discreteTopology

end CategoryTheory.ShortComplex

namespace HomologicalComplex

variable {R : Type*} [Ring R] [TopologicalSpace R] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex (TopModuleCat R) c) (n : ι)

/-- A homological complex of topological modules that is discrete in degree `n` has discrete
cycles in degree `n`. -/
theorem discreteTopology_cycles [DiscreteTopology (K.X n)] : DiscreteTopology (K.cycles n) :=
  -- `(K.sc n).X₂` is `K.X n` by the definition of `HomologicalComplex.shortComplexFunctor`, but
  -- that is not a syntactic match, so the instance has to be handed over explicitly.
  have : DiscreteTopology (K.sc n).X₂ := ‹DiscreteTopology (K.X n)›
  ShortComplex.discreteTopology_cycles (K.sc n)

/-- A homological complex of topological modules that is discrete in degree `n` has discrete
homology in degree `n`. -/
theorem discreteTopology_homology [DiscreteTopology (K.X n)] : DiscreteTopology (K.homology n) :=
  have : DiscreteTopology (K.sc n).X₂ := ‹DiscreteTopology (K.X n)›
  ShortComplex.discreteTopology_homology (K.sc n)

end HomologicalComplex

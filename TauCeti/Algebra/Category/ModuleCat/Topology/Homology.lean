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
`TopModuleCat.coker` with its quotient topology as left and right homology data. That argument is
run inside the instance, so the resulting identifications are not available by name. This file
names them: `ShortComplex.cyclesIsoKer` identifies `S.cycles` with the honest kernel of
`S.g`, and `ShortComplex.homologyIsoCoker` identifies `S.homology` with the honest cokernel
of `S.toCycles`. Mathlib's `ShortComplex.cyclesIsoKernel` and `ShortComplex.homologyIsoCokernelLift`
are the analogous statements for the *categorical* `kernel` and `cokernel`, which say nothing about
which topology those objects carry; the point of the two isomorphisms below is that the topology is
the subspace topology on a kernel and the quotient topology on a cokernel.

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

/-- The cycles of a short complex of topological modules are the kernel of `S.g`, carrying the
subspace topology. -/
noncomputable def cyclesIsoKer : S.cycles ≅ TopModuleCat.ker S.g :=
  IsLimit.conePointUniqueUpToIso S.cyclesIsKernel (TopModuleCat.isLimitKer S.g)

@[reassoc (attr := simp)]
theorem cyclesIsoKer_hom_comp_kerι : (cyclesIsoKer S).hom ≫ TopModuleCat.kerι S.g = S.iCycles :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero

/-- The homology of a short complex of topological modules is the cokernel of `S.toCycles`,
carrying the quotient topology. -/
noncomputable def homologyIsoCoker : S.homology ≅ TopModuleCat.coker S.toCycles :=
  IsColimit.coconePointUniqueUpToIso S.homologyIsCokernel (TopModuleCat.isColimitCoker S.toCycles)

@[reassoc (attr := simp)]
theorem homologyπ_comp_homologyIsoCoker_hom :
    S.homologyπ ≫ (homologyIsoCoker S).hom = TopModuleCat.cokerπ S.toCycles :=
  IsColimit.comp_coconePointUniqueUpToIso_hom S.homologyIsCokernel
    (TopModuleCat.isColimitCoker S.toCycles) WalkingParallelPair.one

/-- The cycles of a short complex of topological modules with discrete middle term are discrete. -/
theorem discreteTopology_cycles [DiscreteTopology S.X₂] : DiscreteTopology S.cycles :=
  (cyclesIsoKer S).toContinuousLinearEquiv.toHomeomorph.isEmbedding.discreteTopology

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

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
public import TauCeti.Algebra.Category.ModuleCat.Topology.Homology
public import TauCeti.Topology.CompactOpen

/-!
# Continuous cohomology of a discrete representation of a compact group

Mathlib builds continuous cohomology as the homology of the homogeneous cochain complex, whose
terms are the invariants of the iterated coinduced representations `C(G, C(G, …, X.V))`. Over a
compact group `G` and for a representation whose underlying module is discrete, every one of those
function spaces is discrete in the compact-open topology, hence so is every term of the complex and
every subquotient of it. So `continuousCohomology n X` is a *discrete* topological module.

This matters because the topology is part of the statement. The low-degree explicit model presents
`H¹` and `H²` as quotients of subgroups of `G → M` and `G × G → M`; those carry the pointwise
topology, whose quotient is not discrete for an infinite profinite `G` (with trivial `ZMod 2`
coefficients on an infinite product of copies of `ZMod 2`, no finite set of evaluations isolates
the zero character). A comparison between the explicit model and the canonical one must therefore
say in which category it holds, and the results here are what make the canonical side of that
comparison a discrete object.

This implements the "category of the comparison" milestone of Layer 3 of the human-authored
roadmap at `TauCetiRoadmap/ProfiniteCohomology/README.md`.
-/

public section

namespace TauCeti

variable {k G : Type*} [Ring k] [TopologicalSpace k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] (X : TopRep k G) [DiscreteTopology X.V] (n : ℕ)

/-- Every term of the coinduced resolution of a discrete representation of a compact group is
discrete: it is an iterated space of continuous maps out of the compact group `G`. -/
instance discreteTopology_resolutionX : DiscreteTopology (TopRep.resolutionX X n).V := by
  induction n with
  | zero => exact ‹DiscreteTopology X.V›
  -- the successor step is `TopRep.coind₁`, whose underlying module is `C(G, -)` by definition
  | succ n ih => exact inferInstanceAs (DiscreteTopology C(G, (TopRep.resolutionX X n).V))

/-- Every term of the homogeneous cochain complex of a discrete representation of a compact group
is discrete. -/
instance discreteTopology_homogeneousCochains :
    DiscreteTopology ((TopRep.homogeneousCochains X).X n) :=
  -- degree `n` of the complex is the invariants of the shifted resolution, an additive subgroup
  -- of a discrete module; the equality holds by definition but is not a syntactic match
  inferInstanceAs (DiscreteTopology (TopRep.invariants (TopRep.resolutionX X (n + 1))))

/-- The continuous cocycles of a discrete representation of a compact group are discrete. -/
instance discreteTopology_cocycles : DiscreteTopology (ContinuousCohomology.cocycles X n) :=
  HomologicalComplex.discreteTopology_cycles _ n

/-- The continuous cohomology of a discrete representation of a compact group is discrete.

This is the statement that lets a comparison with an explicit low-degree model be phrased as an
isomorphism in `TopModuleCat k` between discrete objects rather than as an additive isomorphism
after forgetting the topology. -/
instance discreteTopology_continuousCohomology : DiscreteTopology (continuousCohomology n X) :=
  HomologicalComplex.discreteTopology_homology _ n

end TauCeti

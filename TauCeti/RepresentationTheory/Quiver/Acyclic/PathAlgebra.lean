/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Quiver.Acyclic.FinitePaths
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra

/-!
# The path algebra of an acyclic quiver

A finite quiver with finitely many arrows between any two vertices has finitely many paths when it
is acyclic, and the paths are a basis of its path algebra; so the path algebra of such a quiver is
finite-dimensional over a division ring.

This is the only place the generic path algebra of
`TauCeti.RepresentationTheory.Quiver.PathAlgebra` meets acyclicity, which is why it is a module of
its own: the path algebra itself needs nothing from the theory of acyclic quivers.

## Main results

* `TauCeti.finiteDimensional_pathAlgebra_of_isAcyclic`: the path algebra of a finite acyclic
  quiver with finite arrow types is finite-dimensional.

## References

This file implements the finite-dimensionality half of the path-algebra part of Layer 0 of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`. See Assem--Simson--
Skowroński, *Elements of the Representation Theory of Associative Algebras I*, Ch. II.
-/

public section

namespace TauCeti

open _root_.Quiver

universe u v w

/-- The path algebra of a finite acyclic quiver is finite-dimensional. -/
theorem finiteDimensional_pathAlgebra_of_isAcyclic (k : Type w) (Q : Type u) [DivisionRing k]
    [Quiver.{v} Q] [Finite Q] [∀ a b : Q, Finite (a ⟶ b)] (h : Quiver.IsAcyclic Q) :
    FiniteDimensional k (pathAlgebra k Q) :=
  letI := finite_paths_of_isAcyclic h
  module_finite_pathAlgebra k Q

end TauCeti

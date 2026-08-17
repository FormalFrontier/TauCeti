/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.D4.Basic
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Basic

/-!
# The path algebra of the `D₄` quiver

The `D₄` quiver has seven paths: the four trivial ones and the three arrows. So its path algebra
is seven-dimensional. Finite-dimensionality needs nothing specific to this quiver: it is acyclic,
so `TauCeti.finiteDimensional_pathAlgebra_of_isAcyclic` applies to it as it stands, via
`TauCeti.Quiver.D4.isAcyclic`.

## Main results

* `TauCeti.Quiver.D4.card_totalPath` and `TauCeti.Quiver.D4.finrank_pathAlgebra`: there are seven
  paths, so the path algebra is seven-dimensional.

## References

This file supplies the path algebra of the “`D₄` quiver” worked example of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`. See Derksen--Weyman, *An
Introduction to Quiver Representations*, and Assem--Simson--Skowroński, *Elements of the
Representation Theory of Associative Algebras I*, Ch. II.
-/

public section

namespace TauCeti

open _root_.Quiver

universe w

namespace Quiver.D4

/-- The `D₄` quiver has seven paths: the four trivial ones and the three arrows. -/
theorem card_totalPath : Fintype.card (Quiver.TotalPath D4) = 7 := by
  have h : Fintype.card (Quiver.TotalPath D4)
      = ∑ a : D4, ∑ b : D4, Fintype.card (Path a b) := by
    rw [Fintype.card_sigma]
    exact Finset.sum_congr rfl fun _ _ => Fintype.card_sigma
  rw [h]
  simp

/-- The path algebra of the `D₄` quiver is seven-dimensional: four trivial paths and three
arrows. -/
theorem finrank_pathAlgebra (k : Type w) [DivisionRing k] :
    Module.finrank k (pathAlgebra k D4) = 7 := by
  rw [TauCeti.finrank_pathAlgebra k D4, card_totalPath]

end Quiver.D4

end TauCeti

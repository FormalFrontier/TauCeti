/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization

/-!
# Triangulable topological spaces

A topological space is triangulable if it is homeomorphic to the geometric realization of an
abstract simplicial complex. This is deliberately weaker than carrying a combinatorial or PL
manifold structure: no link condition is imposed on the witnessing complex.

This file supplies the homeomorphism-invariance API and shows that realizations and discrete
topological spaces are triangulable.

This is the general triangulability notion fixed in layer 11 of the geometric-topology roadmap.

## Main definitions

* `IsTriangulable`: a space is homeomorphic to the realization of an abstract simplicial complex.

## Main results

* `Homeomorph.isTriangulable_iff`: triangulability is invariant under homeomorphism.
* `isTriangulable_of_discreteTopology`: every discrete space is triangulable.
-/

public section

noncomputable section

namespace TauCeti

/-- A topological space is triangulable if it is homeomorphic to the geometric realization of an
abstract simplicial complex. -/
def IsTriangulable.{v, u} (X : Type u) [TopologicalSpace X] : Prop :=
  ∃ (ι : Type v) (K : AbstractSimplicialComplex ι),
    Nonempty (AbstractSimplicialComplex.Realization K ≃ₜ X)

universe u v w

namespace AbstractSimplicialComplex

variable {ι : Type u}

/-- The geometric realization of every abstract simplicial complex is triangulable. -/
theorem isTriangulable_realization (K : AbstractSimplicialComplex ι) :
    IsTriangulable.{u} (Realization K) :=
  ⟨ι, K, ⟨Homeomorph.refl _⟩⟩

end AbstractSimplicialComplex

variable {X : Type u} {Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]

/-- Homeomorphic spaces are triangulable simultaneously. -/
theorem _root_.Homeomorph.isTriangulable_iff (e : X ≃ₜ Y) :
    IsTriangulable.{v} X ↔ IsTriangulable.{v} Y := by
  constructor
  · rintro ⟨ι, K, ⟨h⟩⟩
    exact ⟨ι, K, ⟨h.trans e⟩⟩
  · rintro ⟨ι, K, ⟨h⟩⟩
    exact ⟨ι, K, ⟨h.trans e.symm⟩⟩

/-- Every discrete topological space is triangulable, using the bottom abstract simplicial
complex on its points. -/
theorem isTriangulable_of_discreteTopology (X : Type u) [TopologicalSpace X]
    [DiscreteTopology X] : IsTriangulable.{u} X :=
  ⟨X, ⊥, ⟨AbstractSimplicialComplex.realizationBotHomeomorph⟩⟩

end TauCeti

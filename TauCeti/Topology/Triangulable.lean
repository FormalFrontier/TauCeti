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

This file supplies the homeomorphism-invariance API and checks the definition on zero-dimensional
complexes. The realization of the bottom abstract simplicial complex is discrete and canonically
homeomorphic to its vertex type, so every discrete topological space is triangulable.

This is the general triangulability notion fixed in layer 11 of the geometric-topology roadmap.

## Main definitions

* `IsTriangulable`: a space is homeomorphic to the realization of an abstract simplicial complex.
* `AbstractSimplicialComplex.realizationBotHomeomorph`: the realization of the bottom complex is
  its discrete vertex space.

## Main results

* `Homeomorph.isTriangulable_iff`: triangulability is invariant under homeomorphism.
* `isTriangulable_of_discreteTopology`: every discrete space is triangulable.
-/

public section

noncomputable section

namespace TauCeti

open Set

universe u

/-- A topological space is triangulable if it is homeomorphic to the geometric realization of an
abstract simplicial complex. The vertex type is taken in the same universe as the space. -/
def IsTriangulable (X : Type u) [TopologicalSpace X] : Prop :=
  ∃ (ι : Type u) (K : AbstractSimplicialComplex ι),
    Nonempty (AbstractSimplicialComplex.Realization K ≃ₜ X)

/-- The defining characterization of a triangulable space. -/
theorem isTriangulable_iff {X : Type u} [TopologicalSpace X] :
    IsTriangulable X ↔
      ∃ (ι : Type u) (K : AbstractSimplicialComplex ι),
        Nonempty (AbstractSimplicialComplex.Realization K ≃ₜ X) :=
  Iff.rfl

namespace AbstractSimplicialComplex

variable {ι : Type u}

/-- The vertices exhaust the realization of the bottom abstract simplicial complex. -/
theorem vertex_surjective_bot :
    Function.Surjective (vertex (⊥ : AbstractSimplicialComplex ι)) := by
  classical
  intro x
  obtain ⟨v, hv⟩ := (carrier (⊥ : AbstractSimplicialComplex ι) x).2
  refine ⟨v, Subtype.ext ?_⟩
  have hx := mem_convexHull_carrier (⊥ : AbstractSimplicialComplex ι) x
  have hx' : x.1 = Finsupp.single v 1 := by
    simpa only [hv, Finset.image_singleton, Finset.coe_singleton, convexHull_singleton,
      mem_singleton_iff] using hx
  rw [vertex_val]
  exact hx'.symm

/-- The weak topology on the realization of the bottom abstract simplicial complex is discrete. -/
instance realizationBotDiscreteTopology :
    DiscreteTopology (Realization (⊥ : AbstractSimplicialComplex ι)) := by
  classical
  rw [discreteTopology_iff_forall_isOpen]
  intro s
  rw [isOpen_iSup_iff]
  intro σ
  rw [isOpen_coinduced]
  obtain ⟨v, hv⟩ := σ.2
  haveI : Subsingleton (StandardSimplex σ.1) := by
    constructor
    intro x y
    apply Subtype.ext
    have hx : x.1 = Finsupp.single v 1 := by
      simpa only [hv, Finset.image_singleton, Finset.coe_singleton, convexHull_singleton,
        mem_singleton_iff] using x.2
    have hy : y.1 = Finsupp.single v 1 := by
      simpa only [hv, Finset.image_singleton, Finset.coe_singleton, convexHull_singleton,
        mem_singleton_iff] using y.2
    exact hx.trans hy.symm
  exact isOpen_discrete _

private noncomputable def vertexEquivBot :
    ι ≃ Realization (⊥ : AbstractSimplicialComplex ι) :=
  Equiv.ofBijective (vertex (⊥ : AbstractSimplicialComplex ι))
    ⟨vertex_injective _, vertex_surjective_bot⟩

/-- The realization of the bottom abstract simplicial complex is canonically homeomorphic to its
vertex type equipped with a discrete topology. -/
noncomputable def realizationBotHomeomorph [TopologicalSpace ι] [DiscreteTopology ι] :
    Realization (⊥ : AbstractSimplicialComplex ι) ≃ₜ ι :=
  (Homeomorph.ofDiscrete vertexEquivBot).symm

/-- Under the canonical homeomorphism for the bottom complex, the inverse sends a vertex to its
standard barycentric point. -/
@[simp]
theorem realizationBotHomeomorph_symm_apply [TopologicalSpace ι] [DiscreteTopology ι] (v : ι) :
    (realizationBotHomeomorph (ι := ι)).symm v =
      vertex (⊥ : AbstractSimplicialComplex ι) v :=
  by
    rw [realizationBotHomeomorph, Homeomorph.symm_symm]
    calc
      (Homeomorph.ofDiscrete vertexEquivBot) v = vertexEquivBot v := rfl
      _ = vertex (⊥ : AbstractSimplicialComplex ι) v :=
        Equiv.ofBijective_apply _ ⟨vertex_injective _, vertex_surjective_bot⟩ v

/-- The canonical homeomorphism sends the barycentric point of a vertex back to that vertex. -/
@[simp]
theorem realizationBotHomeomorph_apply_vertex [TopologicalSpace ι] [DiscreteTopology ι] (v : ι) :
    realizationBotHomeomorph (vertex (⊥ : AbstractSimplicialComplex ι) v) = v := by
  rw [← realizationBotHomeomorph_symm_apply]
  exact Homeomorph.apply_symm_apply _ _

/-- The geometric realization of every abstract simplicial complex is triangulable. -/
theorem isTriangulable_realization (K : AbstractSimplicialComplex ι) :
    IsTriangulable (Realization K) :=
  ⟨ι, K, ⟨Homeomorph.refl _⟩⟩

end AbstractSimplicialComplex

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- Homeomorphic spaces are triangulable simultaneously. -/
theorem _root_.Homeomorph.isTriangulable_iff (e : X ≃ₜ Y) :
    IsTriangulable X ↔ IsTriangulable Y := by
  constructor
  · rintro ⟨ι, K, ⟨h⟩⟩
    exact ⟨ι, K, ⟨h.trans e⟩⟩
  · rintro ⟨ι, K, ⟨h⟩⟩
    exact ⟨ι, K, ⟨h.trans e.symm⟩⟩

/-- Every discrete topological space is triangulable, using the bottom abstract simplicial
complex on its points. -/
theorem isTriangulable_of_discreteTopology (X : Type u) [TopologicalSpace X]
    [DiscreteTopology X] : IsTriangulable X :=
  ⟨X, ⊥, ⟨AbstractSimplicialComplex.realizationBotHomeomorph⟩⟩

end TauCeti

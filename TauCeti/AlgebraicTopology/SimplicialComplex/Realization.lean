/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Convex.SimplicialComplex.AffineIndependentUnion
public import Mathlib.Topology.UniformSpace.Real
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import TauCeti.AlgebraicTopology.SimplicialComplex.Basic

/-!
# Geometric realization of an abstract simplicial complex

This file realizes an abstract simplicial complex in the real vector space of finitely supported
functions on its vertices. A vertex `v` is represented by the coordinate vector
`Finsupp.single v 1`; the realization is the union of the convex hulls of the images of the faces.
Thus points of the realization are precisely finite barycentric combinations supported on a face.

The construction uses `Geometry.SimplicialComplex.onFinsupp` from Mathlib, which proves that the
standard coordinate vectors are affinely independent and that their convex hulls intersect along
common faces. The polyhedron carries the weak topology: the final topology for the inclusions of
all its closed simplices. This avoids a finiteness or local-finiteness hypothesis on `K`.

This is the first item of layer 11 of the geometric-topology roadmap: the polyhedron `|K|` of an
abstract simplicial complex. It is the object used in the subsequent definition of a triangulation.

## Main definitions

* `AbstractSimplicialComplex.standardGeometricComplex`: the standard geometric complex of `K`.
* `AbstractSimplicialComplex.Realization`: the topological space underlying its polyhedron.

## Main results

* `mem_standardGeometricComplex_faces_iff`: the geometric faces are exactly the coordinate images
  of the abstract faces.
* `mem_realization_iff`: a finitely supported function belongs to the polyhedron exactly when it
  lies in the convex hull of the coordinate image of some abstract face.
* `vertex`: the canonical point of the realization corresponding to a vertex.
-/

public section

noncomputable section

namespace TauCeti

open Set

namespace AbstractSimplicialComplex

variable {ι : Type*}

local instance : DecidableEq ι := Classical.decEq ι
local instance : DecidableEq ℝ := Classical.decEq ℝ

/-- The standard coordinate representative of a vertex in the free real vector space on `ι`. -/
noncomputable def vertexVector (v : ι) : ι →₀ ℝ :=
  Finsupp.single v 1

/-- The standard geometric simplicial complex associated to an abstract simplicial complex.

Each vertex is sent to its coordinate vector in `ι →₀ ℝ`. This is Mathlib's
`Geometry.SimplicialComplex.onFinsupp` construction. -/
noncomputable def standardGeometricComplex (K : AbstractSimplicialComplex ι) :
    Geometry.SimplicialComplex ℝ (ι →₀ ℝ) :=
  Geometry.SimplicialComplex.onFinsupp K.toPreAbstractSimplicialComplex

/-- The carrier of the geometric realization (polyhedron) of an abstract simplicial complex. -/
noncomputable abbrev Realization (K : AbstractSimplicialComplex ι) : Type _ :=
  (standardGeometricComplex K).space

/-- A face of an abstract simplicial complex, bundled with its membership proof. -/
abbrev Face (K : AbstractSimplicialComplex ι) := {σ : Finset ι // σ ∈ K}

/-- The closed simplex spanned by a face, in standard barycentric coordinates. -/
noncomputable abbrev FaceRealization (σ : Finset ι) : Type _ :=
  convexHull ℝ (σ.image vertexVector : Set (ι →₀ ℝ))

instance (σ : Finset ι) : TopologicalSpace (FaceRealization σ) :=
  TopologicalSpace.induced (fun x : FaceRealization σ => (x.1 : ι → ℝ)) inferInstance

/-- Include the realization of a face into the whole polyhedron. -/
noncomputable def faceInclusion (K : AbstractSimplicialComplex ι) (σ : Face K) :
    FaceRealization σ.1 → Realization K :=
  fun x => ⟨x, Geometry.SimplicialComplex.convexHull_subset_space
    (K := standardGeometricComplex K) (by exact ⟨σ.1, σ.2, rfl⟩) x.2⟩

/-- The weak topology on a realization, final with respect to all face inclusions. -/
instance (K : AbstractSimplicialComplex ι) : TopologicalSpace (Realization K) :=
  ⨆ σ : Face K, TopologicalSpace.coinduced (faceInclusion K σ) inferInstance

/-- Every face inclusion is continuous for the weak topology on the realization. -/
theorem continuous_faceInclusion (K : AbstractSimplicialComplex ι) (σ : Face K) :
    Continuous (faceInclusion K σ) :=
  continuous_iff_coinduced_le.2 (le_iSup (fun τ : Face K =>
    TopologicalSpace.coinduced (faceInclusion K τ) inferInstance) σ)

/-- The carrier of the geometric realization is the space of its standard geometric complex. -/
theorem realization_carrier (K : AbstractSimplicialComplex ι) :
    (Realization K : Type _) = (standardGeometricComplex K).space :=
  rfl

/-- A geometric face is exactly the image of an abstract face under the coordinate embedding. -/
theorem mem_standardGeometricComplex_faces_iff (K : AbstractSimplicialComplex ι)
    (τ : Finset (ι →₀ ℝ)) :
    τ ∈ (standardGeometricComplex K).faces ↔
      ∃ σ ∈ K, σ.image vertexVector = τ := by
  classical
  rfl

/-- The coordinate image of every abstract face is a face of the geometric complex. -/
theorem image_vertexVector_mem_standardGeometricComplex {K : AbstractSimplicialComplex ι}
    {σ : Finset ι} (hσ : σ ∈ K) :
    σ.image vertexVector ∈ (standardGeometricComplex K).faces :=
  (mem_standardGeometricComplex_faces_iff K _).2 ⟨σ, hσ, rfl⟩

/-- A point belongs to the standard polyhedron exactly when it lies in the convex hull of the
coordinate image of some abstract face. -/
theorem mem_realization_iff {K : AbstractSimplicialComplex ι} {x : ι →₀ ℝ} :
    x ∈ (standardGeometricComplex K).space ↔
      ∃ σ ∈ K, x ∈ convexHull ℝ (σ.image vertexVector : Set (ι →₀ ℝ)) := by
  rw [Geometry.SimplicialComplex.mem_space_iff]
  constructor
  · rintro ⟨τ, hτ, hx⟩
    obtain ⟨σ, hσ, rfl⟩ := (mem_standardGeometricComplex_faces_iff K τ).1 hτ
    exact ⟨σ, hσ, hx⟩
  · rintro ⟨σ, hσ, hx⟩
    exact ⟨σ.image vertexVector, image_vertexVector_mem_standardGeometricComplex hσ, hx⟩

/-- The standard coordinate vector of every vertex belongs to the geometric realization. -/
theorem vertexVector_mem (K : AbstractSimplicialComplex ι) (v : ι) :
    vertexVector v ∈ (standardGeometricComplex K).space := by
  apply Geometry.SimplicialComplex.vertices_subset_space
  rw [Geometry.SimplicialComplex.mem_vertices]
  simpa [vertexVector] using
    image_vertexVector_mem_standardGeometricComplex (K.singleton_mem v)

/-- The canonical point of the geometric realization corresponding to a vertex. -/
noncomputable def vertex (K : AbstractSimplicialComplex ι) (v : ι) : Realization K :=
  ⟨vertexVector v, vertexVector_mem K v⟩

/-- The underlying finitely supported function of a realization vertex is its coordinate vector. -/
@[simp]
theorem vertex_val (K : AbstractSimplicialComplex ι) (v : ι) :
    (vertex K v : ι →₀ ℝ) = vertexVector v :=
  (rfl)

/-- Distinct vertices give distinct points in the geometric realization. -/
theorem vertex_injective (K : AbstractSimplicialComplex ι) :
    Function.Injective (vertex K) := by
  intro v w h
  have hvw : vertexVector v = vertexVector w := congrArg Subtype.val h
  classical
  simpa [vertexVector] using Finsupp.single_left_injective (M := ℝ) one_ne_zero hvw

/-- The canonical map from vertices to the realization. -/
noncomputable def vertexEmbedding (K : AbstractSimplicialComplex ι) : ι ↪ Realization K :=
  ⟨vertex K, vertex_injective K⟩

/-- Inclusion of abstract complexes induces inclusion of their standard polyhedra. -/
theorem standardGeometricComplex_space_mono {K L : AbstractSimplicialComplex ι} (hKL : K ≤ L) :
    (standardGeometricComplex K).space ⊆ (standardGeometricComplex L).space := by
  intro x hx
  rw [mem_realization_iff] at hx ⊢
  obtain ⟨σ, hσ, hx⟩ := hx
  exact ⟨σ, hKL hσ, hx⟩

end AbstractSimplicialComplex

end TauCeti

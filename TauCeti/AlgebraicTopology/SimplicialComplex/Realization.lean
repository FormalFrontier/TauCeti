/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Convex.SimplicialComplex.AffineIndependentUnion
public import Mathlib.Topology.UniformSpace.Real
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

attribute [local instance] Classical.decEq

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

/-- The closed simplex spanned by a finite vertex set, in standard barycentric coordinates. -/
noncomputable abbrev FaceRealization (σ : Finset ι) : Type _ :=
  convexHull ℝ (σ.image (fun v => Finsupp.single v (1 : ℝ)) : Set (ι →₀ ℝ))

/-- The topology induced by the coordinatewise topology on `ι → ℝ`. These are the domain
topologies used to define the weak topology on the whole realization. -/
instance (σ : Finset ι) : TopologicalSpace (FaceRealization σ) :=
  TopologicalSpace.induced (fun x : FaceRealization σ => (x.1 : ι → ℝ)) inferInstance

/-- A geometric face is exactly the image of an abstract face under the coordinate embedding. -/
theorem mem_standardGeometricComplex_faces_iff (K : AbstractSimplicialComplex ι)
    (τ : Finset (ι →₀ ℝ)) :
    τ ∈ (standardGeometricComplex K).faces ↔
      ∃ σ ∈ K, σ.image (fun v => Finsupp.single v (1 : ℝ)) = τ := by
  classical
  simp only [standardGeometricComplex, Geometry.SimplicialComplex.onFinsupp,
    Geometry.SimplicialComplex.ofAffineIndependent, PreAbstractSimplicialComplex.map,
    Set.mem_image]
  aesop

/-- Include the realization of a face into the whole polyhedron. -/
noncomputable def faceInclusion (K : AbstractSimplicialComplex ι) (σ : Face K) :
    FaceRealization σ.1 → Realization K :=
  fun x => ⟨x, Geometry.SimplicialComplex.convexHull_subset_space
    (K := standardGeometricComplex K)
      ((mem_standardGeometricComplex_faces_iff K _).2 ⟨σ.1, σ.2, rfl⟩) x.2⟩

/-- A face inclusion does not change the underlying barycentric coordinates. -/
@[simp]
theorem faceInclusion_val (K : AbstractSimplicialComplex ι) (σ : Face K)
    (x : FaceRealization σ.1) :
    (faceInclusion K σ x : ι →₀ ℝ) = x := by
  simp [faceInclusion]

/-- The weak topology on a realization, final with respect to all face inclusions. -/
instance (K : AbstractSimplicialComplex ι) : TopologicalSpace (Realization K) :=
  ⨆ σ : Face K, TopologicalSpace.coinduced (faceInclusion K σ) inferInstance

/-- Every face inclusion is continuous for the weak topology on the realization. -/
theorem continuous_faceInclusion (K : AbstractSimplicialComplex ι) (σ : Face K) :
    Continuous (faceInclusion K σ) :=
  continuous_iff_coinduced_le.2 (le_iSup (fun τ : Face K =>
    TopologicalSpace.coinduced (faceInclusion K τ) inferInstance) σ)

/-- A map out of a realization is continuous exactly when its restriction to every face is
continuous. -/
theorem continuous_iff_faceInclusion {K : AbstractSimplicialComplex ι}
    {X : Type*} [TopologicalSpace X] {f : Realization K → X} :
    Continuous f ↔ ∀ σ : Face K, Continuous (f ∘ faceInclusion K σ) := by
  rw [continuous_iSup_dom]
  exact forall_congr' fun _ => continuous_coinduced_dom

/-- The coordinate image of every abstract face is a face of the geometric complex. -/
theorem image_single_mem_standardGeometricComplex_faces {K : AbstractSimplicialComplex ι}
    {σ : Finset ι} (hσ : σ ∈ K) :
    σ.image (fun v => Finsupp.single v (1 : ℝ)) ∈ (standardGeometricComplex K).faces :=
  (mem_standardGeometricComplex_faces_iff K _).2 ⟨σ, hσ, rfl⟩

/-- A point belongs to the standard polyhedron exactly when it lies in the convex hull of the
coordinate image of some abstract face. -/
theorem mem_realization_iff {K : AbstractSimplicialComplex ι} {x : ι →₀ ℝ} :
    x ∈ (standardGeometricComplex K).space ↔
      ∃ σ ∈ K, x ∈
        convexHull ℝ (σ.image (fun v => Finsupp.single v (1 : ℝ)) : Set (ι →₀ ℝ)) := by
  rw [Geometry.SimplicialComplex.mem_space_iff]
  constructor
  · rintro ⟨τ, hτ, hx⟩
    obtain ⟨σ, hσ, rfl⟩ := (mem_standardGeometricComplex_faces_iff K τ).1 hτ
    exact ⟨σ, hσ, hx⟩
  · rintro ⟨σ, hσ, hx⟩
    exact ⟨σ.image (fun v => Finsupp.single v (1 : ℝ)),
      image_single_mem_standardGeometricComplex_faces hσ, hx⟩

/-- The standard coordinate vector of every vertex belongs to the geometric realization. -/
theorem single_mem_standardGeometricComplex_space (K : AbstractSimplicialComplex ι) (v : ι) :
    Finsupp.single v 1 ∈ (standardGeometricComplex K).space := by
  apply Geometry.SimplicialComplex.vertices_subset_space
  rw [Geometry.SimplicialComplex.mem_vertices]
  simpa using image_single_mem_standardGeometricComplex_faces (K.singleton_mem v)

/-- The canonical point of the geometric realization corresponding to a vertex. -/
noncomputable def vertex (K : AbstractSimplicialComplex ι) (v : ι) : Realization K :=
  ⟨Finsupp.single v 1, single_mem_standardGeometricComplex_space K v⟩

/-- The underlying finitely supported function of a realization vertex is its coordinate vector. -/
@[simp]
theorem vertex_val (K : AbstractSimplicialComplex ι) (v : ι) :
    (vertex K v : ι →₀ ℝ) = Finsupp.single v 1 :=
  (rfl)

/-- Distinct vertices give distinct points in the geometric realization. -/
theorem vertex_injective (K : AbstractSimplicialComplex ι) :
    Function.Injective (vertex K) := by
  intro v w h
  have hvw : Finsupp.single v (1 : ℝ) = Finsupp.single w 1 := congrArg Subtype.val h
  classical
  exact Finsupp.single_left_injective (M := ℝ) one_ne_zero hvw

/-- The canonical map from vertices to the realization. -/
noncomputable def vertexEmbedding (K : AbstractSimplicialComplex ι) : ι ↪ Realization K :=
  ⟨vertex K, vertex_injective K⟩

/-- The vertex embedding sends a vertex to its canonical point in the realization. -/
@[simp]
theorem vertexEmbedding_apply (K : AbstractSimplicialComplex ι) (v : ι) :
    vertexEmbedding K v = vertex K v := by
  simp [vertexEmbedding]

/-- Inclusion of abstract complexes induces inclusion of their standard polyhedra. -/
theorem standardGeometricComplex_space_mono {K L : AbstractSimplicialComplex ι} (hKL : K ≤ L) :
    (standardGeometricComplex K).space ⊆ (standardGeometricComplex L).space := by
  intro x hx
  rw [mem_realization_iff] at hx ⊢
  obtain ⟨σ, hσ, hx⟩ := hx
  exact ⟨σ, hKL hσ, hx⟩

/-- The continuous map of realizations induced by an inclusion of abstract complexes. -/
noncomputable def realizationMap {K L : AbstractSimplicialComplex ι} (hKL : K ≤ L) :
    Realization K → Realization L :=
  fun x => ⟨x, standardGeometricComplex_space_mono hKL x.2⟩

/-- An induced map of realizations does not change the underlying barycentric coordinates. -/
@[simp]
theorem realizationMap_val {K L : AbstractSimplicialComplex ι} (hKL : K ≤ L)
    (x : Realization K) :
    (realizationMap hKL x : ι →₀ ℝ) = x := by
  simp [realizationMap]

/-- An inclusion map restricted to a face is the corresponding face inclusion in the larger
complex. -/
@[simp]
theorem realizationMap_comp_faceInclusion {K L : AbstractSimplicialComplex ι} (hKL : K ≤ L)
    (σ : Face K) :
    realizationMap hKL ∘ faceInclusion K σ = faceInclusion L ⟨σ.1, hKL σ.2⟩ := by
  funext x
  exact Subtype.ext rfl

/-- The map of realizations induced by an inclusion is continuous. -/
theorem continuous_realizationMap {K L : AbstractSimplicialComplex ι} (hKL : K ≤ L) :
    Continuous (realizationMap hKL) := by
  apply continuous_iff_faceInclusion.2
  intro σ
  rw [realizationMap_comp_faceInclusion]
  exact continuous_faceInclusion L ⟨σ.1, hKL σ.2⟩

/-- The map induced by the reflexive inclusion is the identity. -/
@[simp]
theorem realizationMap_refl (K : AbstractSimplicialComplex ι) :
    realizationMap (le_refl K) = id := by
  funext x
  exact Subtype.ext rfl

/-- Maps induced by inclusions compose according to transitivity of inclusion. -/
theorem realizationMap_trans {K L M : AbstractSimplicialComplex ι} (hKL : K ≤ L) (hLM : L ≤ M) :
    realizationMap (hKL.trans hLM) = realizationMap hLM ∘ realizationMap hKL := by
  funext x
  exact Subtype.ext rfl

end AbstractSimplicialComplex

end TauCeti

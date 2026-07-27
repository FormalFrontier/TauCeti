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

/-- The closed simplex spanned by a finite vertex set, in standard barycentric coordinates. -/
noncomputable abbrev StandardSimplex (σ : Finset ι) : Type _ :=
  convexHull ℝ (σ.image (fun v => Finsupp.single v (1 : ℝ)) : Set (ι →₀ ℝ))

/-- The topology induced by the coordinatewise topology on `ι → ℝ`. These are the domain
topologies used to define the weak topology on the whole realization. -/
instance (σ : Finset ι) : TopologicalSpace (StandardSimplex σ) :=
  TopologicalSpace.induced (fun x : StandardSimplex σ => (x.1 : ι → ℝ)) inferInstance

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
    StandardSimplex σ.1 → Realization K :=
  Set.inclusion (Geometry.SimplicialComplex.convexHull_subset_space
    (K := standardGeometricComplex K)
      ((mem_standardGeometricComplex_faces_iff K _).2 ⟨σ.1, σ.2, rfl⟩))

/-- A face inclusion does not change the underlying barycentric coordinates. -/
@[simp]
theorem faceInclusion_val (K : AbstractSimplicialComplex ι) (σ : Face K)
    (x : StandardSimplex σ.1) :
    (faceInclusion K σ x : ι →₀ ℝ) = x := by
  exact Set.coe_inclusion
    (Geometry.SimplicialComplex.convexHull_subset_space
      ((mem_standardGeometricComplex_faces_iff K _).2 ⟨σ.1, σ.2, rfl⟩)) x

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

/-- Barycentric coordinates in a standard simplex are nonnegative. -/
theorem StandardSimplex.nonneg {σ : Finset ι} (x : StandardSimplex σ) (v : ι) :
    0 ≤ x.1 v := by
  -- View the coordinate inequality as membership in a convex half-space.
  change x.1 ∈ {y : ι →₀ ℝ | 0 ≤ y v}
  exact convexHull_min (by
      intro y hy
      simp only [Finset.coe_image, Set.mem_image] at hy
      obtain ⟨w, _, rfl⟩ := hy
      by_cases h : w = v <;> simp [h])
    (by
      intro y hy z hz a b ha hb hab
      simp only [Set.mem_setOf_eq, Finsupp.add_apply, Finsupp.smul_apply] at hy hz ⊢
      exact add_nonneg (mul_nonneg ha hy) (mul_nonneg hb hz))
    x.2

/-- The barycentric coordinates in a standard simplex sum to one. -/
theorem StandardSimplex.sum_eq_one {σ : Finset ι} (x : StandardSimplex σ) :
    x.1.sum (fun _ r => r) = 1 := by
  -- Use the linear-map form of coordinate summation required by the convexity API.
  change x.1.sum (fun _ => LinearMap.id (R := ℝ) (M := ℝ)) = 1
  change x.1 ∈
    {y : ι →₀ ℝ | y.sum (fun _ => LinearMap.id (R := ℝ) (M := ℝ)) = 1}
  exact convexHull_min (by
      intro y hy
      simp only [Finset.coe_image, Set.mem_image] at hy
      obtain ⟨v, _, rfl⟩ := hy
      simp)
    (by
      intro y hy z hz a b _ _ hab
      simp only [Set.mem_setOf_eq] at hy hz ⊢
      rw [Finsupp.sum_add_index]
      · rw [Finsupp.sum_smul_index_linearMap', Finsupp.sum_smul_index_linearMap', hy, hz]
        simpa [smul_eq_mul] using hab
      all_goals simp)
    x.2

/-- The support of a point in a standard simplex is contained in its vertex set. -/
theorem StandardSimplex.support_subset {σ : Finset ι} (x : StandardSimplex σ) :
    x.1.support ⊆ σ := by
  -- Express support containment as membership in the standard supported submodule.
  change (x.1.support : Set ι) ⊆ (σ : Set ι)
  change x.1 ∈ Finsupp.supported ℝ ℝ (σ : Set ι)
  exact convexHull_min (by
    intro y hy
    simp only [Finset.coe_image, Set.mem_image] at hy
    obtain ⟨v, hv, rfl⟩ := hy
    simpa [Finsupp.mem_supported] using hv) (Finsupp.supported ℝ ℝ (σ : Set ι)).convex x.2

/-- Membership in a standard simplex in terms of barycentric coordinates. -/
@[simp]
theorem mem_standardSimplex_iff {σ : Finset ι} {x : ι →₀ ℝ} :
    x ∈ convexHull ℝ
        ((fun v => Finsupp.single v (1 : ℝ)) '' (σ : Set ι)) ↔
      (∀ v, 0 ≤ x v) ∧ x.sum (fun _ r => r) = 1 ∧ x.support ⊆ σ := by
  constructor
  · intro hx
    rw [← Finset.coe_image] at hx
    let x' : StandardSimplex σ := ⟨x, hx⟩
    exact ⟨StandardSimplex.nonneg x', StandardSimplex.sum_eq_one x',
      StandardSimplex.support_subset x'⟩
  · rintro ⟨hnonneg, hsum, hsupp⟩
    have hsum' :
        x.sum (fun _ => LinearMap.id (R := ℝ) (M := ℝ)) = 1 := by
      -- Put the coordinate-sum hypothesis in the linear-map form required by `Convex.sum_mem`.
      change x.sum (fun _ r => r) = 1
      exact hsum
    have hx := (convex_convexHull ℝ
        (σ.image (fun v => Finsupp.single v (1 : ℝ)) : Set (ι →₀ ℝ))).sum_mem
      (fun v _ => hnonneg v) hsum'
      (fun v hv => subset_convexHull ℝ _ (Finset.mem_coe.2 <|
        Finset.mem_image.2 ⟨v, hsupp hv, rfl⟩))
    have heq : (∑ i ∈ x.support, x i • Finsupp.single i (1 : ℝ)) = x := by
      simpa [Finsupp.sum] using x.sum_single
    rw [heq] at hx
    rw [Finset.coe_image] at hx
    exact hx

/-- A point of a standard simplex lies in the simplex spanned by its support. -/
theorem StandardSimplex.mem_convexHull_support {σ : Finset ι} (x : StandardSimplex σ) :
    x.1 ∈ convexHull ℝ
      (x.1.support.image (fun v => Finsupp.single v (1 : ℝ)) : Set (ι →₀ ℝ)) := by
  have hx := (convex_convexHull ℝ _).sum_mem
    (fun v _ => StandardSimplex.nonneg x v)
    (by
      -- Return from the linear-map form expected by `Convex.sum_mem` to scalar summation.
      change x.1.sum (fun _ r => r) = 1
      exact StandardSimplex.sum_eq_one x)
    (fun v hv => subset_convexHull ℝ _ (by
      -- Re-express set membership in the finite image so `Finset.mem_image` applies.
      change Finsupp.single v 1 ∈
        (x.1.support.image (fun w => Finsupp.single w (1 : ℝ)) : Finset (ι →₀ ℝ))
      exact Finset.mem_image.2 ⟨v, hv, rfl⟩))
  have heq : (∑ i ∈ x.1.support, x.1 i • Finsupp.single i (1 : ℝ)) = x.1 := by
    simpa [Finsupp.sum] using x.1.sum_single
  rw [heq] at hx
  exact hx

/-- The support of a realization point is an abstract face. -/
theorem support_mem (K : AbstractSimplicialComplex ι) (x : Realization K) : x.1.support ∈ K := by
  obtain ⟨σ, hσ, hx⟩ := mem_realization_iff.1 x.2
  let hx' : StandardSimplex σ := ⟨x.1, hx⟩
  have hs : x.1.support ⊆ σ := by
    simpa [hx'] using StandardSimplex.support_subset hx'
  apply K.isRelLowerSet_faces.mem_of_le hσ
    hs
  exact
    (Finsupp.support_nonempty_iff.mpr <| by
      intro h
      have hs := StandardSimplex.sum_eq_one hx'
      have hs' : x.1.sum (fun _ r => r) = 1 := by
        simpa [hx'] using hs
      rw [h] at hs'
      simp at hs')

/-- The minimal abstract face carrying a point of the realization. -/
noncomputable def carrier (K : AbstractSimplicialComplex ι) (x : Realization K) : Face K :=
  ⟨x.1.support, support_mem K x⟩

/-- The vertices of the carrier are exactly the nonzero barycentric coordinates. -/
@[simp]
theorem carrier_val (K : AbstractSimplicialComplex ι) (x : Realization K) :
    (carrier K x).1 = x.1.support :=
  (rfl)

/-- A realization point belongs to the closed simplex spanned by its carrier. -/
theorem mem_convexHull_carrier (K : AbstractSimplicialComplex ι) (x : Realization K) :
    x.1 ∈ convexHull ℝ
      ((carrier K x).1.image (fun v => Finsupp.single v (1 : ℝ)) : Set (ι →₀ ℝ)) := by
  obtain ⟨σ, _, hx⟩ := mem_realization_iff.1 x.2
  rw [carrier_val]
  exact StandardSimplex.mem_convexHull_support ⟨x.1, hx⟩

/-- The carrier is contained in every finite vertex set whose closed simplex contains the point. -/
theorem carrier_minimal (K : AbstractSimplicialComplex ι) (x : Realization K) {σ : Finset ι}
    (hx : x.1 ∈ convexHull ℝ
      (σ.image (fun v => Finsupp.single v (1 : ℝ)) : Set (ι →₀ ℝ))) :
    (carrier K x).1 ⊆ σ :=
  by
    rw [carrier_val]
    exact StandardSimplex.support_subset ⟨x.1, hx⟩

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
  Set.inclusion (standardGeometricComplex_space_mono hKL)

/-- An induced map of realizations does not change the underlying barycentric coordinates. -/
@[simp]
theorem realizationMap_val {K L : AbstractSimplicialComplex ι} (hKL : K ≤ L)
    (x : Realization K) :
    (realizationMap hKL x : ι →₀ ℝ) = x := by
  exact Set.coe_inclusion (standardGeometricComplex_space_mono hKL) x

/-- The map of realizations induced by an inclusion is injective. -/
theorem realizationMap_injective {K L : AbstractSimplicialComplex ι} (hKL : K ≤ L) :
    Function.Injective (realizationMap hKL) :=
  Set.inclusion_injective (standardGeometricComplex_space_mono hKL)

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
    realizationMap (le_refl K) = id :=
  Set.inclusion_eq_id (standardGeometricComplex_space_mono (le_refl K))

/-- Maps induced by inclusions compose according to transitivity of inclusion. -/
theorem realizationMap_trans {K L M : AbstractSimplicialComplex ι} (hKL : K ≤ L) (hLM : L ≤ M) :
    realizationMap (hKL.trans hLM) = realizationMap hLM ∘ realizationMap hKL := by
  exact (Set.inclusion_comp_inclusion (standardGeometricComplex_space_mono hKL)
    (standardGeometricComplex_space_mono hLM)).symm

end AbstractSimplicialComplex

end TauCeti

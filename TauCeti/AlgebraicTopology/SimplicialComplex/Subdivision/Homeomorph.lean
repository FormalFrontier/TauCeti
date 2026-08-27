/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Injective

/-!
# The realization homeomorphism for barycentric subdivision

The canonical map from the realization of the barycentric subdivision of a simplicial complex to
the realization of the original complex is a homeomorphism. The forward map sends a face-vertex to
the barycenter of that face and extends affinely over subdivision simplices.

Continuity of the inverse is proved simplex by simplex, using the weak topology on realizations.
Each original simplex is covered by the finitely many closed chambers obtained by ordering its
barycentric coordinates. On one chamber the inverse has a fixed affine formula: consecutive
coordinate differences are the coefficients of the nested initial faces in that order. These
formulas are continuous and agree on chamber intersections because the forward map is injective.

This completes the subdivision part of the geometric-realization milestone in Layer 11 of the
GeometricTopology roadmap. The construction follows Rourke--Sanderson, *Introduction to
Piecewise-Linear Topology*, Chapter 2, "Derived Subdivisions".

## Main definition

* `AbstractSimplicialComplex.barycentricSubdivisionRealizationHomeomorph`: the canonical
  homeomorphism from the realization of the barycentric subdivision to the original realization.
-/

public section

noncomputable section

open Finset Set TauCeti TauCeti.SetLike

namespace AbstractSimplicialComplex

variable {ι : Type*}

attribute [local instance] Classical.decEq

private abbrev VertexOrder {K : AbstractSimplicialComplex ι} (σ : Face K) :=
  Fin σ.1.card ≃ {v // v ∈ σ.1}

/-- The closed chamber in which the coordinates occur in decreasing order along `e`. -/
private def orderChamber {K : AbstractSimplicialComplex ι} (σ : Face K)
    (e : VertexOrder σ) : Set (StandardSimplex σ.1) :=
  {x | Antitone fun i => x.1 (e i).1}

private theorem isClosed_orderChamber {K : AbstractSimplicialComplex ι} (σ : Face K)
    (e : VertexOrder σ) : IsClosed (orderChamber σ e) := by
  -- Expand antitonicity as an intersection of closed coordinate inequalities.
  rw [show orderChamber σ e =
      ⋂ i, ⋂ j, ⋂ (_ : i ≤ j), {x | x.1 (e j).1 ≤ x.1 (e i).1} by
    ext x
    simp [orderChamber, Antitone]]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro j
  apply isClosed_iInter
  intro _
  exact isClosed_le
    ((continuous_apply (e j).1).comp continuous_induced_dom)
    ((continuous_apply (e i).1).comp continuous_induced_dom)

@[instance_reducible]
private noncomputable def vertexLinearOrder {K : AbstractSimplicialComplex ι} (σ : Face K)
    (x : StandardSimplex σ.1) : LinearOrder {v // v ∈ σ.1} :=
  LinearOrder.lift'
    (fun v => toLex (OrderDual.toDual (x.1 v.1), Fintype.equivFin _ v))
    (fun _ _ h => (Fintype.equivFin _).injective
      (congrArg (fun z => (ofLex z).2) h))

/-- Order the vertices of a simplex by decreasing coordinate, breaking ties arbitrarily. -/
private noncomputable def decreasingVertexOrder {K : AbstractSimplicialComplex ι} (σ : Face K)
    (x : StandardSimplex σ.1) : VertexOrder σ :=
  let _ := vertexLinearOrder σ x
  (Fintype.orderIsoFinOfCardEq _ (by simp)).toEquiv

private theorem mem_orderChamber_decreasingVertexOrder {K : AbstractSimplicialComplex ι}
    (σ : Face K) (x : StandardSimplex σ.1) :
    x ∈ orderChamber σ (decreasingVertexOrder σ x) := by
  let _ := vertexLinearOrder σ x
  intro i j hij
  have h := (Fintype.orderIsoFinOfCardEq
    {v // v ∈ σ.1} (by simp)).monotone hij
  -- Expose the lexicographic order installed by `vertexLinearOrder` to read its first coordinate.
  change toLex (OrderDual.toDual (x.1 (decreasingVertexOrder σ x i).1),
      Fintype.equivFin {v // v ∈ σ.1} (decreasingVertexOrder σ x i)) ≤
    toLex (OrderDual.toDual (x.1 (decreasingVertexOrder σ x j).1),
      Fintype.equivFin {v // v ∈ σ.1} (decreasingVertexOrder σ x j)) at h
  rw [Prod.Lex.le_iff] at h
  rcases h with h | h
  · exact h.le
  · exact h.1.le

private theorem iUnion_orderChamber {K : AbstractSimplicialComplex ι} (σ : Face K) :
    ⋃ e : VertexOrder σ, orderChamber σ e = Set.univ := by
  rw [eq_univ_iff_forall]
  intro x
  exact Set.mem_iUnion.2
    ⟨decreasingVertexOrder σ x, mem_orderChamber_decreasingVertexOrder σ x⟩

/-- The first `i + 1` vertices in a fixed ordering of a face. -/
private def orderedPrefixVertices {K : AbstractSimplicialComplex ι} {σ : Face K}
    (e : VertexOrder σ) (i : Fin σ.1.card) : Finset ι :=
  (Finset.Iic i).image fun j => (e j).1

private theorem orderedPrefixVertices_nonempty {K : AbstractSimplicialComplex ι} {σ : Face K}
    (e : VertexOrder σ) (i : Fin σ.1.card) : (orderedPrefixVertices e i).Nonempty := by
  exact ⟨(e i).1, Finset.mem_image.2 ⟨i, Finset.mem_Iic.2 le_rfl, rfl⟩⟩

private theorem orderedPrefixVertices_subset {K : AbstractSimplicialComplex ι} {σ : Face K}
    (e : VertexOrder σ) (i : Fin σ.1.card) : orderedPrefixVertices e i ⊆ σ.1 := by
  intro v hv
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hv
  exact (e j).2

private noncomputable def orderedPrefixFace {K : AbstractSimplicialComplex ι} (σ : Face K)
    (e : VertexOrder σ) (i : Fin σ.1.card) : Face K :=
  ⟨orderedPrefixVertices e i, K.isRelLowerSet_faces.mem_of_le σ.2
    (orderedPrefixVertices_subset e i) (orderedPrefixVertices_nonempty e i)⟩

private theorem orderedPrefixFace_mono {K : AbstractSimplicialComplex ι} (σ : Face K)
    (e : VertexOrder σ) {i j : Fin σ.1.card} (hij : i ≤ j) :
    orderedPrefixFace σ e i ≤ orderedPrefixFace σ e j := by
  intro v hv
  obtain ⟨k, hki, rfl⟩ := Finset.mem_image.1 hv
  exact Finset.mem_image.2
    ⟨k, Finset.mem_Iic.2 ((Finset.mem_Iic.1 hki).trans hij), rfl⟩

private theorem card_orderedPrefixFace {K : AbstractSimplicialComplex ι} (σ : Face K)
    (e : VertexOrder σ) (i : Fin σ.1.card) :
    (orderedPrefixFace σ e i).1.card = i.1 + 1 := by
  -- Forget the face-membership proof before counting the underlying initial segment.
  change (orderedPrefixVertices e i).card = i.1 + 1
  rw [orderedPrefixVertices, Finset.card_image_iff.mpr]
  · exact Fin.card_Iic i
  · exact fun _ _ _ _ h => e.injective (Subtype.ext h)

/-- The chain of initial faces determined by a vertex ordering. -/
private noncomputable def orderedSubdivisionFaces {K : AbstractSimplicialComplex ι}
    (σ : Face K) (e : VertexOrder σ) : Finset (Face K) :=
  Finset.univ.image (orderedPrefixFace σ e)

private theorem orderedSubdivisionFaces_nonempty {K : AbstractSimplicialComplex ι}
    (σ : Face K) (e : VertexOrder σ) : (orderedSubdivisionFaces σ e).Nonempty := by
  have hσ : 0 < σ.1.card := Finset.card_pos.mpr
    (K.isRelLowerSet_faces.prop_of_mem σ.2)
  let i : Fin σ.1.card := ⟨0, hσ⟩
  exact ⟨orderedPrefixFace σ e i,
    Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩⟩

private theorem orderedSubdivisionFaces_mem {K : AbstractSimplicialComplex ι}
    (σ : Face K) (e : VertexOrder σ) :
    orderedSubdivisionFaces σ e ∈ TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      K.toPreAbstractSimplicialComplex := by
  rw [TauCeti.PreAbstractSimplicialComplex.mem_barycentricSubdivision_iff]
  refine ⟨orderedSubdivisionFaces_nonempty σ e, ?_⟩
  intro ρ hρ τ hτ _
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hρ
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hτ
  exact (le_total i j).imp (orderedPrefixFace_mono σ e) (orderedPrefixFace_mono σ e)

private noncomputable def orderedSubdivisionFace {K : AbstractSimplicialComplex ι}
    (σ : Face K) (e : VertexOrder σ) :
    Face (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      K.toPreAbstractSimplicialComplex) :=
  ⟨orderedSubdivisionFaces σ e, orderedSubdivisionFaces_mem σ e⟩

/-- Extend the ordered coordinates by zero after the last vertex. -/
private noncomputable def chamberOrderedCoord {K : AbstractSimplicialComplex ι} (σ : Face K)
    (e : VertexOrder σ) (x : orderChamber σ e) (k : ℕ) : ℝ :=
  if h : k < σ.1.card then x.1.1 (e ⟨k, h⟩).1 else 0

private theorem chamberOrderedCoord_of_lt {K : AbstractSimplicialComplex ι} (σ : Face K)
    (e : VertexOrder σ) (x : orderChamber σ e) {k : ℕ} (hk : k < σ.1.card) :
    chamberOrderedCoord σ e x k = x.1.1 (e ⟨k, hk⟩).1 := by
  rw [chamberOrderedCoord]
  split
  · congr
  · contradiction

private theorem chamberOrderedCoord_card {K : AbstractSimplicialComplex ι} (σ : Face K)
    (e : VertexOrder σ) (x : orderChamber σ e) :
    chamberOrderedCoord σ e x σ.1.card = 0 := by
  simp [chamberOrderedCoord]

private theorem continuous_chamberOrderedCoord {K : AbstractSimplicialComplex ι} (σ : Face K)
    (e : VertexOrder σ) (k : ℕ) :
    Continuous (fun x : orderChamber σ e => chamberOrderedCoord σ e x k) := by
  unfold chamberOrderedCoord
  split
  · have hcoe : Continuous (fun y : StandardSimplex σ.1 => (y.1 : ι → ℝ)) :=
      continuous_induced_dom
    exact ((continuous_apply _).comp hcoe).comp continuous_subtype_val
  · exact continuous_const

private theorem chamberOrderedCoord_succ_le {K : AbstractSimplicialComplex ι} (σ : Face K)
    (e : VertexOrder σ) (x : orderChamber σ e) {k : ℕ} (hk : k < σ.1.card) :
    chamberOrderedCoord σ e x (k + 1) ≤ chamberOrderedCoord σ e x k := by
  rw [chamberOrderedCoord_of_lt σ e x hk]
  by_cases hks : k + 1 < σ.1.card
  · rw [chamberOrderedCoord_of_lt σ e x hks]
    exact x.2 (Fin.mk_le_mk.mpr (Nat.le_succ k))
  · rw [chamberOrderedCoord]
    simp only [hks, ↓reduceDIte]
    exact StandardSimplex.nonneg x.1 _

/-- The coefficient of the `i`th initial face in one ordered chamber. -/
private noncomputable def chamberWeight {K : AbstractSimplicialComplex ι} (σ : Face K)
    (e : VertexOrder σ) (x : orderChamber σ e) (i : Fin σ.1.card) : ℝ :=
  (i.1 + 1 : ℝ) *
    (chamberOrderedCoord σ e x i.1 - chamberOrderedCoord σ e x (i.1 + 1))

private theorem chamberWeight_nonneg {K : AbstractSimplicialComplex ι} (σ : Face K)
    (e : VertexOrder σ) (x : orderChamber σ e) (i : Fin σ.1.card) :
    0 ≤ chamberWeight σ e x i := by
  exact mul_nonneg (by positivity)
    (sub_nonneg.2 (chamberOrderedCoord_succ_le σ e x i.2))

private theorem continuous_chamberWeight {K : AbstractSimplicialComplex ι} (σ : Face K)
    (e : VertexOrder σ) (i : Fin σ.1.card) :
    Continuous (fun x : orderChamber σ e => chamberWeight σ e x i) :=
  continuous_const.mul
    ((continuous_chamberOrderedCoord σ e i.1).sub
      (continuous_chamberOrderedCoord σ e (i.1 + 1)))

/-- Summation by parts for the coefficients in an ordered chamber. -/
private theorem sum_range_succ_mul_sub (f : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, (i + 1 : ℝ) * (f i - f (i + 1)) =
      ∑ i ∈ Finset.range n, f i - (n : ℝ) * f n := by
  apply Finset.sum_range_induction
  · simp
  · intro k _
    rw [Finset.sum_range_succ]
    push_cast
    ring

private theorem sum_range_ite_le_sub (f : ℕ → ℝ) {j n : ℕ} (hjn : j < n) :
    ∑ i ∈ Finset.range n, (if j ≤ i then f i - f (i + 1) else 0) = f j - f n := by
  rw [← Finset.sum_filter]
  have hfilter : (Finset.range n).filter (j ≤ ·) = Finset.Ico j n := by
    ext i
    simp [and_comm]
  rw [hfilter]
  calc
    ∑ i ∈ Finset.Ico j n, (f i - f (i + 1)) =
        -∑ i ∈ Finset.Ico j n, (f (i + 1) - f i) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = -(f n - f j) := by rw [Finset.sum_Ico_sub f hjn.le]
    _ = f j - f n := by ring

private theorem sum_chamberOrderedCoord {K : AbstractSimplicialComplex ι} (σ : Face K)
    (e : VertexOrder σ) (x : orderChamber σ e) :
    ∑ k ∈ Finset.range σ.1.card, chamberOrderedCoord σ e x k = 1 := by
  rw [← Fin.sum_univ_eq_sum_range]
  calc
    ∑ i : Fin σ.1.card, chamberOrderedCoord σ e x i =
        ∑ i : Fin σ.1.card, x.1.1 (e i).1 := by
      apply Finset.sum_congr rfl
      intro i _
      exact chamberOrderedCoord_of_lt σ e x i.2
    _ = ∑ v : {v // v ∈ σ.1}, x.1.1 v.1 := by
      exact Fintype.sum_equiv e _ _ fun _ => rfl
    _ = ∑ v ∈ σ.1, x.1.1 v := Finset.sum_attach _ _
    _ = 1 := by
      rw [← Finsupp.sum_of_support_subset x.1.1 (StandardSimplex.support_subset x.1)
        (fun _ r => r) (by simp)]
      exact StandardSimplex.sum_eq_one x.1

private theorem sum_chamberWeight {K : AbstractSimplicialComplex ι} (σ : Face K)
    (e : VertexOrder σ) (x : orderChamber σ e) :
    ∑ i, chamberWeight σ e x i = 1 := by
  calc
    ∑ i, chamberWeight σ e x i =
        ∑ i ∈ Finset.range σ.1.card,
          (i + 1 : ℝ) * (chamberOrderedCoord σ e x i -
            chamberOrderedCoord σ e x (i + 1)) := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i _
      rfl
    _ = 1 := by
      rw [sum_range_succ_mul_sub, chamberOrderedCoord_card, mul_zero, sub_zero,
        sum_chamberOrderedCoord]

/-- The subdivision coordinates defined by a fixed vertex ordering. -/
private noncomputable def chamberCoordinates {K : AbstractSimplicialComplex ι} (σ : Face K)
    (e : VertexOrder σ) (x : orderChamber σ e) : Face K →₀ ℝ :=
  ∑ i : Fin σ.1.card,
    Finsupp.single (orderedPrefixFace σ e i) (chamberWeight σ e x i)

private theorem chamberCoordinates_nonneg {K : AbstractSimplicialComplex ι} (σ : Face K)
    (e : VertexOrder σ) (x : orderChamber σ e) (ρ : Face K) :
    0 ≤ chamberCoordinates σ e x ρ := by
  rw [chamberCoordinates]
  -- Evaluation is the additive homomorphism needed to move through the finite sum of `Finsupp`s.
  change 0 ≤ Finsupp.applyAddHom ρ
    (∑ i : Fin σ.1.card,
      Finsupp.single (orderedPrefixFace σ e i) (chamberWeight σ e x i))
  rw [map_sum]
  apply Finset.sum_nonneg
  intro i _
  by_cases h : orderedPrefixFace σ e i = ρ
  · simp [h, chamberWeight_nonneg]
  · simp [h]

private theorem chamberCoordinates_sum {K : AbstractSimplicialComplex ι} (σ : Face K)
    (e : VertexOrder σ) (x : orderChamber σ e) :
    (chamberCoordinates σ e x).sum (fun _ r => r) = 1 := by
  rw [chamberCoordinates]
  rw [← Finsupp.sum_finsetSum_index (fun _ => rfl) (fun _ _ _ => rfl)]
  simp only [Finsupp.sum_single_index]
  exact sum_chamberWeight σ e x

private theorem chamberCoordinates_support {K : AbstractSimplicialComplex ι} (σ : Face K)
    (e : VertexOrder σ) (x : orderChamber σ e) :
    (chamberCoordinates σ e x).support ⊆ orderedSubdivisionFaces σ e := by
  intro ρ hρ
  by_contra hnot
  have hne : ∀ i : Fin σ.1.card, orderedPrefixFace σ e i ≠ ρ := by
    intro i hi
    apply hnot
    exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩
  have hz : chamberCoordinates σ e x ρ = 0 := by
    simp [chamberCoordinates, hne]
  exact (Finsupp.mem_support_iff.mp hρ) hz

private theorem chamberCoordinates_mem {K : AbstractSimplicialComplex ι} (σ : Face K)
    (e : VertexOrder σ) (x : orderChamber σ e) :
    chamberCoordinates σ e x ∈
      convexHull ℝ ((fun ρ => Finsupp.single ρ (1 : ℝ)) ''
        (orderedSubdivisionFaces σ e : Set (Face K))) := by
  rw [mem_standardSimplex_iff]
  exact ⟨chamberCoordinates_nonneg σ e x, chamberCoordinates_sum σ e x,
    chamberCoordinates_support σ e x⟩

private noncomputable def chamberStandardSimplex {K : AbstractSimplicialComplex ι}
    (σ : Face K) (e : VertexOrder σ) (x : orderChamber σ e) :
    StandardSimplex (orderedSubdivisionFaces σ e) :=
  ⟨chamberCoordinates σ e x, by simpa using chamberCoordinates_mem σ e x⟩

private theorem continuous_chamberStandardSimplex {K : AbstractSimplicialComplex ι}
    (σ : Face K) (e : VertexOrder σ) : Continuous (chamberStandardSimplex σ e) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro ρ
  have hformula :
      (fun x : orderChamber σ e => (chamberStandardSimplex σ e x : Face K → ℝ) ρ) =
        fun x => ∑ i : Fin σ.1.card,
          if orderedPrefixFace σ e i = ρ then chamberWeight σ e x i else 0 := by
    funext x
    -- Expose the coordinate function carried by the target simplex subtype.
    rw [show (chamberStandardSimplex σ e x : Face K →₀ ℝ) =
      chamberCoordinates σ e x by rfl]
    rw [chamberCoordinates]
    rw [Finset.sum_apply']
    apply Finset.sum_congr rfl
    intro i _
    simp [Finsupp.single_apply, eq_comm]
  -- The induced topology on the target simplex is defined through its coordinate function.
  change Continuous (fun x : orderChamber σ e =>
    (chamberStandardSimplex σ e x : Face K → ℝ) ρ)
  rw [hformula]
  apply continuous_finsetSum
  intro i _
  by_cases h : orderedPrefixFace σ e i = ρ
  · simp only [h, ↓reduceIte]
    exact continuous_chamberWeight σ e i
  · simp only [h, ↓reduceIte]
    exact continuous_const

/-- The chamber formula, included into the whole subdivision realization. -/
private noncomputable def chamberMap {K : AbstractSimplicialComplex ι} (σ : Face K)
    (e : VertexOrder σ) (x : orderChamber σ e) :
    Realization (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      K.toPreAbstractSimplicialComplex) :=
  faceInclusion _ (orderedSubdivisionFace σ e) (chamberStandardSimplex σ e x)

private theorem continuous_chamberMap {K : AbstractSimplicialComplex ι} (σ : Face K)
    (e : VertexOrder σ) : Continuous (chamberMap σ e) :=
  (continuous_faceInclusion _ (orderedSubdivisionFace σ e)).comp
    (continuous_chamberStandardSimplex σ e)

private theorem mem_orderedPrefixVertices_iff {K : AbstractSimplicialComplex ι}
    (σ : Face K) (e : VertexOrder σ) {v : ι} (hv : v ∈ σ.1) (i : Fin σ.1.card) :
    v ∈ orderedPrefixVertices e i ↔ e.symm ⟨v, hv⟩ ≤ i := by
  constructor
  · intro h
    obtain ⟨j, hj, hjv⟩ := Finset.mem_image.1 h
    have heq : j = e.symm ⟨v, hv⟩ := by
      apply e.injective
      apply Subtype.ext
      rw [hjv, e.apply_symm_apply]
    rw [← heq]
    exact Finset.mem_Iic.1 hj
  · intro h
    exact Finset.mem_image.2
      ⟨e.symm ⟨v, hv⟩, Finset.mem_Iic.2 h, by simp⟩

private theorem chamberWeight_mul_card_prefix_inv {K : AbstractSimplicialComplex ι}
    (σ : Face K) (e : VertexOrder σ) (x : orderChamber σ e) (i : Fin σ.1.card) :
    chamberWeight σ e x i * ((orderedPrefixFace σ e i).1.card : ℝ)⁻¹ =
      chamberOrderedCoord σ e x i.1 - chamberOrderedCoord σ e x (i.1 + 1) := by
  rw [chamberWeight, card_orderedPrefixFace]
  have hne : (i.1 + 1 : ℝ) ≠ 0 := by positivity
  field_simp
  norm_num [Nat.cast_add, Nat.cast_one]
  ring

private theorem barycentricSubdivisionLinearMap_chamberCoordinates
    {K : AbstractSimplicialComplex ι} (σ : Face K) (e : VertexOrder σ)
    (x : orderChamber σ e) :
    barycentricSubdivisionLinearMap K (chamberCoordinates σ e x) =
      ∑ i : Fin σ.1.card,
        chamberWeight σ e x i • faceBarycenter K (orderedPrefixFace σ e i) := by
  rw [chamberCoordinates, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finsupp.smul_single_one, map_smul, barycentricSubdivisionLinearMap_single]

private theorem barycentricSubdivisionLinearMap_chamberCoordinates_apply_of_mem
    {K : AbstractSimplicialComplex ι} (σ : Face K) (e : VertexOrder σ)
    (x : orderChamber σ e) {v : ι} (hv : v ∈ σ.1) :
    barycentricSubdivisionLinearMap K (chamberCoordinates σ e x) v = x.1.1 v := by
  rw [barycentricSubdivisionLinearMap_chamberCoordinates]
  simp only [Finset.sum_apply', Finsupp.smul_apply, smul_eq_mul, faceBarycenter_apply]
  let j : Fin σ.1.card := e.symm ⟨v, hv⟩
  calc
    ∑ i : Fin σ.1.card,
        chamberWeight σ e x i *
          (if v ∈ (orderedPrefixFace σ e i).1 then
            ((orderedPrefixFace σ e i).1.card : ℝ)⁻¹ else 0) =
        ∑ i : Fin σ.1.card,
          if j ≤ i then chamberOrderedCoord σ e x i.1 -
            chamberOrderedCoord σ e x (i.1 + 1) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hji : j ≤ i
      · have hmem : v ∈ (orderedPrefixFace σ e i).1 :=
          (mem_orderedPrefixVertices_iff σ e hv i).2 hji
        simp only [hmem, hji, ↓reduceIte]
        exact chamberWeight_mul_card_prefix_inv σ e x i
      · have hmem : v ∉ (orderedPrefixFace σ e i).1 := fun h =>
          hji ((mem_orderedPrefixVertices_iff σ e hv i).1 h)
        simp [hmem, hji]
    _ = ∑ i ∈ Finset.range σ.1.card,
          if j.1 ≤ i then chamberOrderedCoord σ e x i -
            chamberOrderedCoord σ e x (i + 1) else 0 := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i _
      rfl
    _ = chamberOrderedCoord σ e x j.1 - chamberOrderedCoord σ e x σ.1.card :=
      sum_range_ite_le_sub (chamberOrderedCoord σ e x) j.2
    _ = x.1.1 v := by
      rw [chamberOrderedCoord_card, sub_zero, chamberOrderedCoord_of_lt σ e x j.2]
      exact congrArg (fun w : {v // v ∈ σ.1} => x.1.1 w.1)
        (e.apply_symm_apply ⟨v, hv⟩)

private theorem barycentricSubdivisionLinearMap_chamberCoordinates_apply_of_notMem
    {K : AbstractSimplicialComplex ι} (σ : Face K) (e : VertexOrder σ)
    (x : orderChamber σ e) {v : ι} (hv : v ∉ σ.1) :
    barycentricSubdivisionLinearMap K (chamberCoordinates σ e x) v = x.1.1 v := by
  rw [barycentricSubdivisionLinearMap_chamberCoordinates]
  simp only [Finset.sum_apply', Finsupp.smul_apply, smul_eq_mul, faceBarycenter_apply]
  have hprefix : ∀ i : Fin σ.1.card, v ∉ (orderedPrefixFace σ e i).1 :=
    fun i hvi => hv (orderedPrefixVertices_subset e i hvi)
  simp only [hprefix, ↓reduceIte, mul_zero, Finset.sum_const_zero]
  exact (Finsupp.notMem_support_iff.mp
    (fun hsupport => hv (StandardSimplex.support_subset x.1 hsupport))).symm

private theorem chamberMap_val {K : AbstractSimplicialComplex ι} (σ : Face K)
    (e : VertexOrder σ) (x : orderChamber σ e) :
    (chamberMap σ e x : Face K →₀ ℝ) = chamberCoordinates σ e x := by
  exact faceInclusion_val _ (orderedSubdivisionFace σ e) (chamberStandardSimplex σ e x)

private theorem barycentricSubdivisionRealizationMap_chamberMap
    {K : AbstractSimplicialComplex ι} (σ : Face K) (e : VertexOrder σ)
    (x : orderChamber σ e) :
    barycentricSubdivisionRealizationMap K (chamberMap σ e x) = faceInclusion K σ x.1 := by
  apply Subtype.ext
  ext v
  rw [barycentricSubdivisionRealizationMap_val, chamberMap_val, faceInclusion_val]
  by_cases hv : v ∈ σ.1
  · exact barycentricSubdivisionLinearMap_chamberCoordinates_apply_of_mem σ e x hv
  · exact barycentricSubdivisionLinearMap_chamberCoordinates_apply_of_notMem σ e x hv

private theorem continuousOn_iUnion_finset_of_isClosed {α β κ : Type*}
    [TopologicalSpace α] [TopologicalSpace β] {f : α → β} (s : Finset κ) (u : κ → Set α)
    (hu : ∀ i ∈ s, IsClosed (u i)) (hf : ∀ i ∈ s, ContinuousOn f (u i)) :
    ContinuousOn f (⋃ i ∈ s, u i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.set_biUnion_insert]
      exact (hf i (Finset.mem_insert_self i s)).union_of_isClosed
        (ih (fun j hj => hu j (Finset.mem_insert_of_mem hj))
          (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
        (hu i (Finset.mem_insert_self i s))
        (isClosed_biUnion_finset fun j hj => hu j (Finset.mem_insert_of_mem hj))

private theorem continuous_inverse_barycentricSubdivisionRealizationMap
    (K : AbstractSimplicialComplex ι) :
    let e := Equiv.ofBijective (barycentricSubdivisionRealizationMap K)
      (barycentricSubdivisionRealizationMap_bijective K)
    Continuous e.symm := by
  let e := Equiv.ofBijective (barycentricSubdivisionRealizationMap K)
    (barycentricSubdivisionRealizationMap_bijective K)
  apply continuous_iff_faceInclusion.2
  intro σ
  rw [← continuousOn_univ, ← iUnion_orderChamber σ]
  have hpiece : ∀ o : VertexOrder σ,
      ContinuousOn (e.symm ∘ faceInclusion K σ) (orderChamber σ o) := by
    intro o
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : (orderChamber σ o).domRestrict (e.symm ∘ faceInclusion K σ) =
        chamberMap σ o := by
      funext x
      exact e.symm_apply_eq.2 (by
        simpa only [e, Equiv.ofBijective_apply] using
          (barycentricSubdivisionRealizationMap_chamberMap σ o x).symm)
    rw [heq]
    exact continuous_chamberMap σ o
  let _ : Fintype (VertexOrder σ) := Fintype.ofFinite (VertexOrder σ)
  simpa only [Finset.mem_univ, Set.iUnion_true] using
    continuousOn_iUnion_finset_of_isClosed
      (Finset.univ : Finset (VertexOrder σ)) (orderChamber σ)
      (fun o _ => isClosed_orderChamber σ o) (fun o _ => hpiece o)

/-- The canonical homeomorphism from the realization of the barycentric subdivision of `K` to
the realization of `K`. It sends every face-vertex to the barycenter of that face. -/
noncomputable def barycentricSubdivisionRealizationHomeomorph
    (K : AbstractSimplicialComplex ι) :
    Realization (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      K.toPreAbstractSimplicialComplex) ≃ₜ Realization K where
  toEquiv := Equiv.ofBijective (barycentricSubdivisionRealizationMap K)
    (barycentricSubdivisionRealizationMap_bijective K)
  continuous_toFun := continuous_barycentricSubdivisionRealizationMap K
  continuous_invFun := continuous_inverse_barycentricSubdivisionRealizationMap K

/-- The subdivision realization homeomorphism has the canonical affine map as its forward map. -/
@[simp]
theorem barycentricSubdivisionRealizationHomeomorph_apply
    (K : AbstractSimplicialComplex ι)
    (x : Realization (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      K.toPreAbstractSimplicialComplex)) :
    barycentricSubdivisionRealizationHomeomorph K x =
      barycentricSubdivisionRealizationMap K x :=
  (rfl)

end AbstractSimplicialComplex

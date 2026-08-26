/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Realization

/-!
# Surjectivity of the barycentric-subdivision realization map

The canonical realization map sends a vertex of the barycentric subdivision to the barycenter of
the face it represents. This file proves that the map is onto. The proof gives the classical
inverse coordinates explicitly: order the nonzero barycentric coordinates of a point decreasingly,
take the nested initial segments in that order, and express the point as a convex combination of
their barycenters.

This is the first bijectivity step in the subdivision-realization milestone in Layer 11 of the
geometric topology roadmap. Injectivity and continuity of the inverse remain separate steps toward
the homeomorphism between a complex and its barycentric subdivision.

The construction follows Rourke--Sanderson, *Introduction to Piecewise-Linear Topology*, Chapter 2,
"Derived Subdivisions".

## Main result

* `AbstractSimplicialComplex.barycentricSubdivisionRealizationMap_surjective`: every point in the
  realization of a complex is the image of a point in its barycentric subdivision.
-/

public section

noncomputable section

open Finset Set TauCeti TauCeti.SetLike

namespace AbstractSimplicialComplex

variable {ι : Type*}

attribute [local instance] Classical.decEq

@[instance_reducible]
private noncomputable def carrierLinearOrder {K : AbstractSimplicialComplex ι}
    (x : Realization K) : LinearOrder {v // v ∈ (carrier K x).1} :=
  LinearOrder.lift'
    (fun v => toLex (OrderDual.toDual (x.1 v.1), Fintype.equivFin _ v))
    (fun _ _ h => (Fintype.equivFin _).injective
      (congrArg (fun z => (ofLex z).2) h))

/-- The vertices in the carrier of `x`, numbered in decreasing order of their barycentric
coordinate. An arbitrary finite numbering breaks ties. -/
private noncomputable def orderedVertex {K : AbstractSimplicialComplex ι} (x : Realization K) :
    Fin (carrier K x).1.card ≃ {v // v ∈ (carrier K x).1} :=
  let _ := carrierLinearOrder x
  (Fintype.orderIsoFinOfCardEq _ (by simp)).toEquiv

private theorem orderedVertex_antitone {K : AbstractSimplicialComplex ι} (x : Realization K)
    {i j : Fin (carrier K x).1.card} (hij : i ≤ j) :
    x.1 (orderedVertex x j).1 ≤ x.1 (orderedVertex x i).1 := by
  let _ := carrierLinearOrder x
  have h := (Fintype.orderIsoFinOfCardEq
    {v // v ∈ (carrier K x).1} (by simp)).monotone hij
  -- Expose the lexicographic order installed by `carrierLinearOrder` so its first coordinate can
  -- be read as the reverse order on the barycentric coordinates.
  change toLex (OrderDual.toDual (x.1 (orderedVertex x i).1),
      Fintype.equivFin {v // v ∈ (carrier K x).1} (orderedVertex x i)) ≤
    toLex (OrderDual.toDual (x.1 (orderedVertex x j).1),
      Fintype.equivFin {v // v ∈ (carrier K x).1} (orderedVertex x j)) at h
  rw [Prod.Lex.le_iff] at h
  rcases h with h | h
  · exact h.le
  · exact h.1.le

/-- The first `i + 1` carrier vertices in decreasing coordinate order. -/
private noncomputable def prefixVertices {K : AbstractSimplicialComplex ι} (x : Realization K)
    (i : Fin (carrier K x).1.card) : Finset ι :=
  (Finset.Iic i).image fun j => (orderedVertex x j).1

private theorem prefixVertices_nonempty {K : AbstractSimplicialComplex ι} (x : Realization K)
    (i : Fin (carrier K x).1.card) : (prefixVertices x i).Nonempty := by
  exact ⟨(orderedVertex x i).1, Finset.mem_image.2 ⟨i, Finset.mem_Iic.2 le_rfl, rfl⟩⟩

private theorem prefixVertices_subset_carrier {K : AbstractSimplicialComplex ι}
    (x : Realization K) (i : Fin (carrier K x).1.card) :
    prefixVertices x i ⊆ (carrier K x).1 := by
  intro v hv
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hv
  exact (orderedVertex x j).2

private noncomputable def prefixFace {K : AbstractSimplicialComplex ι} (x : Realization K)
    (i : Fin (carrier K x).1.card) : Face K :=
  ⟨prefixVertices x i, K.isRelLowerSet_faces.mem_of_le (carrier K x).2
    (prefixVertices_subset_carrier x i) (prefixVertices_nonempty x i)⟩

private theorem prefixFace_mono {K : AbstractSimplicialComplex ι} (x : Realization K)
    {i j : Fin (carrier K x).1.card} (hij : i ≤ j) : prefixFace x i ≤ prefixFace x j := by
  intro v hv
  obtain ⟨k, hki, rfl⟩ := Finset.mem_image.1 hv
  exact Finset.mem_image.2 ⟨k, Finset.mem_Iic.2 ((Finset.mem_Iic.1 hki).trans hij), rfl⟩

private theorem card_prefixVertices {K : AbstractSimplicialComplex ι} (x : Realization K)
    (i : Fin (carrier K x).1.card) : (prefixVertices x i).card = i.1 + 1 := by
  rw [prefixVertices, Finset.card_image_iff.mpr]
  · exact Fin.card_Iic i
  · exact fun _ _ _ _ h => (orderedVertex x).injective (Subtype.ext h)

private theorem card_prefixFace {K : AbstractSimplicialComplex ι} (x : Realization K)
    (i : Fin (carrier K x).1.card) : (prefixFace x i).1.card = i.1 + 1 :=
  card_prefixVertices x i

private theorem sum_orderedVertex {K : AbstractSimplicialComplex ι} (x : Realization K)
    (g : ι → ℝ) :
    ∑ i : Fin (carrier K x).1.card, g (orderedVertex x i).1 =
      ∑ v ∈ (carrier K x).1, g v := by
  calc
    ∑ i : Fin (carrier K x).1.card, g (orderedVertex x i).1 =
        ∑ v : {v // v ∈ (carrier K x).1}, g v.1 := by
      exact Fintype.sum_equiv (orderedVertex x) _ _ fun _ => rfl
    _ = ∑ v ∈ (carrier K x).1, g v := Finset.sum_attach _ _

/-- Extend the decreasing list of carrier coordinates by zero after its last term. -/
private noncomputable def orderedCoord {K : AbstractSimplicialComplex ι} (x : Realization K)
    (k : ℕ) : ℝ :=
  if h : k < (carrier K x).1.card then x.1 (orderedVertex x ⟨k, h⟩).1 else 0

private theorem orderedCoord_of_lt {K : AbstractSimplicialComplex ι} (x : Realization K)
    {k : ℕ} (hk : k < (carrier K x).1.card) :
    orderedCoord x k = x.1 (orderedVertex x ⟨k, hk⟩).1 := by
  rw [orderedCoord]
  split
  · congr
  · contradiction

private theorem orderedCoord_card {K : AbstractSimplicialComplex ι} (x : Realization K) :
    orderedCoord x (carrier K x).1.card = 0 := by
  simp [orderedCoord]

private theorem orderedCoord_succ_le {K : AbstractSimplicialComplex ι} (x : Realization K)
    {k : ℕ} (hk : k < (carrier K x).1.card) : orderedCoord x (k + 1) ≤ orderedCoord x k := by
  rw [orderedCoord_of_lt x hk]
  by_cases hks : k + 1 < (carrier K x).1.card
  · rw [orderedCoord_of_lt x hks]
    exact orderedVertex_antitone x (Fin.mk_le_mk.mpr (Nat.le_succ k))
  · rw [orderedCoord]
    simp only [hks, ↓reduceDIte]
    exact Realization.nonneg K x _

/-- The barycentric coefficient of the `i`th initial face. -/
private noncomputable def subdivisionWeight {K : AbstractSimplicialComplex ι} (x : Realization K)
    (i : Fin (carrier K x).1.card) : ℝ :=
  (i.1 + 1 : ℝ) * (orderedCoord x i.1 - orderedCoord x (i.1 + 1))

private theorem subdivisionWeight_nonneg {K : AbstractSimplicialComplex ι} (x : Realization K)
    (i : Fin (carrier K x).1.card) : 0 ≤ subdivisionWeight x i := by
  exact mul_nonneg (by positivity) (sub_nonneg.2 (orderedCoord_succ_le x i.2))

/-- Summation by parts for the coefficients used to decompose a simplex into its barycentric
subdivision. -/
private theorem sum_range_succ_mul_sub (f : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, (i + 1 : ℝ) * (f i - f (i + 1)) =
      ∑ i ∈ Finset.range n, f i - (n : ℝ) * f n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
      push_cast
      ring

/-- The tail of a telescoping sum of consecutive differences. -/
private theorem sum_range_ite_le_sub (f : ℕ → ℝ) {j n : ℕ} (hjn : j < n) :
    ∑ i ∈ Finset.range n, (if j ≤ i then f i - f (i + 1) else 0) = f j - f n := by
  induction n with
  | zero => omega
  | succ n ih =>
      rw [Finset.sum_range_succ]
      by_cases hj : j = n
      · subst j
        have hz : ∑ i ∈ Finset.range n, (if n ≤ i then f i - f (i + 1) else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          simp only [Finset.mem_range] at hi
          simp [Nat.not_le_of_lt hi]
        rw [hz]
        simp
      · have hjn' : j < n := by omega
        rw [ih hjn']
        simp only [hjn'.le, ↓reduceIte]
        ring

private theorem sum_orderedCoord {K : AbstractSimplicialComplex ι} (x : Realization K) :
    ∑ k ∈ Finset.range (carrier K x).1.card, orderedCoord x k = 1 := by
  rw [← Fin.sum_univ_eq_sum_range]
  calc
    ∑ i : Fin (carrier K x).1.card, orderedCoord x i =
        ∑ i : Fin (carrier K x).1.card, x.1 (orderedVertex x i).1 := by
      apply Finset.sum_congr rfl
      intro i _
      exact orderedCoord_of_lt x i.2
    _ = ∑ v ∈ (carrier K x).1, x.1 v := sum_orderedVertex x x.1
    _ = 1 := by
      let x' : StandardSimplex (carrier K x).1 := ⟨x.1, mem_convexHull_carrier K x⟩
      simpa only [Finsupp.sum, carrier_val] using StandardSimplex.sum_eq_one x'

private theorem sum_subdivisionWeight {K : AbstractSimplicialComplex ι} (x : Realization K) :
    ∑ i, subdivisionWeight x i = 1 := by
  calc
    ∑ i, subdivisionWeight x i =
        ∑ i ∈ Finset.range (carrier K x).1.card,
          (i + 1 : ℝ) * (orderedCoord x i - orderedCoord x (i + 1)) := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i _
      rfl
    _ = 1 := by
      rw [sum_range_succ_mul_sub, orderedCoord_card, mul_zero, sub_zero, sum_orderedCoord]

/-- The barycentric coordinates on the face-vertices of the subdivision. -/
private noncomputable def subdivisionCoordinates {K : AbstractSimplicialComplex ι}
    (x : Realization K) : Face K →₀ ℝ :=
  ∑ i : Fin (carrier K x).1.card,
    Finsupp.single (prefixFace x i) (subdivisionWeight x i)

/-- The nested face of the barycentric subdivision carrying `subdivisionCoordinates x`. -/
private noncomputable def subdivisionFaces {K : AbstractSimplicialComplex ι} (x : Realization K) :
    Finset (Face K) :=
  Finset.univ.image (prefixFace x)

private theorem subdivisionFaces_nonempty {K : AbstractSimplicialComplex ι} (x : Realization K) :
    (subdivisionFaces x).Nonempty := by
  have hcarrier : (carrier K x).1.Nonempty := K.isRelLowerSet_faces.prop_of_mem (carrier K x).2
  let i : Fin (carrier K x).1.card := ⟨0, Finset.card_pos.mpr hcarrier⟩
  exact ⟨prefixFace x i, Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩⟩

private theorem subdivisionFaces_mem {K : AbstractSimplicialComplex ι} (x : Realization K) :
    subdivisionFaces x ∈ TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      K.toPreAbstractSimplicialComplex := by
  rw [TauCeti.PreAbstractSimplicialComplex.mem_barycentricSubdivision_iff]
  refine ⟨subdivisionFaces_nonempty x, ?_⟩
  intro σ hσ τ hτ hστ
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hσ
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hτ
  exact (le_total i j).imp (prefixFace_mono x) (prefixFace_mono x)

private theorem subdivisionCoordinates_nonneg {K : AbstractSimplicialComplex ι}
    (x : Realization K) (σ : Face K) : 0 ≤ subdivisionCoordinates x σ := by
  rw [subdivisionCoordinates]
  -- Evaluation is the additive homomorphism needed to move through the finite sum of `Finsupp`s.
  change 0 ≤ Finsupp.applyAddHom σ
    (∑ i : Fin (carrier K x).1.card,
      Finsupp.single (prefixFace x i) (subdivisionWeight x i))
  rw [map_sum]
  apply Finset.sum_nonneg
  intro i _
  by_cases h : prefixFace x i = σ
  · simp [h, subdivisionWeight_nonneg]
  · simp [h]

private theorem subdivisionCoordinates_sum {K : AbstractSimplicialComplex ι}
    (x : Realization K) : (subdivisionCoordinates x).sum (fun _ r => r) = 1 := by
  rw [subdivisionCoordinates]
  rw [← Finsupp.sum_finsetSum_index (fun _ => rfl) (fun _ _ _ => rfl)]
  simp only [Finsupp.sum_single_index]
  exact sum_subdivisionWeight x

private theorem subdivisionCoordinates_support {K : AbstractSimplicialComplex ι}
    (x : Realization K) : (subdivisionCoordinates x).support ⊆ subdivisionFaces x := by
  intro σ hσ
  by_contra hnot
  have hne : ∀ i : Fin (carrier K x).1.card, prefixFace x i ≠ σ := by
    intro i hi
    apply hnot
    exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩
  have hz : subdivisionCoordinates x σ = 0 := by
    simp [subdivisionCoordinates, hne]
  exact (Finsupp.mem_support_iff.mp hσ) hz

private theorem subdivisionCoordinates_mem {K : AbstractSimplicialComplex ι}
    (x : Realization K) : subdivisionCoordinates x ∈
      convexHull ℝ ((fun σ => Finsupp.single σ (1 : ℝ)) ''
        (subdivisionFaces x : Set (Face K))) := by
  rw [mem_standardSimplex_iff]
  exact ⟨subdivisionCoordinates_nonneg x, subdivisionCoordinates_sum x,
    subdivisionCoordinates_support x⟩

private noncomputable def subdivisionFace {K : AbstractSimplicialComplex ι} (x : Realization K) :
    Face (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      K.toPreAbstractSimplicialComplex) :=
  ⟨subdivisionFaces x, subdivisionFaces_mem x⟩

private noncomputable def subdivisionStandardSimplex {K : AbstractSimplicialComplex ι}
    (x : Realization K) : StandardSimplex (subdivisionFaces x) :=
  ⟨subdivisionCoordinates x, by simpa using subdivisionCoordinates_mem x⟩

/-- The point of the barycentric subdivision obtained by sorting the barycentric coordinates of
`x` and taking the corresponding nested initial faces. -/
private noncomputable def subdivisionPreimage {K : AbstractSimplicialComplex ι}
    (x : Realization K) :
    Realization (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      K.toPreAbstractSimplicialComplex) :=
  faceInclusion _ (subdivisionFace x) (subdivisionStandardSimplex x)

private theorem subdivisionPreimage_val {K : AbstractSimplicialComplex ι} (x : Realization K) :
    (subdivisionPreimage x : Face K →₀ ℝ) = subdivisionCoordinates x := by
  exact faceInclusion_val _ (subdivisionFace x) (subdivisionStandardSimplex x)

private theorem barycentricSubdivisionLinearMap_subdivisionCoordinates
    {K : AbstractSimplicialComplex ι} (x : Realization K) :
    barycentricSubdivisionLinearMap K (subdivisionCoordinates x) =
      ∑ i : Fin (carrier K x).1.card,
        subdivisionWeight x i • faceBarycenter K (prefixFace x i) := by
  rw [subdivisionCoordinates, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finsupp.smul_single_one, map_smul, barycentricSubdivisionLinearMap_single]

private theorem mem_prefixVertices_iff {K : AbstractSimplicialComplex ι} (x : Realization K)
    {v : ι} (hv : v ∈ (carrier K x).1) (i : Fin (carrier K x).1.card) :
    v ∈ prefixVertices x i ↔ (orderedVertex x).symm ⟨v, hv⟩ ≤ i := by
  constructor
  · intro h
    obtain ⟨j, hj, hjv⟩ := Finset.mem_image.1 h
    have heq : j = (orderedVertex x).symm ⟨v, hv⟩ := by
      apply (orderedVertex x).injective
      apply Subtype.ext
      rw [hjv, Equiv.apply_symm_apply]
    rw [← heq]
    exact Finset.mem_Iic.1 hj
  · intro h
    exact Finset.mem_image.2
      ⟨(orderedVertex x).symm ⟨v, hv⟩, Finset.mem_Iic.2 h, by
        simp only [Equiv.apply_symm_apply]⟩

private theorem subdivisionWeight_mul_card_prefix_inv {K : AbstractSimplicialComplex ι}
    (x : Realization K) (i : Fin (carrier K x).1.card) :
    subdivisionWeight x i * ((prefixFace x i).1.card : ℝ)⁻¹ =
      orderedCoord x i.1 - orderedCoord x (i.1 + 1) := by
  rw [subdivisionWeight, card_prefixFace]
  have hne : (i.1 + 1 : ℝ) ≠ 0 := by positivity
  field_simp
  norm_num [Nat.cast_add, Nat.cast_one]
  ring

private theorem barycentricSubdivisionLinearMap_subdivisionCoordinates_apply_of_mem
    {K : AbstractSimplicialComplex ι} (x : Realization K) {v : ι}
    (hv : v ∈ (carrier K x).1) :
    barycentricSubdivisionLinearMap K (subdivisionCoordinates x) v = x.1 v := by
  rw [barycentricSubdivisionLinearMap_subdivisionCoordinates]
  simp only [Finset.sum_apply', Finsupp.smul_apply, smul_eq_mul, faceBarycenter_apply]
  let j : Fin (carrier K x).1.card := (orderedVertex x).symm ⟨v, hv⟩
  calc
    ∑ i : Fin (carrier K x).1.card,
        subdivisionWeight x i *
          (if v ∈ (prefixFace x i).1 then ((prefixFace x i).1.card : ℝ)⁻¹ else 0) =
        ∑ i : Fin (carrier K x).1.card,
          if j ≤ i then orderedCoord x i.1 - orderedCoord x (i.1 + 1) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hji : j ≤ i
      · have hmem : v ∈ (prefixFace x i).1 := (mem_prefixVertices_iff x hv i).2 hji
        simp only [hmem, hji, ↓reduceIte]
        exact subdivisionWeight_mul_card_prefix_inv x i
      · have hmem : v ∉ (prefixFace x i).1 := fun h =>
          hji ((mem_prefixVertices_iff x hv i).1 h)
        simp [hmem, hji]
    _ = ∑ i ∈ Finset.range (carrier K x).1.card,
          if j.1 ≤ i then orderedCoord x i - orderedCoord x (i + 1) else 0 := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i _
      rfl
    _ = orderedCoord x j.1 - orderedCoord x (carrier K x).1.card :=
      sum_range_ite_le_sub (orderedCoord x) j.2
    _ = x.1 v := by
      rw [orderedCoord_card, sub_zero, orderedCoord_of_lt x j.2]
      exact congrArg (fun w : {v // v ∈ (carrier K x).1} => x.1 w.1)
        ((orderedVertex x).apply_symm_apply ⟨v, hv⟩)

private theorem barycentricSubdivisionLinearMap_subdivisionCoordinates_apply_of_notMem
    {K : AbstractSimplicialComplex ι} (x : Realization K) {v : ι}
    (hv : v ∉ (carrier K x).1) :
    barycentricSubdivisionLinearMap K (subdivisionCoordinates x) v = x.1 v := by
  rw [barycentricSubdivisionLinearMap_subdivisionCoordinates]
  simp only [Finset.sum_apply', Finsupp.smul_apply, smul_eq_mul, faceBarycenter_apply]
  have hprefix : ∀ i : Fin (carrier K x).1.card, v ∉ (prefixFace x i).1 :=
    fun i hvi => hv (prefixVertices_subset_carrier x i hvi)
  simp only [hprefix, ↓reduceIte, mul_zero, Finset.sum_const_zero]
  rw [carrier_val] at hv
  exact (Finsupp.notMem_support_iff.mp hv).symm

private theorem barycentricSubdivisionLinearMap_subdivisionCoordinates_eq
    {K : AbstractSimplicialComplex ι} (x : Realization K) :
    barycentricSubdivisionLinearMap K (subdivisionCoordinates x) = x.1 := by
  ext v
  by_cases hv : v ∈ (carrier K x).1
  · exact barycentricSubdivisionLinearMap_subdivisionCoordinates_apply_of_mem x hv
  · exact barycentricSubdivisionLinearMap_subdivisionCoordinates_apply_of_notMem x hv

private theorem barycentricSubdivisionRealizationMap_subdivisionPreimage
    {K : AbstractSimplicialComplex ι} (x : Realization K) :
    barycentricSubdivisionRealizationMap K (subdivisionPreimage x) = x := by
  apply Subtype.ext
  rw [barycentricSubdivisionRealizationMap_val, subdivisionPreimage_val,
    barycentricSubdivisionLinearMap_subdivisionCoordinates_eq]

/-- The canonical map from the realization of the barycentric subdivision to the realization of
the original complex is surjective.

The preimage is the standard barycentric decomposition: list the nonzero coordinates decreasingly
as `x₀ ≥ ⋯ ≥ xₘ₋₁ > 0`, let `σᵢ` be the face on the first `i + 1` vertices, and give its barycenter
weight `(i + 1) * (xᵢ - xᵢ₊₁)`, with `xₘ = 0`. These weights are nonnegative, sum to one, and their
weighted barycenters telescope coordinatewise to the original point. -/
theorem barycentricSubdivisionRealizationMap_surjective (K : AbstractSimplicialComplex ι) :
    Function.Surjective (barycentricSubdivisionRealizationMap K) := by
  intro x
  exact ⟨subdivisionPreimage x, barycentricSubdivisionRealizationMap_subdivisionPreimage x⟩

end AbstractSimplicialComplex

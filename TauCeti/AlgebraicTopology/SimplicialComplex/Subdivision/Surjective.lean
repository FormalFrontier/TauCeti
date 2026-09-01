/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.BigOperators.Intervals
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Realization

/-!
# Surjectivity of the barycentric-subdivision realization map

The canonical realization map sends a vertex of the barycentric subdivision to the barycenter of
the face it represents. This file proves that the map is onto. The proof gives the classical
inverse coordinates explicitly: order the nonzero barycentric coordinates of a point decreasingly,
take the nested initial segments in that order, and express the point as a convex combination of
their barycenters.

This is the first bijectivity step in the subdivision-realization milestone in Layer 11 of the
geometric topology roadmap. `Subdivision.Injective` proves injectivity, and
`Subdivision.Homeomorph` proves continuity of the inverse.

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

namespace BarycentricSubdivision

/-- A numbering of the vertices of a face. -/
abbrev VertexOrder {K : AbstractSimplicialComplex ι} (σ : Face K) :=
  Fin σ.1.card ≃ {v // v ∈ σ.1}

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

/-- The face on the first `i + 1` vertices in a fixed ordering. -/
private noncomputable def orderedPrefixFace {K : AbstractSimplicialComplex ι} (σ : Face K)
    (e : VertexOrder σ) (i : Fin σ.1.card) : Face K :=
  ⟨orderedPrefixVertices e i, K.isRelLowerSet_faces.mem_of_le σ.2
    (orderedPrefixVertices_subset e i) (orderedPrefixVertices_nonempty e i)⟩

private theorem orderedPrefixFace_val {K : AbstractSimplicialComplex ι} (σ : Face K)
    (e : VertexOrder σ) (i : Fin σ.1.card) :
    (orderedPrefixFace σ e i).1 = orderedPrefixVertices e i := rfl

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
  rw [orderedPrefixFace_val]
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

/-- The simplex of the barycentric subdivision determined by a vertex ordering. -/
private noncomputable def orderedSubdivisionFace {K : AbstractSimplicialComplex ι}
    (σ : Face K) (e : VertexOrder σ) :
    Face (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      K.toPreAbstractSimplicialComplex) :=
  ⟨orderedSubdivisionFaces σ e, orderedSubdivisionFaces_mem σ e⟩

/-- The coefficient of the `i`th initial face for a sequence of ordered coordinates. -/
private def orderedWeight (c : ℕ → ℝ) (i : ℕ) : ℝ :=
  (i + 1 : ℝ) * (c i - c (i + 1))

/-- Summation by parts for consecutive coordinate differences. -/
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
  rw [← Finset.sum_filter]
  have hfilter : (Finset.range n).filter (j ≤ ·) = Finset.Ico j n := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hfilter]
  simpa only [neg_sub_neg] using Finset.sum_Ico_sub (fun k => -f k) hjn.le

/-- The barycentric-subdivision coordinates associated to an ordered coordinate sequence. -/
private noncomputable def orderedCoordinates {K : AbstractSimplicialComplex ι} (σ : Face K)
    (e : VertexOrder σ) (c : ℕ → ℝ) : Face K →₀ ℝ :=
  ∑ i : Fin σ.1.card, Finsupp.single (orderedPrefixFace σ e i) (orderedWeight c i)

private theorem orderedWeight_nonneg (c : ℕ → ℝ) {n : ℕ}
    (hc : ∀ {k}, k < n → c (k + 1) ≤ c k) (i : Fin n) : 0 ≤ orderedWeight c i := by
  exact mul_nonneg (by positivity) (sub_nonneg.2 (hc i.2))

private theorem sum_orderedWeight (c : ℕ → ℝ) (n : ℕ)
    (hsum : ∑ k ∈ Finset.range n, c k = 1) (hcard : c n = 0) :
    ∑ i : Fin n, orderedWeight c i = 1 := by
  calc
    ∑ i : Fin n, orderedWeight c i =
        ∑ i ∈ Finset.range n, (i + 1 : ℝ) * (c i - c (i + 1)) := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i _
      rfl
    _ = 1 := by rw [sum_range_succ_mul_sub, hsum, hcard, mul_zero, sub_zero]

private theorem orderedCoordinates_nonneg {K : AbstractSimplicialComplex ι} (σ : Face K)
    (e : VertexOrder σ) (c : ℕ → ℝ) (hc : ∀ {k}, k < σ.1.card → c (k + 1) ≤ c k)
    (ρ : Face K) : 0 ≤ orderedCoordinates σ e c ρ := by
  rw [orderedCoordinates]
  -- Expose evaluation of the finite `Finsupp` sum so nonnegativity reduces coordinatewise.
  change 0 ≤ Finsupp.applyAddHom ρ
    (∑ i : Fin σ.1.card, Finsupp.single (orderedPrefixFace σ e i) (orderedWeight c i))
  rw [map_sum]
  apply Finset.sum_nonneg
  intro i _
  by_cases h : orderedPrefixFace σ e i = ρ
  · simp [h, orderedWeight_nonneg c hc]
  · simp [h]

private theorem orderedCoordinates_sum {K : AbstractSimplicialComplex ι} (σ : Face K)
    (e : VertexOrder σ) (c : ℕ → ℝ) (hsum : ∑ k ∈ Finset.range σ.1.card, c k = 1)
    (hcard : c σ.1.card = 0) : (orderedCoordinates σ e c).sum (fun _ r => r) = 1 := by
  rw [orderedCoordinates, ← Finsupp.sum_finsetSum_index (fun _ => rfl) (fun _ _ _ => rfl)]
  simp only [Finsupp.sum_single_index]
  exact sum_orderedWeight c σ.1.card hsum hcard

private theorem orderedCoordinates_support {K : AbstractSimplicialComplex ι} (σ : Face K)
    (e : VertexOrder σ) (c : ℕ → ℝ) :
    (orderedCoordinates σ e c).support ⊆ orderedSubdivisionFaces σ e := by
  intro ρ hρ
  by_contra hnot
  have hne : ∀ i : Fin σ.1.card, orderedPrefixFace σ e i ≠ ρ := by
    intro i hi
    apply hnot
    exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩
  have hz : orderedCoordinates σ e c ρ = 0 := by simp [orderedCoordinates, hne]
  exact (Finsupp.mem_support_iff.mp hρ) hz

private theorem orderedCoordinates_mem {K : AbstractSimplicialComplex ι} (σ : Face K)
    (e : VertexOrder σ) (c : ℕ → ℝ) (hc : ∀ {k}, k < σ.1.card → c (k + 1) ≤ c k)
    (hsum : ∑ k ∈ Finset.range σ.1.card, c k = 1) (hcard : c σ.1.card = 0) :
    orderedCoordinates σ e c ∈ convexHull ℝ ((fun ρ => Finsupp.single ρ (1 : ℝ)) ''
      (orderedSubdivisionFaces σ e : Set (Face K))) := by
  rw [mem_standardSimplex_iff]
  exact ⟨orderedCoordinates_nonneg σ e c hc, orderedCoordinates_sum σ e c hsum hcard,
    orderedCoordinates_support σ e c⟩

private noncomputable def orderedStandardSimplex {K : AbstractSimplicialComplex ι}
    (σ : Face K) (e : VertexOrder σ) (c : ℕ → ℝ)
    (hc : ∀ {k}, k < σ.1.card → c (k + 1) ≤ c k)
    (hsum : ∑ k ∈ Finset.range σ.1.card, c k = 1) (hcard : c σ.1.card = 0) :
    StandardSimplex (orderedSubdivisionFaces σ e) :=
  ⟨orderedCoordinates σ e c, by simpa using orderedCoordinates_mem σ e c hc hsum hcard⟩

/-- The point of the barycentric subdivision determined by a face, an ordering of its vertices,
and a decreasing sequence of barycentric coordinates. -/
noncomputable def orderedSubdivisionPoint {K : AbstractSimplicialComplex ι} (σ : Face K)
    (e : VertexOrder σ) (c : ℕ → ℝ) (hc : ∀ {k}, k < σ.1.card → c (k + 1) ≤ c k)
    (hsum : ∑ k ∈ Finset.range σ.1.card, c k = 1) (hcard : c σ.1.card = 0) :
    Realization (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      K.toPreAbstractSimplicialComplex) :=
  faceInclusion _ (orderedSubdivisionFace σ e)
    (orderedStandardSimplex σ e c hc hsum hcard)

private theorem orderedSubdivisionPoint_val {K : AbstractSimplicialComplex ι} (σ : Face K)
    (e : VertexOrder σ) (c : ℕ → ℝ) (hc : ∀ {k}, k < σ.1.card → c (k + 1) ≤ c k)
    (hsum : ∑ k ∈ Finset.range σ.1.card, c k = 1) (hcard : c σ.1.card = 0) :
    (orderedSubdivisionPoint σ e c hc hsum hcard : Face K →₀ ℝ) =
      orderedCoordinates σ e c := by
  exact faceInclusion_val _ (orderedSubdivisionFace σ e)
    (orderedStandardSimplex σ e c hc hsum hcard)

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

private theorem orderedWeight_mul_card_prefix_inv {K : AbstractSimplicialComplex ι}
    (σ : Face K) (e : VertexOrder σ) (c : ℕ → ℝ) (i : Fin σ.1.card) :
    orderedWeight c i * ((orderedPrefixFace σ e i).1.card : ℝ)⁻¹ = c i.1 - c (i.1 + 1) := by
  rw [orderedWeight, card_orderedPrefixFace]
  have hne : (i.1 + 1 : ℝ) ≠ 0 := by positivity
  field_simp
  norm_num [Nat.cast_add, Nat.cast_one]
  ring

private theorem barycentricSubdivisionLinearMap_orderedCoordinates
    {K : AbstractSimplicialComplex ι} (σ : Face K) (e : VertexOrder σ) (c : ℕ → ℝ) :
    barycentricSubdivisionLinearMap K (orderedCoordinates σ e c) =
      ∑ i : Fin σ.1.card, orderedWeight c i • faceBarycenter K (orderedPrefixFace σ e i) := by
  rw [orderedCoordinates, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finsupp.smul_single_one, map_smul, barycentricSubdivisionLinearMap_single]

/-- The shared ordered-coordinate construction maps back to the original simplex point. -/
theorem barycentricSubdivisionRealizationMap_orderedSubdivisionPoint
    {K : AbstractSimplicialComplex ι} (σ : Face K) (e : VertexOrder σ) (c : ℕ → ℝ)
    (hc : ∀ {k}, k < σ.1.card → c (k + 1) ≤ c k)
    (hsum : ∑ k ∈ Finset.range σ.1.card, c k = 1) (hcard : c σ.1.card = 0)
    (x : StandardSimplex σ.1) (hcoord : ∀ i : Fin σ.1.card, c i.1 = x.1 (e i).1) :
    barycentricSubdivisionRealizationMap K (orderedSubdivisionPoint σ e c hc hsum hcard) =
      faceInclusion K σ x := by
  apply Subtype.ext
  ext v
  rw [barycentricSubdivisionRealizationMap_val, orderedSubdivisionPoint_val, faceInclusion_val]
  rw [barycentricSubdivisionLinearMap_orderedCoordinates]
  simp only [Finset.sum_apply', Finsupp.smul_apply, smul_eq_mul, faceBarycenter_apply]
  by_cases hv : v ∈ σ.1
  · let j : Fin σ.1.card := e.symm ⟨v, hv⟩
    calc
      ∑ i : Fin σ.1.card, orderedWeight c i *
          (if v ∈ (orderedPrefixFace σ e i).1 then
            ((orderedPrefixFace σ e i).1.card : ℝ)⁻¹ else 0) =
          ∑ i : Fin σ.1.card, if j ≤ i then c i.1 - c (i.1 + 1) else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hji : j ≤ i
        · have hmem : v ∈ (orderedPrefixFace σ e i).1 :=
            (mem_orderedPrefixVertices_iff σ e hv i).2 hji
          simp only [hmem, hji, ↓reduceIte]
          exact orderedWeight_mul_card_prefix_inv σ e c i
        · have hmem : v ∉ (orderedPrefixFace σ e i).1 := fun h =>
            hji ((mem_orderedPrefixVertices_iff σ e hv i).1 h)
          simp [hmem, hji]
      _ = ∑ i ∈ Finset.range σ.1.card,
            if j.1 ≤ i then c i - c (i + 1) else 0 := by
        rw [← Fin.sum_univ_eq_sum_range]
        apply Finset.sum_congr rfl
        intro i _
        rfl
      _ = c j.1 - c σ.1.card := sum_range_ite_le_sub c j.2
      _ = x.1 v := by
        rw [hcard, sub_zero, hcoord j]
        exact congrArg (fun w : {v // v ∈ σ.1} => x.1 w.1) (e.apply_symm_apply ⟨v, hv⟩)
  · have hprefix : ∀ i : Fin σ.1.card, v ∉ (orderedPrefixFace σ e i).1 :=
      fun i hvi => hv (orderedPrefixVertices_subset e i hvi)
    simp only [hprefix, ↓reduceIte, mul_zero, Finset.sum_const_zero]
    exact (Finsupp.notMem_support_iff.mp
      (fun hsupport => hv (StandardSimplex.support_subset x hsupport))).symm

/-- The shared ordered-coordinate construction is continuous when all its used coordinates are. -/
theorem continuous_orderedSubdivisionPoint {K : AbstractSimplicialComplex ι} {α : Type*}
    [TopologicalSpace α] (σ : Face K) (e : VertexOrder σ) (c : α → ℕ → ℝ)
    (hc : ∀ a {k}, k < σ.1.card → c a (k + 1) ≤ c a k)
    (hsum : ∀ a, ∑ k ∈ Finset.range σ.1.card, c a k = 1)
    (hcard : ∀ a, c a σ.1.card = 0)
    (hcontinuous : ∀ k ≤ σ.1.card, Continuous fun a => c a k) :
    Continuous fun a => orderedSubdivisionPoint σ e (c a) (hc a) (hsum a) (hcard a) := by
  apply (continuous_faceInclusion _ (orderedSubdivisionFace σ e)).comp
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro ρ
  -- The realization and simplex topologies are induced from the ambient coordinate function;
  -- expose that coordinate, then expand the finite `Finsupp.single` sum pointwise.
  change Continuous (fun a => orderedCoordinates σ e (c a) ρ)
  rw [show (fun a => orderedCoordinates σ e (c a) ρ) = fun a =>
      ∑ i : Fin σ.1.card,
        if orderedPrefixFace σ e i = ρ then orderedWeight (c a) i else 0 by
    funext a
    rw [orderedCoordinates, Finset.sum_apply']
    apply Finset.sum_congr rfl
    intro i _
    simp [Finsupp.single_apply, eq_comm]]
  apply continuous_finsetSum
  intro i _
  by_cases hi : orderedPrefixFace σ e i = ρ
  · simp only [hi, ↓reduceIte, orderedWeight]
    exact continuous_const.mul
      ((hcontinuous i.1 i.2.le).sub (hcontinuous (i.1 + 1) (Nat.succ_le_of_lt i.2)))
  · simp only [hi, ↓reduceIte]
    exact continuous_const

end BarycentricSubdivision

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

/-- The point of the barycentric subdivision obtained by sorting the barycentric coordinates of
`x` and taking the corresponding nested initial faces. -/
private noncomputable def subdivisionPreimage {K : AbstractSimplicialComplex ι}
    (x : Realization K) :
    Realization (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      K.toPreAbstractSimplicialComplex) :=
  BarycentricSubdivision.orderedSubdivisionPoint (carrier K x) (orderedVertex x)
    (orderedCoord x) (orderedCoord_succ_le x) (sum_orderedCoord x) (orderedCoord_card x)

private theorem barycentricSubdivisionRealizationMap_subdivisionPreimage
    {K : AbstractSimplicialComplex ι} (x : Realization K) :
    barycentricSubdivisionRealizationMap K (subdivisionPreimage x) = x := by
  let x' : StandardSimplex (carrier K x).1 := ⟨x.1, mem_convexHull_carrier K x⟩
  calc
    barycentricSubdivisionRealizationMap K (subdivisionPreimage x) =
        faceInclusion K (carrier K x) x' := by
      exact BarycentricSubdivision.barycentricSubdivisionRealizationMap_orderedSubdivisionPoint
        (carrier K x) (orderedVertex x) (orderedCoord x) (orderedCoord_succ_le x)
        (sum_orderedCoord x) (orderedCoord_card x) x' (fun i => orderedCoord_of_lt x i.2)
    _ = x := by
      apply Subtype.ext
      exact faceInclusion_val K (carrier K x) x'

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

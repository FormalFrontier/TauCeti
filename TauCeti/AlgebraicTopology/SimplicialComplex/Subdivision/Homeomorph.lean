/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Injective

/-!
# The realization homeomorphism for barycentric subdivision

The canonical map from the realization of the barycentric subdivision of a simplicial complex to
the realization of the original complex is a homeomorphism. The forward map sends a face-vertex to
the barycenter of that face and extends affinely over subdivision simplices.

Continuity of the inverse is proved simplex by simplex, using the weak topology on realizations.
Each original simplex is covered by the finitely many closed chambers obtained by ordering its
barycentric coordinates. On one chamber the inverse has a fixed affine formula: cardinality-scaled
consecutive coordinate differences are the coefficients of the nested initial faces in that order.
These formulas are continuous and agree on chamber intersections because the forward map is
injective.

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
  BarycentricSubdivision.VertexOrder σ

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

/-- The chamber formula, included into the whole subdivision realization. -/
private noncomputable def chamberMap {K : AbstractSimplicialComplex ι} (σ : Face K)
    (e : VertexOrder σ) (x : orderChamber σ e) :
    Realization (TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision
      K.toPreAbstractSimplicialComplex) :=
  BarycentricSubdivision.orderedSubdivisionPoint σ e (chamberOrderedCoord σ e x)
    (chamberOrderedCoord_succ_le σ e x) (sum_chamberOrderedCoord σ e x)
    (chamberOrderedCoord_card σ e x)

private theorem continuous_chamberMap {K : AbstractSimplicialComplex ι} (σ : Face K)
    (e : VertexOrder σ) : Continuous (chamberMap σ e) := by
  exact BarycentricSubdivision.continuous_orderedSubdivisionPoint σ e
    (fun x k => chamberOrderedCoord σ e x k)
    (fun x _ hk => chamberOrderedCoord_succ_le σ e x hk)
    (sum_chamberOrderedCoord σ e) (chamberOrderedCoord_card σ e)
    (fun k _ => continuous_chamberOrderedCoord σ e k)

private theorem barycentricSubdivisionRealizationMap_chamberMap
    {K : AbstractSimplicialComplex ι} (σ : Face K) (e : VertexOrder σ)
    (x : orderChamber σ e) :
    barycentricSubdivisionRealizationMap K (chamberMap σ e x) = faceInclusion K σ x.1 := by
  exact BarycentricSubdivision.barycentricSubdivisionRealizationMap_orderedSubdivisionPoint
    σ e (chamberOrderedCoord σ e x) (chamberOrderedCoord_succ_le σ e x)
    (sum_chamberOrderedCoord σ e x) (chamberOrderedCoord_card σ e x) x.1
    (fun i => chamberOrderedCoord_of_lt σ e x i.2)

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

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Collapse.FaceCount
public import TauCeti.AlgebraicTopology.SimplicialComplex.Cone
import Mathlib.Order.Preorder.Finite

/-!
# A finite cone collapses to its apex

A simplicial complex is a *cone with apex `v`* when `v` is one of its vertices and adjoining
`v` to any face gives a face again.  The basic collapsing theorem of piecewise-linear topology
(Rourke--Sanderson, *Introduction to Piecewise-Linear Topology*, Chapter 3) says that a finite
cone collapses to its apex; in particular every finite cone is collapsible.

This file proves that theorem for the collapse relation of
`TauCeti.PreAbstractSimplicialComplex.CollapsesTo`, and reads it off for the standard cones:
an abstract simplex, the closed star of a face, and the cone construction
`TauCeti.PreAbstractSimplicialComplex.cone`.  Before this, `Collapsible` was known only for the
one-vertex complexes of `Collapsible.point`; these theorems supply collapsible complexes of
arbitrarily many faces, and the simplex case is the base of the recursion on combinatorial balls
in layer 11 of the geometric-topology roadmap
(`TauCetiRoadmap/GeometricTopology/README.md`).

The cone predicate `IsCone` and the recognition of the standard cones live with the cone
construction in `TauCeti.AlgebraicTopology.SimplicialComplex.Cone`; this file adds only what
depends on collapse theory.

The proof is the usual one: pick a face `σ` maximal among the faces missing the apex.
Maximality makes `σ` a free face with unique proper coface `insert v σ`, deleting it leaves a
smaller cone with the same apex, and the face count of `Collapse.FaceCount` provides the
termination measure.

## Main results

* `PreAbstractSimplicialComplex.IsCone.collapsesTo_point`: a finite cone collapses to its apex.
* `PreAbstractSimplicialComplex.IsCone.collapsible`: a finite cone is collapsible.
* `PreAbstractSimplicialComplex.collapsesTo_point_simplex`: an abstract simplex collapses to any
  of its vertices.
* `PreAbstractSimplicialComplex.collapsesTo_point_closedStar`: a finite closed star of a face
  collapses to any vertex of that face.
* `PreAbstractSimplicialComplex.collapsesTo_point_cone`: the cone on a finite complex collapses
  to its apex.
-/

public section

namespace TauCeti

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι] {K : _root_.PreAbstractSimplicialComplex ι}
  {v : ι} {σ : Finset ι}

/-- The one-vertex complex is a cone with apex its vertex. -/
theorem isCone_point (v : ι) : IsCone (point v) v where
  apex_mem := mem_point.mpr rfl
  insert_mem σ hσ := by
    rw [mem_point.mp hσ]
    simp

/-- In a cone, a face `σ` missing the apex and maximal with that property is a free face, with
`insert v σ` as its unique proper coface.

Maximality is used twice: a coface of `σ` missing the apex is `σ` itself, and a coface `ω`
containing the apex has `ω.erase v` a coface of `σ` missing the apex, hence equal to `σ`. -/
theorem IsCone.isFreePair (h : IsCone K v) (hσ : σ ∈ K) (hv : v ∉ σ)
    (hmax : ∀ ⦃τ : Finset ι⦄, τ ∈ K → v ∉ τ → σ ⊆ τ → τ = σ) :
    IsFreePair K σ (insert v σ) where
  lower_mem := hσ
  upper_mem := h.insert_mem hσ
  lower_ssubset_upper := Finset.ssubset_insert hv
  eq_lower_or_eq_upper ω hω hσω := by
    by_cases hvω : v ∈ ω
    · refine Or.inr ?_
      have hsub : σ ⊆ ω.erase v := Finset.subset_erase.mpr ⟨hσω, hv⟩
      have hmem : ω.erase v ∈ K :=
        (K.isRelLowerSet_faces hω).2 (Finset.erase_subset _ _)
          (((K.isRelLowerSet_faces hσ).1).mono hsub)
      rw [← hmax hmem (Finset.notMem_erase _ _) hsub, Finset.insert_erase hvω]
    · exact Or.inl (hmax hω hvω hσω)

omit [DecidableEq ι] in
/-- A finite complex with a face missing `v` has one that is maximal among the faces missing
`v`. -/
private theorem exists_maximal_notMem_of_mem (hfin : K.faces.Finite) (hσ : σ ∈ K) (hv : v ∉ σ) :
    ∃ τ ∈ K, v ∉ τ ∧ ∀ ⦃ω : Finset ι⦄, ω ∈ K → v ∉ ω → τ ⊆ ω → ω = τ := by
  obtain ⟨τ, -, hτ⟩ :=
    (hfin.subset fun _ hρ => hρ.1 : {ρ : Finset ι | ρ ∈ K ∧ v ∉ ρ}.Finite).exists_le_maximal
      (show σ ∈ {ρ : Finset ι | ρ ∈ K ∧ v ∉ ρ} from ⟨hσ, hv⟩)
  exact ⟨τ, hτ.prop.1, hτ.prop.2, fun _ hω hvω hτω => hτ.eq_of_ge ⟨hω, hvω⟩ hτω⟩

/-- A cone with apex `v` that is not the one-vertex complex at `v` has a face missing `v`. -/
theorem IsCone.exists_notMem_of_ne_point (h : IsCone K v) (hne : K ≠ point v) :
    ∃ σ ∈ K, v ∉ σ := by
  by_contra hcon
  have hall : ∀ ⦃τ : Finset ι⦄, τ ∈ K → v ∈ τ := fun τ hτ =>
    not_not.mp fun hv => hcon ⟨τ, hτ, hv⟩
  refine hne (le_antisymm (fun σ hσ => ?_) (point_le_iff.mpr h.apex_mem))
  refine mem_point.mpr (Finset.eq_singleton_iff_unique_mem.mpr ⟨hall hσ, fun w hw => ?_⟩)
  have hwK : ({w} : Finset ι) ∈ K :=
    (K.isRelLowerSet_faces hσ).2 (Finset.singleton_subset_iff.mpr hw)
      (Finset.singleton_nonempty w)
  exact (Finset.mem_singleton.mp (hall hwK)).symm

/-- The collapse of a finite cone to its apex, by induction on a bound for the face count: each
elementary collapse removes a maximal apex-free face together with its unique coface, and leaves
a cone with the same apex. -/
private theorem collapsesTo_point_aux (v : ι) :
    ∀ (n : ℕ) (K : _root_.PreAbstractSimplicialComplex ι), K.faces.Finite →
      K.faces.ncard ≤ n → IsCone K v → CollapsesTo K (point v) := by
  intro n
  induction n with
  | zero =>
    intro K hfin hcard h
    have hempty : K.faces = ∅ := (Set.ncard_eq_zero hfin).mp (Nat.le_zero.mp hcard)
    have hmem : ({v} : Finset ι) ∈ K.faces := h.apex_mem
    rw [hempty] at hmem
    exact absurd hmem (Set.notMem_empty _)
  | succ n ih =>
    intro K hfin hcard h
    rcases eq_or_ne K (point v) with rfl | hne
    · exact CollapsesTo.refl _
    obtain ⟨σ₀, hσ₀, hv₀⟩ := h.exists_notMem_of_ne_point hne
    obtain ⟨σ, hσ, hvσ, hmax⟩ := exists_maximal_notMem_of_mem hfin hσ₀ hv₀
    have hcollapse : ElementaryCollapsesTo K (deletion K σ) :=
      ElementaryCollapsesTo.of_isFreePair (h.isFreePair hσ hvσ hmax) rfl
    have hlt := hcollapse.ncard_faces_lt hfin
    exact CollapsesTo.head hcollapse
      (ih _ (hfin.subset deletion_le) (by omega)
        (isCone_deletion h (K.isRelLowerSet_faces hσ).1 hvσ))

/-- **A finite cone collapses to its apex** (Rourke--Sanderson, *Introduction to
Piecewise-Linear Topology*, Chapter 3). -/
theorem IsCone.collapsesTo_point (h : IsCone K v) (hfin : K.faces.Finite) :
    CollapsesTo K (point v) :=
  collapsesTo_point_aux v _ K hfin le_rfl h

/-- A finite cone is collapsible. -/
theorem IsCone.collapsible (h : IsCone K v) (hfin : K.faces.Finite) : Collapsible K :=
  collapsible_iff.mpr ⟨v, h.collapsesTo_point hfin⟩

section Simplex

variable {V : Finset ι}

omit [DecidableEq ι] in
/-- An abstract simplex collapses to any of its vertices. -/
theorem collapsesTo_point_simplex (hv : v ∈ V) : CollapsesTo (simplex V) (point v) := by
  classical
  exact (isCone_simplex hv).collapsesTo_point (finite_faces_simplex V)

omit [DecidableEq ι] in
/-- An abstract simplex on a nonempty spanning set is collapsible.  Its face count grows with
the spanning set, so this exhibits collapsible complexes with arbitrarily many faces, beyond the
one-vertex complexes of `Collapsible.point`. -/
theorem collapsible_simplex (hV : V.Nonempty) : Collapsible (simplex V) := by
  obtain ⟨v, hv⟩ := hV
  exact collapsible_iff.mpr ⟨v, collapsesTo_point_simplex hv⟩

end Simplex

section ClosedStar

/-- A finite closed star of a face collapses to any vertex of that face. -/
theorem collapsesTo_point_closedStar (hfin : (closedStar K σ).faces.Finite) (hσ : σ ∈ K)
    (hv : v ∈ σ) : CollapsesTo (closedStar K σ) (point v) :=
  (isCone_closedStar hσ hv).collapsesTo_point hfin

/-- A finite closed star of a face is collapsible. -/
theorem collapsible_closedStar (hfin : (closedStar K σ).faces.Finite) (hσ : σ ∈ K) :
    Collapsible (closedStar K σ) := by
  obtain ⟨v, hv⟩ := (K.isRelLowerSet_faces hσ).1
  exact collapsible_iff.mpr ⟨v, collapsesTo_point_closedStar hfin hσ hv⟩

end ClosedStar

section Cone

variable {α : Type*} [DecidableEq α] {L : _root_.PreAbstractSimplicialComplex α}

omit [DecidableEq α] in
/-- The cone on a finite complex collapses to its apex. -/
theorem collapsesTo_point_cone (hfin : L.faces.Finite) :
    CollapsesTo (cone L) (point (Sum.inr PUnit.unit)) := by
  classical
  exact (isCone_cone L).collapsesTo_point (finite_faces_cone hfin)

omit [DecidableEq α] in
/-- The cone on a finite complex is collapsible. -/
theorem collapsible_cone (hfin : L.faces.Finite) : Collapsible (cone L) :=
  collapsible_iff.mpr ⟨_, collapsesTo_point_cone hfin⟩

end Cone

end PreAbstractSimplicialComplex

end TauCeti

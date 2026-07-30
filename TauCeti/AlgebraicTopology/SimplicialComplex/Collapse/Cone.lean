/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Set.Finite.Lemmas
public import TauCeti.AlgebraicTopology.SimplicialComplex.Collapse.FaceCount
public import TauCeti.AlgebraicTopology.SimplicialComplex.Cone

/-!
# A finite cone collapses to its apex

A simplicial complex is a *cone with apex `v`* when `v` is one of its vertices and adjoining
`v` to any face gives a face again.  The basic collapsing theorem of piecewise-linear topology
(Rourke--Sanderson, *Introduction to Piecewise-Linear Topology*, Chapter 3) says that a finite
cone collapses to its apex; in particular every finite cone is collapsible.

This file proves that theorem for the collapse relation of
`TauCeti.PreAbstractSimplicialComplex.CollapsesTo`, and reads it off for the standard cones:
an abstract simplex, the closed star of a vertex, and the cone construction
`TauCeti.PreAbstractSimplicialComplex.cone`.  These are the first complexes known to be
collapsible, so they are what keeps `Collapsible` from being vacuous, and the simplex case is
the base of the recursion on combinatorial balls in layer 11 of the geometric-topology roadmap
(`TauCetiRoadmap/GeometricTopology/README.md`).

The predicate `IsCone` is phrased inside a fixed vertex type, unlike `cone`, which enlarges the
vertex type by an apex.  Keeping it internal is what lets the theorem apply to complexes that
happen to be cones — simplices and closed stars — rather than only to complexes literally built
by `cone`; `isCone_cone` records that the two accounts agree.

The proof is the usual one: pick a face `σ` of maximal cardinality among the faces missing the
apex.  Maximality makes `σ` a free face with unique proper coface `insert v σ`, deleting it
leaves a smaller cone with the same apex, and the face count of `Collapse.FaceCount` provides
the termination measure.

## Main definitions

* `PreAbstractSimplicialComplex.IsCone`: a complex is a cone with a given apex.

## Main results

* `PreAbstractSimplicialComplex.IsCone.collapsesTo_point`: a finite cone collapses to its apex.
* `PreAbstractSimplicialComplex.IsCone.collapsible`: a finite cone is collapsible.
* `PreAbstractSimplicialComplex.collapsesTo_point_simplex`: an abstract simplex collapses to any
  of its vertices.
* `PreAbstractSimplicialComplex.collapsesTo_point_closedStar`: the closed star of a vertex of a
  finite complex collapses to that vertex.
* `PreAbstractSimplicialComplex.collapsesTo_point_cone`: the cone on a finite complex collapses
  to its apex.
-/

public section

namespace TauCeti

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι] {K : _root_.PreAbstractSimplicialComplex ι}
  {v : ι} {σ : Finset ι}

/-- `K` is a **cone with apex `v`** when `v` is a vertex of `K` and adjoining `v` to a face of
`K` again gives a face of `K`.

This is the internal form of the cone condition: the apex is a vertex of the ambient type of
`K` itself, so a complex can be recognised as a cone without changing its vertex type. The
`cone` construction of `TauCeti.PreAbstractSimplicialComplex.cone` satisfies it at its apex
(`isCone_cone`). -/
structure IsCone (K : _root_.PreAbstractSimplicialComplex ι) (v : ι) : Prop where
  /-- The apex is a vertex of the complex. -/
  apex_mem : ({v} : Finset ι) ∈ K
  /-- Adjoining the apex to a face gives a face. -/
  insert_mem : ∀ ⦃σ : Finset ι⦄, σ ∈ K → insert v σ ∈ K

/-- The one-vertex complex is a cone with apex its vertex. -/
theorem isCone_point (v : ι) : IsCone (point v) v where
  apex_mem := mem_point.mpr rfl
  insert_mem σ hσ := by
    rw [mem_point.mp hσ]
    simp

/-- A cone with apex `v` is nonempty. -/
theorem IsCone.ne_bot (h : IsCone K v) : K ≠ ⊥ := fun hK =>
  (hK ▸ h.apex_mem : ({v} : Finset ι) ∈ (⊥ : _root_.PreAbstractSimplicialComplex ι)).elim

/-- Deleting a nonempty face that misses the apex leaves a cone with the same apex. Note that
the deletion of a face *containing* the apex need not be a cone: deleting `{v}` itself destroys
the apex. -/
theorem isCone_deletion (h : IsCone K v) (hσ : σ.Nonempty) (hv : v ∉ σ) :
    IsCone (deletion K σ) v where
  apex_mem := by
    refine mem_deletion.mpr ⟨h.apex_mem, fun hsub => ?_⟩
    rcases Finset.subset_singleton_iff.mp hsub with rfl | rfl
    · exact hσ.ne_empty rfl
    · exact hv (Finset.mem_singleton_self v)
  insert_mem ω hω := by
    rw [mem_deletion] at hω ⊢
    exact ⟨h.insert_mem hω.1, fun hsub =>
      hω.2 ((Finset.subset_insert_iff_of_notMem hv).mp hsub)⟩

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
theorem exists_maximal_notMem_of_mem (hfin : K.faces.Finite) (hσ : σ ∈ K) (hv : v ∉ σ) :
    ∃ τ ∈ K, v ∉ τ ∧ ∀ ⦃ω : Finset ι⦄, ω ∈ K → v ∉ ω → τ ⊆ ω → ω = τ := by
  obtain ⟨τ, hτ, hmax⟩ :=
    Set.exists_max_image {ρ : Finset ι | ρ ∈ K ∧ v ∉ ρ} Finset.card
      (hfin.subset fun _ hρ => hρ.1) ⟨σ, hσ, hv⟩
  exact ⟨τ, hτ.1, hτ.2, fun _ hω hvω hτω =>
    (Finset.eq_of_subset_of_card_le hτω (hmax _ ⟨hω, hvω⟩)).symm⟩

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

/-- An abstract simplex is a cone with apex any of its vertices. -/
theorem isCone_simplex (hv : v ∈ V) : IsCone (simplex V) v where
  apex_mem := mem_simplex.mpr ⟨Finset.singleton_nonempty v, Finset.singleton_subset_iff.mpr hv⟩
  insert_mem σ hσ :=
    mem_simplex.mpr ⟨Finset.insert_nonempty v σ, Finset.insert_subset hv (mem_simplex.mp hσ).2⟩

omit [DecidableEq ι] in
/-- An abstract simplex has finitely many faces: they are subsets of the spanning set. -/
theorem faces_finite_simplex (V : Finset ι) : (simplex V).faces.Finite :=
  V.powerset.finite_toSet.subset fun _ hσ => Finset.mem_powerset.mpr (mem_simplex.mp hσ).2

omit [DecidableEq ι] in
/-- An abstract simplex collapses to any of its vertices. -/
theorem collapsesTo_point_simplex (hv : v ∈ V) : CollapsesTo (simplex V) (point v) := by
  classical
  exact (isCone_simplex hv).collapsesTo_point (faces_finite_simplex V)

omit [DecidableEq ι] in
/-- An abstract simplex on a nonempty spanning set is collapsible.  Since a simplex is a
genuinely large complex, this is the non-vacuity check for `Collapsible`. -/
theorem collapsible_simplex (hV : V.Nonempty) : Collapsible (simplex V) := by
  obtain ⟨v, hv⟩ := hV
  exact collapsible_iff.mpr ⟨v, collapsesTo_point_simplex hv⟩

end Simplex

section ClosedStar

/-- The closed star of a vertex is a cone with that vertex as apex: adjoining `v` to a face of
the closed star is idempotent on the defining condition. -/
theorem isCone_closedStar_singleton (hv : ({v} : Finset ι) ∈ K) :
    IsCone (closedStar K {v}) v where
  apex_mem := mem_closedStar_singleton.mpr ⟨hv, by simpa using hv⟩
  insert_mem σ hσ := by
    rw [mem_closedStar_singleton] at hσ ⊢
    exact ⟨hσ.2, by rw [Finset.insert_idem]; exact hσ.2⟩

/-- The closed star of a vertex of a finite complex collapses to that vertex. -/
theorem collapsesTo_point_closedStar (hfin : K.faces.Finite) (hv : ({v} : Finset ι) ∈ K) :
    CollapsesTo (closedStar K {v}) (point v) :=
  (isCone_closedStar_singleton hv).collapsesTo_point (hfin.subset closedStar_le)

/-- The closed star of a vertex of a finite complex is collapsible. -/
theorem collapsible_closedStar (hfin : K.faces.Finite) (hv : ({v} : Finset ι) ∈ K) :
    Collapsible (closedStar K {v}) :=
  collapsible_iff.mpr ⟨v, collapsesTo_point_closedStar hfin hv⟩

end ClosedStar

section Cone

variable {α : Type*} [DecidableEq α] {L : _root_.PreAbstractSimplicialComplex α}

/-- The cone construction produces a cone in the internal sense, with apex the adjoined
vertex.  This is what identifies the two accounts of a cone. -/
theorem isCone_cone (L : _root_.PreAbstractSimplicialComplex α) :
    IsCone (cone L) (Sum.inr PUnit.unit) where
  apex_mem := apex_mem_cone
  insert_mem σ hσ := by
    rw [mem_cone_iff] at hσ ⊢
    exact ⟨Finset.insert_nonempty _ _, by rw [Finset.toLeft_insert_inr]; exact hσ.2⟩

omit [DecidableEq α] in
/-- The cone on a finite complex is finite: a face of the cone is determined by its two
projections, the left one is empty or a face of the base, and the apex type is finite. -/
theorem faces_finite_cone (hfin : L.faces.Finite) : (cone L).faces.Finite := by
  have hinj : Function.Injective
      (fun σ : Finset (α ⊕ PUnit) => (σ.toLeft, σ.toRight)) := by
    intro a b hab
    rw [Prod.mk.injEq] at hab
    rw [← Finset.toLeft_disjSum_toRight (u := a), ← Finset.toLeft_disjSum_toRight (u := b),
      hab.1, hab.2]
  refine Set.Finite.of_finite_image (Set.Finite.subset
    ((hfin.insert ∅).prod (Set.finite_univ (α := Finset PUnit))) ?_) hinj.injOn
  rintro _ ⟨σ, hσ, rfl⟩
  exact Set.mem_prod.mpr ⟨Set.mem_insert_iff.mpr (mem_cone_iff.mp hσ).2, Set.mem_univ _⟩

omit [DecidableEq α] in
/-- The cone on a finite complex collapses to its apex. -/
theorem collapsesTo_point_cone (hfin : L.faces.Finite) :
    CollapsesTo (cone L) (point (Sum.inr PUnit.unit)) := by
  classical
  exact (isCone_cone L).collapsesTo_point (faces_finite_cone hfin)

omit [DecidableEq α] in
/-- The cone on a finite complex is collapsible. -/
theorem collapsible_cone (hfin : L.faces.Finite) : Collapsible (cone L) :=
  collapsible_iff.mpr ⟨_, collapsesTo_point_cone hfin⟩

end Cone

end PreAbstractSimplicialComplex

end TauCeti

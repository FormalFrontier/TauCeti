/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Collapse.Basic

/-!
# Relabeling simplicial collapses

Simplicial collapse is intrinsic to a complex and must not depend on its ambient vertex names.
This file proves that an injective relabeling carries free pairs, elementary collapses, finite
collapse sequences, and collapsibility to the corresponding image complexes. In particular, a
vertex equivalence preserves and reflects both `CollapsesTo` and `Collapsible`.

This is functorial infrastructure for the collapse track in layer 11 of the geometric-topology
roadmap. It lets later subdivision and product constructions replace a complex by an isomorphic
copy before forming collapse sequences. The definitions of free pairs and collapse follow
Rourke--Sanderson, *Introduction to Piecewise-Linear Topology*, Chapter 3; the results here are
the standard invariance of those definitions under a change of vertex labels.

## Main results

* `PreAbstractSimplicialComplex.IsFreePair.map`: an injective vertex map preserves a free pair.
* `PreAbstractSimplicialComplex.ElementaryCollapsesTo.map`: an injective vertex map preserves an
  elementary collapse.
* `PreAbstractSimplicialComplex.CollapsesTo.map`: an injective vertex map preserves a finite
  collapse sequence.
* `PreAbstractSimplicialComplex.CollapsesTo.map_equiv_iff`: relabeling by a vertex equivalence
  preserves and reflects a collapse sequence.
* `PreAbstractSimplicialComplex.Collapsible.map_equiv_iff`: relabeling by a vertex equivalence
  preserves and reflects collapsibility.
-/

public section

namespace TauCeti

namespace PreAbstractSimplicialComplex

variable {α β : Type*} [DecidableEq β]
variable {K L : _root_.PreAbstractSimplicialComplex α}

private theorem mem_map_iff {f : α → β} {K : _root_.PreAbstractSimplicialComplex α}
    {σ : Finset β} : σ ∈ K.map f ↔ ∃ τ, τ ∈ K ∧ τ.image f = σ :=
  Iff.rfl

/-- Mapping a one-vertex complex along any vertex map gives the one-vertex complex at the image
vertex. -/
@[simp]
theorem map_point (f : α → β) (v : α) : (point v).map f = point (f v) := by
  refine SetLike.ext fun σ => ?_
  rw [mem_map_iff, mem_point]
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    rw [mem_point] at hτ
    subst τ
    simp
  · rintro rfl
    exact ⟨{v}, mem_point.mpr rfl, by simp⟩

/-- An injective vertex map commutes with deletion: a face contains the image of `σ` exactly when
its unique preimage face contains `σ`. -/
theorem map_deletion (f : α → β) (hf : Function.Injective f) (K : PreAbstractSimplicialComplex α)
    (σ : Finset α) : (deletion K σ).map f = deletion (K.map f) (σ.image f) := by
  refine SetLike.ext fun ω => ?_
  constructor
  · intro hω
    obtain ⟨ρ, hρ, rfl⟩ := mem_map_iff.mp hω
    obtain ⟨hρK, hσρ⟩ := mem_deletion.mp hρ
    refine mem_deletion.mpr ⟨mem_map_iff.mpr ⟨ρ, hρK, rfl⟩, fun h => hσρ ?_⟩
    exact (Finset.image_subset_image_iff hf).mp h
  · intro hω
    obtain ⟨hωK, hσρ⟩ := mem_deletion.mp hω
    obtain ⟨ρ, hρK, hρω⟩ := mem_map_iff.mp hωK
    subst ω
    refine mem_map_iff.mpr ⟨ρ, mem_deletion.mpr ⟨hρK, fun h => hσρ ?_⟩, rfl⟩
    exact Finset.image_subset_image h

namespace IsFreePair

variable {σ τ : Finset α}

/-- An injective relabeling of the vertices of a complex carries a free pair to a free pair in
the image complex. -/
theorem map (h : IsFreePair K σ τ) (f : α → β) (hf : Function.Injective f) :
    IsFreePair (K.map f) (σ.image f) (τ.image f) where
  lower_mem := mem_map_iff.mpr ⟨σ, h.lower_mem, rfl⟩
  upper_mem := mem_map_iff.mpr ⟨τ, h.upper_mem, rfl⟩
  lower_ssubset_upper := (Finset.image_ssubset_image hf).mpr h.lower_ssubset_upper
  eq_lower_or_eq_upper := by
    rintro ω hω hσω
    obtain ⟨ρ, hρK, rfl⟩ := mem_map_iff.mp hω
    have hσρ : σ ⊆ ρ := (Finset.image_subset_image_iff hf).mp hσω
    rcases h.eq_lower_or_eq_upper hρK hσρ with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl

end IsFreePair

namespace ElementaryCollapsesTo

/-- An injective relabeling preserves an elementary collapse. The deleted free pair is sent to
its image pair. -/
theorem map (h : ElementaryCollapsesTo K L) (f : α → β) (hf : Function.Injective f) :
    ElementaryCollapsesTo (K.map f) (L.map f) := by
  obtain ⟨σ, τ, hfree, _, hmem⟩ := h.exists_pair
  have hL : L = deletion K σ := SetLike.ext fun ω =>
    (hmem ω).trans <| (mem_deletion_of_isFreePair K hfree).symm.trans mem_deletion.symm
  subst L
  exact of_isFreePair (hfree.map f hf) (map_deletion f hf K σ)

end ElementaryCollapsesTo

namespace CollapsesTo

/-- An injective relabeling carries every finite collapse sequence to the corresponding sequence
between the image complexes. -/
theorem map (h : CollapsesTo K L) (f : α → β) (hf : Function.Injective f) :
    CollapsesTo (K.map f) (L.map f) := by
  apply h.property_of_elementaryCollapsesTo
      (p := fun P => CollapsesTo (K.map f) (P.map f))
  · intro A B hAB hA
    exact hA.tail (hAB.map f hf)
  · exact refl _

/-- Relabeling both complexes by a vertex equivalence preserves and reflects the existence of a
finite collapse sequence. -/
theorem map_equiv_iff (e : α ≃ β) :
    CollapsesTo (K.map e) (L.map e) ↔ CollapsesTo K L := by
  classical
  have map_symm (P : PreAbstractSimplicialComplex α) : (P.map e).map e.symm = P := by
    refine SetLike.ext fun σ => ?_
    rw [mem_map_iff]
    constructor
    · rintro ⟨τ, hτ, rfl⟩
      obtain ⟨ρ, hρP, rfl⟩ := mem_map_iff.mp hτ
      simpa [Finset.image_image] using hρP
    · intro hσ
      refine ⟨σ.image e, mem_map_iff.mpr ⟨σ, hσ, rfl⟩, ?_⟩
      simp [Finset.image_image]
  constructor
  · intro h
    have h' := h.map e.symm e.symm.injective
    rwa [map_symm K, map_symm L] at h'
  · exact fun h => h.map e e.injective

end CollapsesTo

namespace Collapsible

/-- An injective relabeling preserves collapsibility, with the image of a terminal vertex as the
terminal vertex of the image collapse. -/
theorem map (h : Collapsible K) (f : α → β) (hf : Function.Injective f) :
    Collapsible (K.map f) := by
  obtain ⟨v, hv⟩ := collapsible_iff.mp h
  exact collapsible_iff.mpr ⟨f v, by simpa using hv.map f hf⟩

/-- Relabeling a complex by a vertex equivalence preserves and reflects collapsibility. -/
theorem map_equiv_iff (e : α ≃ β) : Collapsible (K.map e) ↔ Collapsible K := by
  classical
  constructor
  · intro h
    obtain ⟨w, hw⟩ := collapsible_iff.mp h
    refine collapsible_iff.mpr ⟨e.symm w, (CollapsesTo.map_equiv_iff e).mp ?_⟩
    simpa using hw
  · exact fun h => h.map e e.injective

end Collapsible

end PreAbstractSimplicialComplex

end TauCeti

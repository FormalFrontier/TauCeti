/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Collapse.Basic

/-!
# Relabeling simplicial collapses

Simplicial collapse is intrinsic to a complex and must not depend on its ambient vertex names.
This file proves that an injective relabeling preserves and reflects free pairs, elementary
collapses, finite collapse sequences, and collapsibility.

This is functorial infrastructure for the collapse track in layer 11 of the geometric-topology
roadmap. It lets later subdivision and product constructions replace a complex by an isomorphic
copy before forming collapse sequences. The definitions of free pairs and collapse follow
Rourke--Sanderson, *Introduction to Piecewise-Linear Topology*, Chapter 3; the results here are
the standard invariance of those definitions under a change of vertex labels.

## Main results

* `PreAbstractSimplicialComplex.IsFreePair.map`: an injective vertex map preserves a free pair.
* `PreAbstractSimplicialComplex.IsFreePair.map_iff_of_injective`: an injective vertex map
  preserves and reflects a free pair.
* `PreAbstractSimplicialComplex.ElementaryCollapsesTo.map`: an injective vertex map preserves an
  elementary collapse.
* `PreAbstractSimplicialComplex.ElementaryCollapsesTo.map_iff_of_injective`: an injective vertex
  map preserves and reflects an elementary collapse.
* `PreAbstractSimplicialComplex.CollapsesTo.map`: an injective vertex map preserves a finite
  collapse sequence.
* `PreAbstractSimplicialComplex.CollapsesTo.map_iff_of_injective`: an injective vertex map
  preserves and reflects a collapse sequence.
* `PreAbstractSimplicialComplex.CollapsesTo.map_equiv_iff`: relabeling by a vertex equivalence
  preserves and reflects a collapse sequence.
* `PreAbstractSimplicialComplex.Collapsible.map_iff_of_injective`: an injective vertex map
  preserves and reflects collapsibility.
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

private theorem map_injective (f : α → β) (hf : Function.Injective f) :
    Function.Injective (fun K : _root_.PreAbstractSimplicialComplex α => K.map f) := by
  intro K L hKL
  refine SetLike.ext fun σ => ?_
  have mem_image (P : _root_.PreAbstractSimplicialComplex α) :
      σ.image f ∈ P.map f ↔ σ ∈ P := by
    constructor
    · rintro ⟨τ, hτ, hτσ⟩
      rwa [(Finset.image_inj hf).mp hτσ] at hτ
    · exact fun hσ => mem_map_iff.mpr ⟨σ, hσ, rfl⟩
  have hKL' : K.map f = L.map f := by simpa only using hKL
  calc
    σ ∈ K ↔ σ.image f ∈ K.map f := (mem_image K).symm
    _ ↔ σ.image f ∈ L.map f := by rw [hKL']
    _ ↔ σ ∈ L := mem_image L

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
@[simp]
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

/-- An injective relabeling preserves and reflects a free pair. -/
theorem map_iff_of_injective (f : α → β) (hf : Function.Injective f) :
    IsFreePair (K.map f) (σ.image f) (τ.image f) ↔ IsFreePair K σ τ := by
  constructor
  · intro h
    refine
      { lower_mem := ?_
        upper_mem := ?_
        lower_ssubset_upper := (Finset.image_ssubset_image hf).mp h.lower_ssubset_upper
        eq_lower_or_eq_upper := ?_ }
    · obtain ⟨ρ, hρ, hρσ⟩ := mem_map_iff.mp h.lower_mem
      simpa only [(Finset.image_inj hf).mp hρσ] using hρ
    · obtain ⟨ρ, hρ, hρτ⟩ := mem_map_iff.mp h.upper_mem
      simpa only [(Finset.image_inj hf).mp hρτ] using hρ
    · intro ω hω hσω
      have hω' : ω.image f ∈ K.map f := mem_map_iff.mpr ⟨ω, hω, rfl⟩
      have hσω' : σ.image f ⊆ ω.image f := Finset.image_subset_image hσω
      rcases h.eq_lower_or_eq_upper hω' hσω' with h | h
      · exact Or.inl ((Finset.image_inj hf).mp h)
      · exact Or.inr ((Finset.image_inj hf).mp h)
  · exact fun h => h.map f hf

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

private theorem exists_of_map_left {P : _root_.PreAbstractSimplicialComplex β}
    {f : α → β} (hf : Function.Injective f) (h : ElementaryCollapsesTo (K.map f) P) :
    ∃ L : _root_.PreAbstractSimplicialComplex α,
      P = L.map f ∧ ElementaryCollapsesTo K L := by
  obtain ⟨σ', τ', hfree, _, hmem⟩ := h.exists_pair
  have hP : P = deletion (K.map f) σ' := SetLike.ext fun ω =>
    (hmem ω).trans <|
      (mem_deletion_of_isFreePair (K.map f) hfree).symm.trans mem_deletion.symm
  subst P
  obtain ⟨σ, _, hσσ'⟩ := mem_map_iff.mp hfree.lower_mem
  obtain ⟨τ, _, hττ'⟩ := mem_map_iff.mp hfree.upper_mem
  subst σ'
  subst τ'
  have hfree' : IsFreePair K σ τ :=
    (IsFreePair.map_iff_of_injective f hf).mp hfree
  exact ⟨deletion K σ, (map_deletion f hf K σ).symm, of_isFreePair hfree' rfl⟩

/-- An injective relabeling preserves and reflects an elementary collapse. -/
theorem map_iff_of_injective (f : α → β) (hf : Function.Injective f) :
    ElementaryCollapsesTo (K.map f) (L.map f) ↔ ElementaryCollapsesTo K L := by
  constructor
  · intro h
    obtain ⟨P, hLP, hKP⟩ := exists_of_map_left hf h
    have hLP' : L = P := map_injective f hf hLP
    simpa only [hLP'] using hKP
  · exact fun h => h.map f hf

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

/-- An injective relabeling preserves and reflects finite collapse sequences. -/
theorem map_iff_of_injective (f : α → β) (hf : Function.Injective f) :
    CollapsesTo (K.map f) (L.map f) ↔ CollapsesTo K L := by
  constructor
  · intro h
    obtain ⟨q, hLQ, hKQ⟩ := property_of_elementaryCollapsesTo
      (p := fun P => ∃ q : _root_.PreAbstractSimplicialComplex α,
        P = q.map f ∧ CollapsesTo K q)
      (fun ⦃A B⦄ hAB hA => by
        obtain ⟨q, hAQ, hKQ⟩ := hA
        have hAB' : ElementaryCollapsesTo (q.map f) _ := hAQ ▸ hAB
        obtain ⟨r, hBR, hQR⟩ := ElementaryCollapsesTo.exists_of_map_left hf hAB'
        exact ⟨r, hBR, hKQ.tail hQR⟩)
      h
      ⟨K, rfl, refl K⟩
    have hLQ' : L = q := map_injective f hf hLQ
    rwa [← hLQ'] at hKQ
  · exact fun h => h.map f hf

/-- Relabeling both complexes by a vertex equivalence preserves and reflects the existence of a
finite collapse sequence. -/
@[simp]
theorem map_equiv_iff (e : α ≃ β) :
    CollapsesTo (K.map e) (L.map e) ↔ CollapsesTo K L :=
  map_iff_of_injective e e.injective

end CollapsesTo

namespace Collapsible

/-- An injective relabeling preserves collapsibility, with the image of a terminal vertex as the
terminal vertex of the image collapse. -/
theorem map (h : Collapsible K) (f : α → β) (hf : Function.Injective f) :
    Collapsible (K.map f) := by
  obtain ⟨v, hv⟩ := collapsible_iff.mp h
  exact collapsible_iff.mpr ⟨f v, by simpa using hv.map f hf⟩

/-- An injective relabeling preserves and reflects collapsibility. -/
theorem map_iff_of_injective (f : α → β) (hf : Function.Injective f) :
    Collapsible (K.map f) ↔ Collapsible K := by
  constructor
  · intro h
    obtain ⟨w, hw⟩ := collapsible_iff.mp h
    have hwK : ({w} : Finset β) ∈ K.map f := point_le_iff.mp hw.le
    obtain ⟨σ, hσ, hσw⟩ := mem_map_iff.mp hwK
    obtain ⟨v, hv⟩ := (K.isRelLowerSet_faces hσ).1
    have hvw : f v = w := by
      have : f v ∈ σ.image f := Finset.mem_image.mpr ⟨v, hv, rfl⟩
      rw [hσw, Finset.mem_singleton] at this
      exact this
    refine collapsible_iff.mpr ⟨v, (CollapsesTo.map_iff_of_injective f hf).mp ?_⟩
    simpa [hvw] using hw
  · exact fun h => h.map f hf

/-- Relabeling a complex by a vertex equivalence preserves and reflects collapsibility. -/
@[simp]
theorem map_equiv_iff (e : α ≃ β) : Collapsible (K.map e) ↔ Collapsible K :=
  map_iff_of_injective e e.injective

end Collapsible

end PreAbstractSimplicialComplex

end TauCeti

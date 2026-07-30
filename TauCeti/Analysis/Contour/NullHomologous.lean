/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.Winding.Number.Basic

/-!
# Basic API for null-homologous contours

The contour-integration roadmap uses `Contour.IsNullHomologous γ a b Ω` as the hypothesis that a
curve has zero generalized winding number about every point outside the domain `Ω`. This file
records the elementary set-theoretic API for that predicate: monotonicity in the ambient domain,
the universal and empty-domain boundary cases, intersections, unions, and replacement by another
curve with the same winding numbers off the domain.

These lemmas are prerequisites for the homology Cauchy theorem and for the Hungerbühler--Wasem
generalized residue theorem, where the same cycle is repeatedly viewed inside larger or smaller
domains and the proof only needs the vanishing of the winding number on the complement.

## Main results

* `Contour.IsNullHomologous.mono` — enlarge the ambient domain.
* `Contour.IsNullHomologous.inter`, `Contour.isNullHomologous_iInter` — combine null-homology
  hypotheses by intersecting domains.
* `Contour.IsNullHomologous.union_left`, `Contour.IsNullHomologous.union_right` — a null-homologous
  curve remains null-homologous after adjoining an extra part of the domain.
* `Contour.isNullHomologous_const`, `Contour.isNullHomologous_empty_iff`,
  `Contour.isNullHomologous_univ` — constant curves and the two boundary cases.
* `Contour.IsNullHomologous.refl`, `Contour.IsNullHomologous.of_eq` — a zero-length parameter
  interval is null-homologous in every ambient set.
* `Contour.IsNullHomologous.congr_windingNumber` — replace a curve by another with the same winding
  numbers outside the domain.

## Provenance

This is routine API around the Hungerbühler--Wasem null-homology condition from the contour
integration roadmap; no formal source is vendored.
-/

public section

noncomputable section

namespace TauCeti.Contour

open Set

variable {γ η : ℝ → ℂ} {a b c d : ℝ} {Ω Ω' : Set ℂ}

/-- A curve is null-homologous in the whole plane, since there are no exterior points. -/
@[simp]
theorem isNullHomologous_univ (γ : ℝ → ℂ) (a b : ℝ) :
    IsNullHomologous γ a b (Set.univ : Set ℂ) := by
  rw [isNullHomologous_iff]
  intro w hw
  simp at hw

/-- A constant curve is null-homologous in every ambient set and on every parameter interval. -/
@[simp]
theorem isNullHomologous_const (x : ℂ) (a b : ℝ) (Ω : Set ℂ) :
    IsNullHomologous (fun _ : ℝ => x) a b Ω := by
  rw [isNullHomologous_iff]
  intro w _hw
  exact windingNumber_const x a b w

/-- Null-homology in the empty set is exactly vanishing of the winding number about every point. -/
@[simp]
theorem isNullHomologous_empty_iff :
    IsNullHomologous γ a b (∅ : Set ℂ) ↔ ∀ w, windingNumber γ a b w = 0 := by
  rw [isNullHomologous_iff]
  simp

/-- Every zero-length parameter interval is null-homologous in every ambient set. -/
theorem IsNullHomologous.refl (γ : ℝ → ℂ) (a : ℝ) (Ω : Set ℂ) :
    IsNullHomologous γ a a Ω := by
  rw [isNullHomologous_iff]
  intro z _hz
  exact windingNumber_same γ a z

/-- If the two endpoints are equal, the parameter interval is null-homologous in every ambient
set. -/
theorem IsNullHomologous.of_eq (γ : ℝ → ℂ) {a b : ℝ} (hab : a = b) (Ω : Set ℂ) :
    IsNullHomologous γ a b Ω := by
  subst b
  exact IsNullHomologous.refl γ a Ω

/-- If every winding number vanishes, then the curve is null-homologous in the empty set. -/
theorem isNullHomologous_empty_of_forall_windingNumber_eq_zero
    (h : ∀ w, windingNumber γ a b w = 0) :
    IsNullHomologous γ a b (∅ : Set ℂ) :=
  isNullHomologous_empty_iff.2 h

/-- Null-homology is monotone in the ambient domain: enlarging the domain shrinks its complement. -/
theorem IsNullHomologous.mono (h : IsNullHomologous γ a b Ω) (hΩ : Ω ⊆ Ω') :
    IsNullHomologous γ a b Ω' := by
  rw [isNullHomologous_iff] at h ⊢
  intro w hw
  exact h w (fun hwΩ => hw (hΩ hwΩ))

/-- A curve null-homologous in the empty set is null-homologous in every set. -/
theorem IsNullHomologous.of_empty (h : IsNullHomologous γ a b (∅ : Set ℂ)) :
    IsNullHomologous γ a b Ω :=
  h.mono (empty_subset Ω)

/-- A complement-subset form of `Contour.IsNullHomologous.mono`. -/
theorem IsNullHomologous.mono_compl (h : IsNullHomologous γ a b Ω) (hΩ : Ω'ᶜ ⊆ Ωᶜ) :
    IsNullHomologous γ a b Ω' :=
  h.mono (Set.compl_subset_compl.mp hΩ)

/-- It suffices to prove winding-number vanishing on any set containing the complement of `Ω`. -/
theorem isNullHomologous_of_compl_subset {E : Set ℂ} (hE : Ωᶜ ⊆ E)
    (h : ∀ w ∈ E, windingNumber γ a b w = 0) :
    IsNullHomologous γ a b Ω := by
  rw [isNullHomologous_iff]
  intro w hw
  exact h w (hE hw)

/-- If two curves have the same winding numbers outside `Ω`, null-homology transfers from one to
the other. This is the replacement principle used by homotopy or decomposition arguments before the
homology Cauchy theorem. -/
theorem IsNullHomologous.congr_windingNumber (h : IsNullHomologous γ a b Ω)
    (hwind : ∀ w ∉ Ω, windingNumber η c d w = windingNumber γ a b w) :
    IsNullHomologous η c d Ω := by
  rw [isNullHomologous_iff] at h ⊢
  intro w hw
  rw [hwind w hw]
  exact h w hw

/-- If a curve is null-homologous in `Ω`, then it is null-homologous in `Ω ∪ Ω'`. -/
theorem IsNullHomologous.union_left (h : IsNullHomologous γ a b Ω) :
    IsNullHomologous γ a b (Ω ∪ Ω') :=
  h.mono (subset_union_left)

/-- If a curve is null-homologous in `Ω'`, then it is null-homologous in `Ω ∪ Ω'`. -/
theorem IsNullHomologous.union_right (h : IsNullHomologous γ a b Ω') :
    IsNullHomologous γ a b (Ω ∪ Ω') :=
  h.mono (subset_union_right)

/-- If a curve is null-homologous in each of two domains, it is null-homologous in their
intersection. -/
theorem IsNullHomologous.inter (hΩ : IsNullHomologous γ a b Ω)
    (hΩ' : IsNullHomologous γ a b Ω') :
    IsNullHomologous γ a b (Ω ∩ Ω') := by
  rw [isNullHomologous_iff] at hΩ hΩ' ⊢
  intro w hw
  by_cases hwΩ : w ∈ Ω
  · exact hΩ' w (fun hwΩ' => hw ⟨hwΩ, hwΩ'⟩)
  · exact hΩ w hwΩ

/-- If a curve is null-homologous in every member of an indexed family, then it is
null-homologous in the intersection of the family. -/
theorem isNullHomologous_iInter {ι : Sort*} {Ω : ι → Set ℂ}
    (h : ∀ i, IsNullHomologous γ a b (Ω i)) :
    IsNullHomologous γ a b (⋂ i, Ω i) := by
  classical
  rw [isNullHomologous_iff]
  intro w hw
  rw [mem_iInter] at hw
  push Not at hw
  obtain ⟨i, hi⟩ := hw
  exact (isNullHomologous_iff.mp (h i)) w hi

end TauCeti.Contour

end

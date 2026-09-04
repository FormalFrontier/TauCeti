/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.Basic
public import TauCeti.Analysis.Complex.Conformal.Removability.Circle
import TauCeti.Analysis.Complex.Conformal.Inverse.Function

/-!
# Painlevé removability across an analytic arc

An analytic arc is locally straightened by a biholomorphic coordinate chart. This file proves
that every subset of the real locus of such a chart is removable for continuous holomorphic
functions: if `F` is continuous on an open part of the chart source and holomorphic away from the
subset, then `F` is holomorphic throughout that open set.

The proof reads `F` in the chart coordinate as `F ∘ e.symm`. The inverse chart is holomorphic on
the image of the domain by `DifferentiableOn.invFunOn`, and the removable set becomes a subset of
the real axis. Painlevé removability of the real axis then applies, after which the result is
transported back through `e`.

This is the analytic-arc case requested by layer L4 of the conformal-mapping roadmap. It follows
the standard coordinate reduction of removability across an analytic arc to the real axis; see
Ahlfors, *Complex Analysis*, Chapter 6, §1.4, and Rudin, *Real and Complex Analysis*, Chapter 11,
Exercise 11.

## Main results

* `TauCeti.differentiableOn_of_continuousOn_of_differentiableOn_diff_of_subset_coord_im_eq_zero`:
  every subset of the charted real locus is removable.
* `TauCeti.differentiableOn_of_continuousOn_of_differentiableOn_diff_coord_im_eq_zero`:
  removability of the full charted real locus.
* The corresponding gluing theorem for the two sides of the arc.
-/

public section

namespace TauCeti

open Complex Set

variable {F : ℂ → ℂ}

/-- **Painlevé removability across a charted analytic arc.** Let `e` be an open partial
homeomorphism of `ℂ` that is holomorphic on an open subset `Ω` of its source, and let `S` meet `Ω`
only where the chart coordinate is real. A function continuous on `Ω` and holomorphic there away
from `S` is holomorphic throughout `Ω`.

The hypothesis on `S` only constrains its intersection with `Ω`, since points outside the domain
under consideration do not affect the conclusion. -/
theorem
    differentiableOn_of_continuousOn_of_differentiableOn_diff_of_subset_coord_im_eq_zero
    (e : OpenPartialHomeomorph ℂ ℂ) {Ω S : Set ℂ} (he : DifferentiableOn ℂ e Ω)
    (hΩ : IsOpen Ω) (hΩe : Ω ⊆ e.source)
    (hcont : ContinuousOn F Ω) (hdiff : DifferentiableOn ℂ F (Ω \ S))
    (hS : Ω ∩ S ⊆ {z : ℂ | (e z).im = 0}) :
    DifferentiableOn ℂ F Ω := by
  have himage_target : e '' Ω ⊆ e.target := by
    rw [← e.image_source_eq_target]
    exact image_mono hΩe
  have hsymm_maps : MapsTo e.symm (e '' Ω) Ω := by
    rintro _ ⟨z, hz, rfl⟩
    simpa only [e.left_inv (hΩe hz)] using hz
  have he_invFunOn :=
    TauCeti.DifferentiableOn.invFunOn he hΩ (e.injOn.mono hΩe)
  have he_inv : DifferentiableOn ℂ e.symm (e '' Ω) :=
    he_invFunOn.congr fun _ hw => by
      rcases hw with ⟨z, hz, rfl⟩
      calc
        e.symm (e z) = z := e.left_inv (hΩe hz)
        _ = Function.invFunOn e Ω (e z) :=
          ((e.injOn.mono hΩe).leftInvOn_invFunOn hz).symm
  have hpull_cont : ContinuousOn (F ∘ e.symm) (e '' Ω) :=
    hcont.comp (e.continuousOn_symm.mono himage_target) hsymm_maps
  have hpull_diff : DifferentiableOn ℂ (F ∘ e.symm)
      ((e '' Ω) ∩ {w : ℂ | w.im ≠ 0}) := by
    refine hdiff.comp (he_inv.mono inter_subset_left) fun w hw =>
      ⟨hsymm_maps hw.1, ?_⟩
    intro hmem
    have him_zero := hS ⟨hsymm_maps hw.1, hmem⟩
    exact hw.2
      (by simpa only [Set.mem_ofPred_eq, e.right_inv (himage_target hw.1)] using him_zero)
  have hpull : DifferentiableOn ℂ (F ∘ e.symm) (e '' Ω) :=
    differentiableOn_of_continuousOn_of_differentiableOn_im_ne_zero
      (e.isOpen_image_of_subset_source hΩ hΩe) hpull_cont hpull_diff
  exact (hpull.comp he (mapsTo_image e Ω)).congr fun z hz => by
    simp only [Function.comp_apply, e.left_inv (hΩe hz)]

/-- **Painlevé removability of the full real locus of a holomorphic chart.** If a function is
continuous on an open part of the chart source and holomorphic wherever the chart coordinate has
nonzero imaginary part, then it is holomorphic throughout that open set. -/
theorem differentiableOn_of_continuousOn_of_differentiableOn_diff_coord_im_eq_zero
    (e : OpenPartialHomeomorph ℂ ℂ) {Ω : Set ℂ} (he : DifferentiableOn ℂ e Ω)
    (hΩ : IsOpen Ω) (hΩe : Ω ⊆ e.source) (hcont : ContinuousOn F Ω)
    (hdiff : DifferentiableOn ℂ F (Ω \ {z : ℂ | (e z).im = 0})) :
    DifferentiableOn ℂ F Ω :=
  differentiableOn_of_continuousOn_of_differentiableOn_diff_of_subset_coord_im_eq_zero
    e he hΩ hΩe hcont hdiff (fun _ hz => hz.2)

/-- **Gluing across a charted analytic arc.** A continuous function on an open part of the source
of a holomorphic chart that is holomorphic on both open sides of the charted real locus is
holomorphic throughout that open set. -/
theorem
  differentiableOn_of_continuousOn_of_differentiableOn_coord_im_pos_of_differentiableOn_coord_im_neg
    (e : OpenPartialHomeomorph ℂ ℂ) {Ω : Set ℂ} (he : DifferentiableOn ℂ e Ω)
    (hΩ : IsOpen Ω) (hΩe : Ω ⊆ e.source) (hcont : ContinuousOn F Ω)
    (hpos : DifferentiableOn ℂ F (Ω ∩ {z : ℂ | 0 < (e z).im}))
    (hneg : DifferentiableOn ℂ F (Ω ∩ {z : ℂ | (e z).im < 0})) :
    DifferentiableOn ℂ F Ω := by
  apply differentiableOn_of_continuousOn_of_differentiableOn_diff_coord_im_eq_zero
    e he hΩ hΩe hcont
  have hoffArc :
      Ω \ {z : ℂ | (e z).im = 0} =
        (Ω ∩ {z : ℂ | 0 < (e z).im}) ∪
          (Ω ∩ {z : ℂ | (e z).im < 0}) := by
    ext z
    simp only [mem_sdiff, mem_ofPred_eq, mem_union, mem_inter_iff]
    constructor
    · rintro ⟨hz, him⟩
      rcases lt_or_gt_of_ne him with h | h
      · exact Or.inr ⟨hz, h⟩
      · exact Or.inl ⟨hz, h⟩
    · rintro (⟨hz, h⟩ | ⟨hz, h⟩)
      · exact ⟨hz, ne_of_gt h⟩
      · exact ⟨hz, ne_of_lt h⟩
  rw [hoffArc]
  exact hpos.union_of_isOpen hneg
    (he.continuousOn.isOpen_inter_preimage hΩ
      (isOpen_lt continuous_const Complex.continuous_im))
    (he.continuousOn.isOpen_inter_preimage hΩ
      (isOpen_lt Complex.continuous_im continuous_const))

end TauCeti

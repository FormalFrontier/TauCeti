/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Modular
public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Basic
public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.SingularSets
public import TauCeti.NumberTheory.ModularForms.Order.OfVanishing

import Mathlib.NumberTheory.ModularForms.QExpansion
import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Containment

/-!
# On-curve capture of the boundary zeros

Every zero of a nonzero level-one modular form on the boundary contour lands in one of the
two singular sets: arc points (including the corners) in the arc singular set, vertical
points in the vertical singular set — the left vertical through the translation onto the
right one — and ceiling points do not occur at all once the height exceeds a bound on the
capturing set. The capturing hypothesis is completeness: every fundamental-domain point of
nonzero vanishing order belongs to `S`. The contour lies in the truncated fundamental
domain, so each on-curve zero yields a fundamental-domain point of `S`, and the segment
geometry decides which singular set receives it.

## Main declarations

* `TauCeti.ModularForm.fdBoundary_mem_verticalSingularSet_of_mem_Ioo_zero_one` and
  `…_of_mem_Ioo_three_four` (the vertical captures).
* `TauCeti.ModularForm.fdBoundary_mem_arcSingularSet_of_mem_Icc_one_three` (the arc capture).
* `TauCeti.ModularForm.comp_ofComplex_fdBoundary_ne_zero_of_forall_im_lt` (no ceiling zeros).
* `TauCeti.ModularForm.fdBoundary_mem_arcSingularSet_union_verticalSingularSet_of_comp_eq_zero`
  (the full capture).

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development (`ForMathlib/ValenceFormula/PVChain/OnCurveCapture.lean`) this file ports onto
  the current Mathlib pin.
-/

public section

open Complex Set UpperHalfPlane TauCeti.UpperHalfPlane

open scoped ModularForm MatrixGroups Modular

namespace TauCeti

namespace ModularForm

variable {k : ℤ} {F : Type*} [FunLike F ℍ ℂ] {f : F} {S : Finset ℍ} {H t : ℝ}

/-- A fundamental-domain point at which the form's realization vanishes lies in every
complete capturing set. -/
private lemma mem_of_mem_fd_of_comp_eq_zero [ModularFormClass F 𝒮ℒ k]
    (hf : (⇑f : ℍ → ℂ) ≠ 0)
    (hS : ∀ p, p ∈ 𝒟 → orderOfVanishingAt (⇑f) p ≠ 0 → p ∈ S)
    {q : ℍ} (hq : q ∈ 𝒟) (h0 : (⇑f ∘ ofComplex) (q : ℂ) = 0) : q ∈ S := by
  refine hS q hq (orderOfVanishingAt_ne_zero_of_eq_zero (ModularFormClass.holo f) hf ?_)
  simpa [Function.comp_apply, ofComplex_apply] using h0

/-- A zero on the open right vertical is captured by the vertical singular set. -/
theorem fdBoundary_mem_verticalSingularSet_of_mem_Ioo_zero_one [ModularFormClass F 𝒮ℒ k]
    (hf : (⇑f : ℍ → ℂ) ≠ 0)
    (hS : ∀ p, p ∈ 𝒟 → orderOfVanishingAt (⇑f) p ≠ 0 → p ∈ S)
    (hH : 1 ≤ H) (ht : t ∈ Ioo (0 : ℝ) 1)
    (h0 : (⇑f ∘ ofComplex) (fdBoundary H t) = 0) :
    fdBoundary H t ∈ (verticalSingularSet S : Set ℂ) := by
  have ht05 : t ∈ Icc (0 : ℝ) 5 := ⟨ht.1.le, by linarith [ht.2]⟩
  obtain ⟨q, hq, hqe⟩ := fdBoundary_mem_coe_truncatedFundamentalDomain hH ht05
  have hre : (fdBoundary H t).re = 1 / 2 := re_fdBoundarySegment1 H ⟨ht.1.le, ht.2.le⟩
  have hs32 : Real.sqrt 3 / 2 < 1 := sqrt_three_div_two_lt_one
  have him_gt : Real.sqrt 3 / 2 < (fdBoundary H t).im := by
    rw [im_fdBoundary_of_le_one ht.2.le]
    nlinarith [ht.1, ht.2]
  have hnorm : 1 < ‖fdBoundary H t‖ := by
    refine Complex.one_lt_normSq_iff.mp ?_
    rw [Complex.normSq_apply, hre]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
  have hq_S : q ∈ S := mem_of_mem_fd_of_comp_eq_zero hf hS hq.1 (by rwa [hqe])
  rw [Finset.mem_coe, mem_verticalSingularSet]
  exact Or.inl ⟨q, hq_S, ⟨by rw [hqe]; exact hre, by rw [hqe]; exact hnorm⟩, hqe⟩

/-- A zero on the arc, corners included, is captured by the arc singular set. -/
theorem fdBoundary_mem_arcSingularSet_of_mem_Icc_one_three [ModularFormClass F 𝒮ℒ k]
    (hf : (⇑f : ℍ → ℂ) ≠ 0)
    (hS : ∀ p, p ∈ 𝒟 → orderOfVanishingAt (⇑f) p ≠ 0 → p ∈ S)
    (hH : 1 ≤ H) (ht : t ∈ Icc (1 : ℝ) 3)
    (h0 : (⇑f ∘ ofComplex) (fdBoundary H t) = 0) :
    fdBoundary H t ∈ (arcSingularSet S : Set ℂ) := by
  have ht05 : t ∈ Icc (0 : ℝ) 5 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  obtain ⟨q, hq, hqe⟩ := fdBoundary_mem_coe_truncatedFundamentalDomain hH ht05
  have hnorm : ‖fdBoundary H t‖ = 1 := norm_fdBoundary_arc ht.1 ht.2
  have hq_S : q ∈ S := mem_of_mem_fd_of_comp_eq_zero hf hS hq.1 (by rwa [hqe])
  rw [Finset.mem_coe, mem_arcSingularSet]
  exact Or.inl ⟨q, hq_S, by rw [hqe]; exact hnorm, hqe⟩

/-- The form does not vanish on the contour's ceiling row once the height dominates the
capturing set. -/
theorem comp_ofComplex_fdBoundary_ne_zero_of_forall_im_lt [ModularFormClass F 𝒮ℒ k]
    (hf : (⇑f : ℍ → ℂ) ≠ 0)
    (hS : ∀ p, p ∈ 𝒟 → orderOfVanishingAt (⇑f) p ≠ 0 → p ∈ S)
    (hH : 1 ≤ H) (hbound : ∀ p ∈ S, (p : ℂ).im < H) (ht : t ∈ Icc (0 : ℝ) 5)
    (him : (fdBoundary H t).im = H) : (⇑f ∘ ofComplex) (fdBoundary H t) ≠ 0 := by
  intro h0
  obtain ⟨q, hq, hqe⟩ := fdBoundary_mem_coe_truncatedFundamentalDomain hH ht
  have hq_S : q ∈ S := mem_of_mem_fd_of_comp_eq_zero hf hS hq.1 (by rwa [hqe])
  have := hbound q hq_S
  rw [hqe, him] at this
  exact lt_irrefl H this

/-- A zero on the open left vertical is captured by the vertical singular set, through the
translation onto the right vertical. -/
theorem fdBoundary_mem_verticalSingularSet_of_mem_Ioo_three_four [ModularFormClass F 𝒮ℒ k]
    (hf : (⇑f : ℍ → ℂ) ≠ 0)
    (hS : ∀ p, p ∈ 𝒟 → orderOfVanishingAt (⇑f) p ≠ 0 → p ∈ S)
    (hH : 1 ≤ H) (ht : t ∈ Ioo (3 : ℝ) 4)
    (h0 : (⇑f ∘ ofComplex) (fdBoundary H t) = 0) :
    fdBoundary H t ∈ (verticalSingularSet S : Set ℂ) := by
  set s : ℝ := 4 - t with hs
  have hs_mem : s ∈ Ioo (0 : ℝ) 1 := ⟨by rw [hs]; linarith [ht.2], by rw [hs]; linarith [ht.1]⟩
  have hshift : fdBoundary H t = fdBoundary H s - 1 := by
    have h4 := fdBoundary_four_sub_vertical H ⟨hs_mem.1.le, hs_mem.2.le⟩
    have hts : (4 : ℝ) - s = t := by
      rw [hs]
      ring
    rw [hts] at h4
    exact h4
  have hper : Function.Periodic (⇑f ∘ ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex f (by simp)
  have h0s : (⇑f ∘ ofComplex) (fdBoundary H s) = 0 := by
    have hp := hper (fdBoundary H t)
    rw [hshift, sub_add_cancel] at hp
    rw [hp]
    rwa [hshift] at h0
  have hmem_s := fdBoundary_mem_verticalSingularSet_of_mem_Ioo_zero_one hf hS hH hs_mem h0s
  have hre_s : (fdBoundary H s).re = 1 / 2 :=
    re_fdBoundarySegment1 H ⟨hs_mem.1.le, hs_mem.2.le⟩
  rw [hshift]
  exact sub_one_mem_verticalSingularSet hmem_s hre_s

/-- **Full on-curve capture**: every zero of the form on the boundary contour lies in one
of the two singular sets, once the height dominates the capturing set. -/
theorem fdBoundary_mem_arcSingularSet_union_verticalSingularSet_of_comp_eq_zero
    [ModularFormClass F 𝒮ℒ k]
    (hf : (⇑f : ℍ → ℂ) ≠ 0)
    (hS : ∀ p, p ∈ 𝒟 → orderOfVanishingAt (⇑f) p ≠ 0 → p ∈ S)
    (hH : 1 ≤ H) (hbound : ∀ p ∈ S, (p : ℂ).im < H) (ht : t ∈ Icc (0 : ℝ) 5)
    (h0 : (⇑f ∘ ofComplex) (fdBoundary H t) = 0) :
    fdBoundary H t ∈ (arcSingularSet S ∪ verticalSingularSet S : Finset ℂ) := by
  rw [Finset.mem_union]
  rcases eq_or_lt_of_le ht.1 with h0t | h0t
  · exfalso
    refine comp_ofComplex_fdBoundary_ne_zero_of_forall_im_lt hf hS hH hbound ht ?_ h0
    rw [← h0t, fdBoundary_of_le_one (by norm_num), fdBoundarySegment1_apply_zero]
    simp
  rcases lt_or_ge t 1 with h1 | h1
  · exact Or.inr (fdBoundary_mem_verticalSingularSet_of_mem_Ioo_zero_one hf hS hH
      ⟨h0t, h1⟩ h0)
  rcases le_or_gt t 3 with h3 | h3
  · exact Or.inl (fdBoundary_mem_arcSingularSet_of_mem_Icc_one_three hf hS hH ⟨h1, h3⟩ h0)
  rcases lt_or_ge t 4 with h4 | h4
  · exact Or.inr (fdBoundary_mem_verticalSingularSet_of_mem_Ioo_three_four hf hS hH
      ⟨h3, h4⟩ h0)
  · exfalso
    refine comp_ofComplex_fdBoundary_ne_zero_of_forall_im_lt hf hS hH hbound ht ?_ h0
    exact im_fdBoundarySegment5 H ⟨h4, ht.2⟩

end ModularForm

end TauCeti

end

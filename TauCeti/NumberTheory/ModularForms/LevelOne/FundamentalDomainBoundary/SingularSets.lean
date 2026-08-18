/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Data.Finset.Lattice.Fold

import Mathlib.Analysis.Real.Sqrt
import TauCeti.Analysis.Complex.UpperHalfPlane.Rho

/-!
# The singular sets on the boundary contour

The two candidate exceptional sets the on-curve principal values excise, built from any
finite set of upper half-plane points and closed under the identifications the contour
pairings use: the arc singular set —
the unit-norm points of a finite set `S ⊆ ℍ` together with their images under the inversion
`z ↦ -1/z` and the corners `ρ`, `ρ + 1` — and the vertical singular set — the `re = ±1/2`,
norm-above-one points of `S` together with their translates onto the opposite vertical
line. Their calculus: the corners belong to the arc set, the arc set consists of unit-norm
points and is inversion-closed, the vertical set lies on the two vertical lines and is
translation-paired, all points have positive imaginary part, and a single height bound
dominates every vertical point.

## Main declarations

* `TauCeti.ModularForm.arcSingularSet` and `TauCeti.ModularForm.verticalSingularSet`.
* `TauCeti.ModularForm.neg_one_div_mem_arcSingularSet` (inversion closure).
* `TauCeti.ModularForm.sub_one_mem_verticalSingularSet` and
  `TauCeti.ModularForm.add_one_mem_verticalSingularSet` (translation pairing).
* `TauCeti.ModularForm.neg_conj_mem_arcSingularSet_union_verticalSingularSet` (closure of the
  union under the vertical reflection `z ↦ -conj z`, through the two closures above).
* `TauCeti.ModularForm.exists_height_bound` (a height above `√3/2` and `1` dominating `S`).

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development (`ForMathlib/ValenceFormula/PVChain/Helpers.lean`) this file ports onto the
  current Mathlib pin; the reflection and union closure lemmas adapt the per-part closure
  bookkeeping of `ForMathlib/ValenceFormula/PVChain/Assembly.lean`.
-/

public section

open Complex Set UpperHalfPlane

namespace TauCeti

namespace ModularForm

/-- The arc singular set of a finite `S ⊆ ℍ`: its unit-norm members, their images under the
inversion `z ↦ -1/z`, and the corners `ρ` and `ρ + 1`. -/
noncomputable def arcSingularSet (S : Finset ℍ) : Finset ℂ :=
  (S.filter fun p : ℍ ↦ ‖(p : ℂ)‖ = 1).image ((↑·) : ℍ → ℂ) ∪
    (S.filter fun p : ℍ ↦ ‖(p : ℂ)‖ = 1).image (fun p : ℍ ↦ -1 / (p : ℂ)) ∪
    {(ρ : ℂ), (ρ : ℂ) + 1}

/-- The vertical singular set of a finite `S ⊆ ℍ`: its `re = ±1/2`, norm-above-one members
together with their translates onto the opposite vertical line. -/
noncomputable def verticalSingularSet (S : Finset ℍ) : Finset ℂ :=
  (S.filter fun p : ℍ ↦ (p : ℂ).re = 1 / 2 ∧ 1 < ‖(p : ℂ)‖).image ((↑·) : ℍ → ℂ) ∪
    (S.filter fun p : ℍ ↦ (p : ℂ).re = 1 / 2 ∧ 1 < ‖(p : ℂ)‖).image
      (fun p : ℍ ↦ (p : ℂ) - 1) ∪
    (S.filter fun p : ℍ ↦ (p : ℂ).re = -(1 / 2) ∧ 1 < ‖(p : ℂ)‖).image ((↑·) : ℍ → ℂ) ∪
    (S.filter fun p : ℍ ↦ (p : ℂ).re = -(1 / 2) ∧ 1 < ‖(p : ℂ)‖).image
      (fun p : ℍ ↦ (p : ℂ) + 1)

/-- Membership in the arc singular set, by branch: an original unit-norm point, an inversion
image, or one of the two corners. -/
@[simp]
theorem mem_arcSingularSet {S : Finset ℍ} {s : ℂ} :
    s ∈ arcSingularSet S ↔
      (∃ p ∈ S, ‖(p : ℂ)‖ = 1 ∧ (p : ℂ) = s) ∨
        (∃ p ∈ S, ‖(p : ℂ)‖ = 1 ∧ -1 / (p : ℂ) = s) ∨ s = (ρ : ℂ) ∨ s = (ρ : ℂ) + 1 := by
  simp only [arcSingularSet, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_insert, Finset.mem_singleton, and_assoc, or_assoc]

/-- Membership in the vertical singular set, by branch: an original point on either line or a
translate onto the opposite line. -/
@[simp]
theorem mem_verticalSingularSet {S : Finset ℍ} {s : ℂ} :
    s ∈ verticalSingularSet S ↔
      (∃ p ∈ S, ((p : ℂ).re = 1 / 2 ∧ 1 < ‖(p : ℂ)‖) ∧ (p : ℂ) = s) ∨
        (∃ p ∈ S, ((p : ℂ).re = 1 / 2 ∧ 1 < ‖(p : ℂ)‖) ∧ (p : ℂ) - 1 = s) ∨
        (∃ p ∈ S, ((p : ℂ).re = -(1 / 2) ∧ 1 < ‖(p : ℂ)‖) ∧ (p : ℂ) = s) ∨
        (∃ p ∈ S, ((p : ℂ).re = -(1 / 2) ∧ 1 < ‖(p : ℂ)‖) ∧ (p : ℂ) + 1 = s) := by
  simp only [verticalSingularSet, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    and_assoc, or_assoc]

/-- Every point of the vertical singular set has norm above `1`: the translates keep the
square norm because they only flip the sign of the real part. -/
theorem one_lt_norm_of_mem_verticalSingularSet {S : Finset ℍ} {s : ℂ}
    (hs : s ∈ verticalSingularSet S) : 1 < ‖s‖ := by
  rw [mem_verticalSingularSet] at hs
  have key : ∀ (p : ℍ) (c : ℝ), (p : ℂ).re = c → ‖(p : ℂ)‖ ^ 2 = c ^ 2 + (p : ℂ).im ^ 2 := by
    intro p c hc
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hc]
    ring
  rcases hs with ⟨p, -, ⟨hre, hn⟩, rfl⟩ | ⟨p, -, ⟨hre, hn⟩, rfl⟩ |
    ⟨p, -, ⟨hre, hn⟩, rfl⟩ | ⟨p, -, ⟨hre, hn⟩, rfl⟩
  · exact hn
  · have h1 := key p _ hre
    have h2 : ‖(p : ℂ) - 1‖ ^ 2 = (-(1 / 2) : ℝ) ^ 2 + (p : ℂ).im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, sub_re, sub_im, one_re, one_im,
        hre]
      ring
    nlinarith [norm_nonneg ((p : ℂ) - 1)]
  · exact hn
  · have h1 := key p _ hre
    have h2 : ‖(p : ℂ) + 1‖ ^ 2 = ((1 / 2) : ℝ) ^ 2 + (p : ℂ).im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, add_re, add_im, one_re, one_im,
        hre]
      ring
    nlinarith [norm_nonneg ((p : ℂ) + 1)]

/-- The corner `ρ` belongs to the arc singular set. -/
theorem rho_mem_arcSingularSet (S : Finset ℍ) : (ρ : ℂ) ∈ arcSingularSet S := by
  simp [arcSingularSet]

/-- The corner `ρ + 1` belongs to the arc singular set. -/
theorem rho_add_one_mem_arcSingularSet (S : Finset ℍ) :
    (ρ : ℂ) + 1 ∈ arcSingularSet S := by
  simp [arcSingularSet]

/-- Every point of the arc singular set has norm `1`. -/
theorem norm_eq_one_of_mem_arcSingularSet {S : Finset ℍ} {s : ℂ}
    (hs : s ∈ arcSingularSet S) : ‖s‖ = 1 := by
  simp only [arcSingularSet, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with (⟨p, ⟨-, hp_norm⟩, rfl⟩ | ⟨p, ⟨-, hp_norm⟩, rfl⟩) | rfl | rfl
  · exact hp_norm
  · rw [norm_div, norm_neg, norm_one, hp_norm, div_one]
  · exact UpperHalfPlane.norm_ρ
  · exact UpperHalfPlane.norm_ρ_add_one

/-- The arc singular set is closed under the inversion `z ↦ -1/z`. -/
theorem neg_one_div_mem_arcSingularSet {S : Finset ℍ} {s : ℂ}
    (hs : s ∈ arcSingularSet S) : -1 / s ∈ arcSingularSet S := by
  simp only [arcSingularSet, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_insert, Finset.mem_singleton] at hs ⊢
  rcases hs with (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩) | rfl | rfl
  · exact Or.inl (Or.inr ⟨p, hp, rfl⟩)
  · refine Or.inl (Or.inl ⟨p, hp, ?_⟩)
    have hne : (p : ℂ) ≠ 0 := by
      intro h0
      rw [h0] at hp
      simpa using hp.2
    field_simp
  · exact Or.inr (Or.inr UpperHalfPlane.neg_one_div_ρ)
  · exact Or.inr (Or.inl UpperHalfPlane.neg_one_div_ρ_add_one)

/-- Every point of the vertical singular set lies on one of the two vertical lines. -/
theorem re_eq_of_mem_verticalSingularSet {S : Finset ℍ} {s : ℂ}
    (hs : s ∈ verticalSingularSet S) : s.re = 1 / 2 ∨ s.re = -(1 / 2) := by
  simp only [verticalSingularSet, Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hs
  rcases hs with ((⟨p, ⟨-, hp_re, -⟩, rfl⟩ | ⟨p, ⟨-, hp_re, -⟩, rfl⟩) |
    ⟨p, ⟨-, hp_re, -⟩, rfl⟩) | ⟨p, ⟨-, hp_re, -⟩, rfl⟩
  · exact Or.inl hp_re
  · right
    rw [sub_re, one_re, hp_re]
    norm_num
  · exact Or.inr hp_re
  · left
    rw [add_re, one_re, hp_re]
    norm_num

/-- A right-line point of the vertical singular set has its left translate in the set. -/
theorem sub_one_mem_verticalSingularSet {S : Finset ℍ} {s : ℂ}
    (hs : s ∈ verticalSingularSet S) (hre : s.re = 1 / 2) :
    s - 1 ∈ verticalSingularSet S := by
  simp only [verticalSingularSet, Finset.mem_union, Finset.mem_image,
    Finset.mem_filter] at hs ⊢
  rcases hs with ((⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩) | ⟨p, hp, rfl⟩) | ⟨p, hp, rfl⟩
  · exact Or.inl (Or.inl (Or.inr ⟨p, hp, rfl⟩))
  · rw [sub_re, one_re, hp.2.1] at hre
    norm_num at hre
  · rw [hp.2.1] at hre
    norm_num at hre
  · refine Or.inl (Or.inr ⟨p, hp, ?_⟩)
    ring

/-- A left-line point of the vertical singular set has its right translate in the set. -/
theorem add_one_mem_verticalSingularSet {S : Finset ℍ} {s : ℂ}
    (hs : s ∈ verticalSingularSet S) (hre : s.re = -(1 / 2)) :
    s + 1 ∈ verticalSingularSet S := by
  simp only [verticalSingularSet, Finset.mem_union, Finset.mem_image,
    Finset.mem_filter] at hs ⊢
  rcases hs with ((⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩) | ⟨p, hp, rfl⟩) | ⟨p, hp, rfl⟩
  · rw [hp.2.1] at hre
    norm_num at hre
  · refine Or.inl (Or.inl (Or.inl ⟨p, hp, ?_⟩))
    ring
  · exact Or.inr ⟨p, hp, rfl⟩
  · rw [add_re, one_re, hp.2.1] at hre
    norm_num at hre

/-- The arc singular set is closed under the reflection `z ↦ -conj z` that exchanges the two
verticals of the boundary contour: on unit-norm points the reflection coincides with the
inversion `z ↦ -1/z`, and the set is inversion-closed. -/
theorem neg_conj_mem_arcSingularSet {S : Finset ℍ} {s : ℂ}
    (hs : s ∈ arcSingularSet S) : -(starRingEnd ℂ) s ∈ arcSingularSet S := by
  rw [← Complex.inv_eq_conj (norm_eq_one_of_mem_arcSingularSet hs), ← one_div, ← neg_div]
  exact neg_one_div_mem_arcSingularSet hs

/-- The vertical singular set is closed under the reflection `z ↦ -conj z` that exchanges the
two verticals of the boundary contour: on the lines `re = ±1/2` the reflection coincides with
the translation onto the opposite line, and the set is translation-paired. -/
theorem neg_conj_mem_verticalSingularSet {S : Finset ℍ} {s : ℂ}
    (hs : s ∈ verticalSingularSet S) : -(starRingEnd ℂ) s ∈ verticalSingularSet S := by
  rcases re_eq_of_mem_verticalSingularSet hs with hre | hre
  · have h : -(starRingEnd ℂ) s = s - 1 := by norm_num [Complex.ext_iff, hre]
    exact h ▸ sub_one_mem_verticalSingularSet hs hre
  · have h : -(starRingEnd ℂ) s = s + 1 := by norm_num [Complex.ext_iff, hre]
    exact h ▸ add_one_mem_verticalSingularSet hs hre

/-- The union of the two singular sets is closed under the reflection `z ↦ -conj z` — the
reflection invariance the excised vertical cancellation
(`intervalIntegral_excised_fdBoundarySegment4_eq_neg_segment1`) asks of its excision set. -/
theorem neg_conj_mem_arcSingularSet_union_verticalSingularSet {S : Finset ℍ} {s : ℂ}
    (hs : s ∈ arcSingularSet S ∪ verticalSingularSet S) :
    -(starRingEnd ℂ) s ∈ arcSingularSet S ∪ verticalSingularSet S := by
  rcases Finset.mem_union.mp hs with h | h
  · exact Finset.mem_union_left _ (neg_conj_mem_arcSingularSet h)
  · exact Finset.mem_union_right _ (neg_conj_mem_verticalSingularSet h)

/-- Some height above `√3/2` and `1` dominates the imaginary parts of a finite `S ⊆ ℍ`. -/
theorem exists_height_bound (S : Finset ℍ) :
    ∃ H : ℝ, Real.sqrt 3 / 2 < H ∧ 1 < H ∧ ∀ p ∈ S, (p : ℂ).im < H := by
  have hsqrt3 : Real.sqrt 3 / 2 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
  rcases S.eq_empty_or_nonempty with rfl | h_ne
  · exact ⟨2, hsqrt3, by norm_num, by simp⟩
  refine ⟨max 2 (S.sup' h_ne (fun p : ℍ ↦ (p : ℂ).im) + 1),
    lt_of_lt_of_le hsqrt3 (le_max_left _ _),
    lt_of_lt_of_le (by norm_num) (le_max_left _ _), fun p hp ↦ ?_⟩
  calc (p : ℂ).im ≤ S.sup' h_ne (fun p : ℍ ↦ (p : ℂ).im) :=
        Finset.le_sup' (fun p : ℍ ↦ (p : ℂ).im) hp
    _ < S.sup' h_ne (fun p : ℍ ↦ (p : ℂ).im) + 1 := by linarith
    _ ≤ max 2 (S.sup' h_ne (fun p : ℍ ↦ (p : ℂ).im) + 1) := le_max_right _ _

/-- A height bound on `S` bounds the vertical singular set. -/
theorem im_lt_of_mem_verticalSingularSet {S : Finset ℍ} {s : ℂ} {H : ℝ}
    (hs : s ∈ verticalSingularSet S) (h_bound : ∀ p ∈ S, (p : ℂ).im < H) : s.im < H := by
  simp only [verticalSingularSet, Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hs
  rcases hs with ((⟨p, ⟨hp_mem, -⟩, rfl⟩ | ⟨p, ⟨hp_mem, -⟩, rfl⟩) |
    ⟨p, ⟨hp_mem, -⟩, rfl⟩) | ⟨p, ⟨hp_mem, -⟩, rfl⟩ <;>
    first | exact h_bound p hp_mem | simpa using h_bound p hp_mem

/-- Every point of the arc singular set lies in the open upper half-plane. -/
theorem im_pos_of_mem_arcSingularSet {S : Finset ℍ} {s : ℂ}
    (hs : s ∈ arcSingularSet S) : 0 < s.im := by
  simp only [arcSingularSet, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with (⟨p, ⟨-, hp_norm⟩, rfl⟩ | ⟨p, ⟨-, hp_norm⟩, rfl⟩) | rfl | rfl
  · exact p.2
  · simpa [neg_div] using p.im_inv_neg_coe_pos
  · simpa using (ρ : ℍ).2
  · rw [add_im, one_im, add_zero]
    simpa using (ρ : ℍ).2

/-- Every point of the vertical singular set lies in the open upper half-plane. -/
theorem im_pos_of_mem_verticalSingularSet {S : Finset ℍ} {s : ℂ}
    (hs : s ∈ verticalSingularSet S) : 0 < s.im := by
  simp only [verticalSingularSet, Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hs
  rcases hs with ((⟨p, -, rfl⟩ | ⟨p, -, rfl⟩) | ⟨p, -, rfl⟩) | ⟨p, -, rfl⟩ <;>
    simpa using p.2

/-- Every arc excision centre sits below the ceiling: it has unit norm, and the imaginary
part is bounded by the norm. -/
theorem im_lt_of_mem_arcSingularSet {S : Finset ℍ} {s : ℂ} {H : ℝ}
    (hs : s ∈ arcSingularSet S) (hH : 1 < H) : s.im < H := by
  have h1 : s.im ≤ ‖s‖ := Complex.im_le_norm s
  rw [norm_eq_one_of_mem_arcSingularSet hs] at h1
  linarith

/-- Every union excision centre sits below the ceiling: arc points by their unit norm,
vertical points by the height bound on their source set. -/
theorem im_lt_of_mem_arcSingularSet_union_verticalSingularSet {S : Finset ℍ} {s : ℂ} {H : ℝ}
    (hH : 1 < H) (hHgt : ∀ p ∈ S, (p : ℂ).im < H)
    (hs : s ∈ arcSingularSet S ∪ verticalSingularSet S) : s.im < H := by
  rcases Finset.mem_union.mp hs with h | h
  · exact im_lt_of_mem_arcSingularSet h hH
  · exact im_lt_of_mem_verticalSingularSet h hHgt

end ModularForm

end TauCeti

end

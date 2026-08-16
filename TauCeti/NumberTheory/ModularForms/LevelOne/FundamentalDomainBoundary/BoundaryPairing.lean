/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.Modular
public import TauCeti.Analysis.Complex.UpperHalfPlane.Rho
public import TauCeti.NumberTheory.ModularForms.Order.OfVanishing
import TauCeti.NumberTheory.Modular.Orbits

/-!
# Pairing the boundary divisor points of the fundamental domain

The boundary of the fundamental domain is identified with itself in pairs: `z ↦ z + 1`
carries the left vertical edge onto the right one, and `z ↦ -1/z` swaps the two halves of
the unit arc, fixing `i` and exchanging the two `ρ`-corners. A slash-invariant form has the
same vanishing order at paired points, so — over a divisor set that is *complete* for the
closed fundamental domain `𝒟` — each right-half order sum equals its left-half partner, and
the full non-elliptic boundary sum is twice the sum over left representatives.

These are the bookkeeping identities that turn the winding-weighted boundary count of the
valence formula (each non-elliptic boundary point carries weight `-1/2`) into a sum with one
full-weight representative per pair.

## Main results

* `TauCeti.ModularForm.sum_orderOfVanishingAt_rightVertical_eq_leftVertical`: the vertical pairing.
* `TauCeti.ModularForm.sum_orderOfVanishingAt_rightArc_eq_leftArc`: the arc pairing.
* `TauCeti.ModularForm.sum_orderOfVanishingAt_rightArc_ne_ρ_add_one_eq_leftArc_ne_ρ`: the arc
  pairing with the two `ρ`-corners removed.
* `sum_orderOfVanishingAt_nonEllipticBoundary_eq_verticals_add_arcs`
  (in `TauCeti.ModularForm`): the order sum over the non-elliptic boundary points splits into
  the four half-edge sums.
* `TauCeti.ModularForm.sum_orderOfVanishingAt_nonEllipticBoundary_eq_two_mul`: the non-elliptic
  boundary sum is twice the left-representative sum.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development (`ForMathlib/OrbitPairing.lean` and the partition lemmas of
  `ForMathlib/CoreIdentityProof.lean`), ported onto the current Mathlib pin.
-/

public section

open Complex Set UpperHalfPlane Function

open scoped ModularForm MatrixGroups Modular

namespace TauCeti

namespace ModularForm

variable {k : ℤ} {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup SL(2, ℤ)} {f : F}
  {S : Finset ℍ}

section Vertical

variable {g : ℍ → ℂ} {r : ℝ} {p : ℍ}

-- `re = -r / 2` is the perpendicular bisector of `0` and `-r`; for `r = ±1` it is an edge of `𝒟`.
private lemma normSq_coe_vadd_of_re_eq (hre : (p : ℂ).re = -r / 2) :
    normSq ((r +ᵥ p : ℍ) : ℂ) = normSq (p : ℂ) := by
  grind [coe_vadd, normSq_apply, add_re, add_im, ofReal_re, ofReal_im]

private lemma norm_coe_vadd_of_re_eq (hre : (p : ℂ).re = -r / 2) :
    ‖((r +ᵥ p : ℍ) : ℂ)‖ = ‖(p : ℂ)‖ := by
  rw [norm_def, norm_def, normSq_coe_vadd_of_re_eq hre]

/-- Translation by `r` carries a fundamental-domain point on the line `re = -r / 2` to one on
`re = r / 2`, keeping the modulus. -/
lemma vadd_mem_fd_of_re_eq (hr : |r| ≤ 1) (hp : p ∈ 𝒟) (hre : (p : ℂ).re = -r / 2) :
    r +ᵥ p ∈ 𝒟 := by
  refine ⟨normSq_coe_vadd_of_re_eq hre ▸ hp.1, abs_le.mpr ⟨?_, ?_⟩⟩ <;>
    rw [vadd_re, ← coe_re, hre] <;> linarith [abs_le.mp hr]

private lemma orderOfVanishingAt_vadd_one (hper : Periodic (g ∘ ofComplex) 1) (p : ℍ) :
    orderOfVanishingAt g ((1 : ℝ) +ᵥ p) = orderOfVanishingAt g p :=
  orderOfVanishingAt_eq_of_coe_eq_add hper <| by simp [add_comm]

private lemma orderOfVanishingAt_vadd_neg_one (hper : Periodic (g ∘ ofComplex) 1) (p : ℍ) :
    orderOfVanishingAt g ((-1 : ℝ) +ᵥ p) = orderOfVanishingAt g p :=
  orderOfVanishingAt_eq_of_coe_eq_add hper.neg <| by simp [add_comm]

private lemma vadd_mem_of_re_eq (hr : |r| ≤ 1) (hS : ∀ q ∈ S, orderOfVanishingAt g q ≠ 0 → q ∈ 𝒟)
    (hcomp : ∀ q, q ∈ 𝒟 → orderOfVanishingAt g q ≠ 0 → q ∈ S)
    (hord : orderOfVanishingAt g (r +ᵥ p) = orderOfVanishingAt g p) (hp : p ∈ S)
    (hre : (p : ℂ).re = -r / 2) (hne : orderOfVanishingAt g p ≠ 0) :
    r +ᵥ p ∈ S ∧ ((r +ᵥ p : ℍ) : ℂ).re = r / 2 ∧ ‖((r +ᵥ p : ℍ) : ℂ)‖ = ‖(p : ℂ)‖ :=
  ⟨hcomp _ (vadd_mem_fd_of_re_eq hr (hS p hp hne) hre) (hord ▸ hne),
    by rw [coe_vadd, add_re, ofReal_re, hre]; ring, norm_coe_vadd_of_re_eq hre⟩

-- Translation by `r` matches the points of modulus `> 1` on `re = a` with those on `re = -a`.
private theorem sum_orderOfVanishingAt_vert_aux {a : ℝ} (hr : |r| ≤ 1) (ha : a = -r / 2)
    (hord : ∀ q : ℍ, orderOfVanishingAt g (r +ᵥ q) = orderOfVanishingAt g q)
    (hS : ∀ q ∈ S, orderOfVanishingAt g q ≠ 0 → q ∈ 𝒟)
    (hcomp : ∀ q, q ∈ 𝒟 → orderOfVanishingAt g q ≠ 0 → q ∈ S) :
    ∑ q ∈ S.filter (fun q : ℍ ↦ (q : ℂ).re = a ∧ 1 < ‖(q : ℂ)‖), orderOfVanishingAt g q =
      ∑ q ∈ S.filter (fun q : ℍ ↦ (q : ℂ).re = -a ∧ 1 < ‖(q : ℂ)‖), orderOfVanishingAt g q := by
  have hord' : ∀ q : ℍ, orderOfVanishingAt g ((-r) +ᵥ q) = orderOfVanishingAt g q := fun q ↦ by
    simpa using (hord ((-r) +ᵥ q)).symm
  refine Finset.sum_bij_ne_zero (fun q _ _ ↦ r +ᵥ q) (fun q hq hne ↦ ?_)
    (fun q₁ _ _ q₂ _ _ ↦ vadd_left_cancel r)
    (fun q hq hne ↦ ⟨(-r) +ᵥ q, ?_, hord' q ▸ hne, by simp⟩) fun q _ _ ↦ (hord q).symm
  · obtain ⟨hqS, hre, hnorm⟩ := Finset.mem_filter.mp hq
    obtain ⟨h₁, h₂, h₃⟩ := vadd_mem_of_re_eq hr hS hcomp (hord q) hqS (hre.trans ha) hne
    exact Finset.mem_filter.mpr ⟨h₁, by rw [h₂, ha]; ring, h₃ ▸ hnorm⟩
  · obtain ⟨hqS, hre, hnorm⟩ := Finset.mem_filter.mp hq
    obtain ⟨h₁, h₂, h₃⟩ := vadd_mem_of_re_eq (by rwa [abs_neg]) hS hcomp (hord' q) hqS
      (by rw [hre, ha]; ring) hne
    exact Finset.mem_filter.mpr ⟨h₁, h₂.trans ha.symm, h₃ ▸ hnorm⟩

end Vertical

/-- **The vertical pairing.** Over a divisor set complete for the closed fundamental domain,
the order sum along the right vertical edge equals the order sum along the left one. -/
theorem sum_orderOfVanishingAt_rightVertical_eq_leftVertical (f : F)
    (hper : Periodic (⇑f ∘ ofComplex) 1) (hS : ∀ p ∈ S, orderOfVanishingAt f p ≠ 0 → p ∈ 𝒟)
    (hcomp : ∀ p, p ∈ 𝒟 → orderOfVanishingAt f p ≠ 0 → p ∈ S) :
    ∑ p ∈ S.filter (fun p : ℍ ↦ (p : ℂ).re = 1 / 2 ∧ 1 < ‖(p : ℂ)‖), orderOfVanishingAt f p =
      ∑ p ∈ S.filter (fun p : ℍ ↦ (p : ℂ).re = -(1 / 2) ∧ 1 < ‖(p : ℂ)‖), orderOfVanishingAt f p :=
  sum_orderOfVanishingAt_vert_aux (r := -1) (by norm_num) (by norm_num)
    (orderOfVanishingAt_vadd_neg_one hper) hS hcomp

section Arc

variable {g : ℍ → ℂ} {p : ℍ}

/-- Slash-invariance carries the vanishing order along the inversion. -/
private lemma orderOfVanishingAt_S_smul [SlashInvariantFormClass F Γ k] (f : F)
    (hSmem : ModularGroup.S ∈ Γ) (p : ℍ) :
    orderOfVanishingAt f (ModularGroup.S • p) = orderOfVanishingAt f p := by
  rw [MulAction.compHom_smul_def]
  exact orderOfVanishingAt_smul f (γ := Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S)
    (Subgroup.mem_map_of_mem _ hSmem)
    (det_pos_of_mem_slGL (MonoidHom.mem_range.mpr ⟨ModularGroup.S, rfl⟩)) p

/-- Over a divisor set complete for `𝒟`, a nonzero-order point of the unit arc is carried by the
inversion back into the set, again on the unit arc, with the real part flipped. -/
private lemma S_smul_mem_of_norm_eq_one (hS : ∀ q ∈ S, orderOfVanishingAt g q ≠ 0 → q ∈ 𝒟)
    (hcomp : ∀ q, q ∈ 𝒟 → orderOfVanishingAt g q ≠ 0 → q ∈ S)
    (hord : orderOfVanishingAt g (ModularGroup.S • p) = orderOfVanishingAt g p) (hp : p ∈ S)
    (hnorm : ‖(p : ℂ)‖ = 1) (hne : orderOfVanishingAt g p ≠ 0) :
    ModularGroup.S • p ∈ S ∧ ‖((ModularGroup.S • p : ℍ) : ℂ)‖ = 1 ∧
      ((ModularGroup.S • p : ℍ) : ℂ).re = -(p : ℂ).re :=
  ⟨hcomp _ (ModularGroup.S_smul_mem_fd_of_norm_eq_one (hS p hp hne).2 hnorm) (hord ▸ hne),
    ModularGroup.norm_coe_S_smul_of_norm_eq_one hnorm,
    by rw [coe_re, ModularGroup.re_S_smul_of_norm_eq_one hnorm, coe_re]⟩

end Arc

/-- **The arc pairing.** Over a divisor set complete for the closed fundamental domain, the
order sum along the right half of the unit arc equals the order sum along the left half:
`z ↦ -1/z` matches the two halves point by point — carrying `ρ + 1` to `ρ` — and
slash-invariance carries the order across. -/
theorem sum_orderOfVanishingAt_rightArc_eq_leftArc [SlashInvariantFormClass F Γ k] (f : F)
    (hSmem : ModularGroup.S ∈ Γ) (hS : ∀ p ∈ S, orderOfVanishingAt f p ≠ 0 → p ∈ 𝒟)
    (hcomp : ∀ p, p ∈ 𝒟 → orderOfVanishingAt f p ≠ 0 → p ∈ S) :
    ∑ p ∈ S.filter (fun p : ℍ ↦ ‖(p : ℂ)‖ = 1 ∧ 0 < (p : ℂ).re), orderOfVanishingAt f p =
      ∑ p ∈ S.filter (fun p : ℍ ↦ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0), orderOfVanishingAt f p := by
  classical
  have hord := orderOfVanishingAt_S_smul f hSmem
  rw [← Finset.sum_filter_ne_zero, ← Finset.sum_filter_ne_zero
    (s := S.filter (fun p : ℍ ↦ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0))]
  refine Finset.sum_nbij' (ModularGroup.S • ·) (ModularGroup.S • ·) (fun q hq ↦ ?_)
    (fun q hq ↦ ?_) (fun q _ ↦ ModularGroup.S_smul_S_smul q)
    (fun q _ ↦ ModularGroup.S_smul_S_smul q)
    (fun q _ ↦ (hord q).symm)
  -- the two halves of the arc are interchanged by the same argument, `re` flipping sign
  all_goals
    simp only [Finset.mem_filter] at hq ⊢
    obtain ⟨⟨hqS, hnorm, hre⟩, hne⟩ := hq
    obtain ⟨h₁, h₂, h₃⟩ := S_smul_mem_of_norm_eq_one hS hcomp (hord q) hqS hnorm hne
    exact ⟨⟨h₁, h₂, by rw [h₃]; linarith⟩, hord q ▸ hne⟩

section Corners

/-- The corner `ρ` lies in the left arc family of a divisor set complete for `𝒟`, as soon as its
order is nonzero. -/
private lemma ρ_mem_leftArc {g : ℍ → ℂ}
    (hcomp : ∀ q, q ∈ 𝒟 → orderOfVanishingAt g q ≠ 0 → q ∈ S)
    (h : orderOfVanishingAt g ρ ≠ 0) :
    ρ ∈ S.filter (fun p : ℍ ↦ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0) :=
  Finset.mem_filter.mpr ⟨hcomp ρ ModularGroup.ρ_mem_fd h, norm_ρ, by norm_num⟩

/-- The corner `ρ + 1` lies in the right arc family of a divisor set complete for `𝒟`, as soon as
the order at `ρ` is nonzero — the two corners carry the same order. -/
private lemma vadd_one_ρ_mem_rightArc {g : ℍ → ℂ}
    (hcomp : ∀ q, q ∈ 𝒟 → orderOfVanishingAt g q ≠ 0 → q ∈ S)
    (hordρ : orderOfVanishingAt g ((1 : ℝ) +ᵥ ρ) = orderOfVanishingAt g ρ)
    (h : orderOfVanishingAt g ρ ≠ 0) :
    (1 : ℝ) +ᵥ ρ ∈ S.filter (fun p : ℍ ↦ ‖(p : ℂ)‖ = 1 ∧ 0 < (p : ℂ).re) :=
  Finset.mem_filter.mpr
    ⟨hcomp _ (vadd_mem_fd_of_re_eq (r := 1) (by norm_num) ModularGroup.ρ_mem_fd
        (by norm_num)) (by rw [hordρ]; exact h),
      by rw [coe_vadd_one_ρ]; exact norm_ρ_add_one,
      by norm_num⟩

end Corners

/-- The arc pairing with the two `ρ`-corners removed: the pairing map matches them with each
other, so deleting one from each half preserves the identity. This is the shape the valence
formula consumes, whose arc family excludes the corner it weights separately. -/
theorem sum_orderOfVanishingAt_rightArc_ne_ρ_add_one_eq_leftArc_ne_ρ
    [SlashInvariantFormClass F Γ k] (f : F) (hper : Periodic (⇑f ∘ ofComplex) 1)
    (hSmem : ModularGroup.S ∈ Γ) (hS : ∀ p ∈ S, orderOfVanishingAt f p ≠ 0 → p ∈ 𝒟)
    (hcomp : ∀ p, p ∈ 𝒟 → orderOfVanishingAt f p ≠ 0 → p ∈ S) :
    ∑ p ∈ S.filter (fun p : ℍ ↦ (p : ℂ) ≠ (ρ : ℂ) + 1 ∧ ‖(p : ℂ)‖ = 1 ∧ 0 < (p : ℂ).re),
        orderOfVanishingAt f p =
      ∑ p ∈ S.filter (fun p : ℍ ↦ (p : ℂ) ≠ (ρ : ℂ) ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0),
        orderOfVanishingAt f p := by
  classical
  have hordρ : orderOfVanishingAt f ((1 : ℝ) +ᵥ ρ) = orderOfVanishingAt f ρ :=
    orderOfVanishingAt_vadd_one hper ρ
  have harc := sum_orderOfVanishingAt_rightArc_eq_leftArc f hSmem hS hcomp
  have hR : S.filter (fun p : ℍ ↦ (p : ℂ) ≠ (ρ : ℂ) + 1 ∧ ‖(p : ℂ)‖ = 1 ∧ 0 < (p : ℂ).re) =
      (S.filter (fun p : ℍ ↦ ‖(p : ℂ)‖ = 1 ∧ 0 < (p : ℂ).re)).filter
        (fun p ↦ p ≠ (1 : ℝ) +ᵥ ρ) := by
    ext q
    simp only [Finset.mem_filter, ne_eq, UpperHalfPlane.ext_iff, coe_vadd_one_ρ]
    tauto
  have hL : S.filter (fun p : ℍ ↦ (p : ℂ) ≠ (ρ : ℂ) ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0) =
      (S.filter (fun p : ℍ ↦ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0)).filter (fun p ↦ p ≠ ρ) := by
    ext q
    simp only [Finset.mem_filter, ne_eq, UpperHalfPlane.ext_iff]
    tauto
  rw [hR, hL, Finset.filter_ne', Finset.filter_ne']
  by_cases h : orderOfVanishingAt f ρ = 0
  · rw [Finset.sum_erase _ (hordρ.trans h), Finset.sum_erase _ h]
    exact harc
  · rw [Finset.sum_erase_eq_sub (vadd_one_ρ_mem_rightArc hcomp hordρ h),
      Finset.sum_erase_eq_sub (ρ_mem_leftArc hcomp h), harc, hordρ]

section Partition

variable {p : ℍ}

/-- The real part of the second corner. -/
private lemma coe_re_ρ_add_one : ((ρ : ℂ) + 1).re = 1 / 2 := by
  norm_num

/-- Each of the four half-edges consists of non-elliptic points that are not strictly interior:
the verticals are cut off from the corners by their modulus, the arc halves by their real part. -/
private lemma notMem_corners_of_half_edge
    (h : ((p : ℂ).re = 1 / 2 ∧ 1 < ‖(p : ℂ)‖) ∨ ((p : ℂ).re = -(1 / 2) ∧ 1 < ‖(p : ℂ)‖) ∨
      ((p : ℂ) ≠ (ρ : ℂ) + 1 ∧ ‖(p : ℂ)‖ = 1 ∧ 0 < (p : ℂ).re) ∨
      ((p : ℂ) ≠ (ρ : ℂ) ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0)) :
    ((p : ℂ) ≠ Complex.I ∧ (p : ℂ) ≠ (ρ : ℂ) ∧ (p : ℂ) ≠ (ρ : ℂ) + 1) ∧
      ¬(1 < ‖(p : ℂ)‖ ∧ |(p : ℂ).re| < 1 / 2) := by
  rcases h with ⟨hre, hn⟩ | ⟨hre, hn⟩ | ⟨hne, hn, hre⟩ | ⟨hne, hn, hre⟩
  · exact ⟨⟨fun h ↦ by rw [h] at hre; norm_num at hre,
      fun h ↦ by rw [h, norm_ρ] at hn; norm_num at hn,
      fun h ↦ by rw [h, norm_ρ_add_one] at hn; norm_num at hn⟩,
      fun h ↦ by rw [hre] at h; norm_num at h⟩
  · exact ⟨⟨fun h ↦ by rw [h] at hre; norm_num at hre,
      fun h ↦ by rw [h, norm_ρ] at hn; norm_num at hn,
      fun h ↦ by rw [h, norm_ρ_add_one] at hn; norm_num at hn⟩,
      fun h ↦ by rw [hre] at h; norm_num at h⟩
  · exact ⟨⟨fun h ↦ by rw [h] at hre; norm_num at hre,
      fun h ↦ by rw [h] at hre; norm_num at hre, hne⟩,
      fun h ↦ by rw [hn] at h; exact absurd h.1 (lt_irrefl 1)⟩
  · exact ⟨⟨fun h ↦ by rw [h] at hre; norm_num at hre, hne,
      fun h ↦ by rw [h, coe_re_ρ_add_one] at hre; norm_num at hre⟩,
      fun h ↦ by rw [hn] at h; exact absurd h.1 (lt_irrefl 1)⟩

/-- A point of `𝒟` that is neither elliptic nor strictly interior lies on one of the four
half-edges: on the unit arc its real part decides which half, and off the arc the failure of
interiority pins its real part to `±1/2`. -/
private lemma half_edge_of_boundary (hp : p ∈ 𝒟) (hI : (p : ℂ) ≠ Complex.I)
    (hρ : (p : ℂ) ≠ (ρ : ℂ)) (hρ₁ : (p : ℂ) ≠ (ρ : ℂ) + 1)
    (hint : ¬(1 < ‖(p : ℂ)‖ ∧ |(p : ℂ).re| < 1 / 2)) :
    ((p : ℂ).re = 1 / 2 ∧ 1 < ‖(p : ℂ)‖) ∨ ((p : ℂ).re = -(1 / 2) ∧ 1 < ‖(p : ℂ)‖) ∨
      ((p : ℂ) ≠ (ρ : ℂ) + 1 ∧ ‖(p : ℂ)‖ = 1 ∧ 0 < (p : ℂ).re) ∨
      ((p : ℂ) ≠ (ρ : ℂ) ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0) := by
  rcases eq_or_lt_of_le (Complex.one_le_normSq_iff.mp hp.1) with heq | hgt
  · rcases lt_trichotomy (p : ℂ).re 0 with h | h | h
    · exact Or.inr (Or.inr (Or.inr ⟨hρ, heq.symm, h⟩))
    · exact absurd ((congrArg _ (eq_I_of_re_eq_zero heq.symm h)).trans coe_I) hI
    · exact Or.inr (Or.inr (Or.inl ⟨hρ₁, heq.symm, h⟩))
  · have habs : |(p : ℂ).re| = 1 / 2 := le_antisymm hp.2 (not_lt.mp fun h ↦ hint ⟨hgt, h⟩)
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1 / 2)).mp habs with h | h
    · exact Or.inl ⟨h, hgt⟩
    · exact Or.inr (Or.inl ⟨h, hgt⟩)

/-- **The pointwise boundary classification.** A point of `𝒟` avoids the three elliptic points
and the open fundamental domain exactly when it lies on one of the four half-edges. -/
lemma mem_boundary_iff (hp : p ∈ 𝒟) :
    ((p : ℂ) ∉ ({Complex.I, (ρ : ℂ), (ρ : ℂ) + 1} : Finset ℂ) ∧
        ¬(1 < ‖(p : ℂ)‖ ∧ |(p : ℂ).re| < 1 / 2)) ↔
      (((p : ℂ).re = 1 / 2 ∧ 1 < ‖(p : ℂ)‖) ∨ ((p : ℂ).re = -(1 / 2) ∧ 1 < ‖(p : ℂ)‖) ∨
        ((p : ℂ) ≠ (ρ : ℂ) + 1 ∧ ‖(p : ℂ)‖ = 1 ∧ 0 < (p : ℂ).re) ∨
        ((p : ℂ) ≠ (ρ : ℂ) ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0)) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  refine ⟨fun ⟨⟨hI, hρ, hρ₁⟩, hint⟩ ↦ half_edge_of_boundary hp hI hρ hρ₁ hint,
    notMem_corners_of_half_edge⟩

end Partition

/-- **The boundary partition.** A non-elliptic point of the closed fundamental domain that is
not strictly interior lies on exactly one of the four half-edges — the two verticals and the
two open arc halves — so the order sum over the non-elliptic boundary splits into the four
half-edge sums. -/
theorem sum_orderOfVanishingAt_nonEllipticBoundary_eq_verticals_add_arcs
    (f : F) (hS : ∀ p ∈ S, orderOfVanishingAt f p ≠ 0 → p ∈ 𝒟) :
    ∑ p ∈ S.filter (fun p : ℍ ↦ (p : ℂ) ∉ ({Complex.I, (ρ : ℂ), (ρ : ℂ) + 1} : Finset ℂ) ∧
        ¬(1 < ‖(p : ℂ)‖ ∧ |(p : ℂ).re| < 1 / 2)), orderOfVanishingAt f p =
      ∑ p ∈ S.filter (fun p : ℍ ↦ (p : ℂ).re = 1 / 2 ∧ 1 < ‖(p : ℂ)‖),
          orderOfVanishingAt f p +
        ∑ p ∈ S.filter (fun p : ℍ ↦ (p : ℂ).re = -(1 / 2) ∧ 1 < ‖(p : ℂ)‖),
          orderOfVanishingAt f p +
        ∑ p ∈ S.filter (fun p : ℍ ↦ (p : ℂ) ≠ (ρ : ℂ) + 1 ∧ ‖(p : ℂ)‖ = 1 ∧ 0 < (p : ℂ).re),
          orderOfVanishingAt f p +
        ∑ p ∈ S.filter (fun p : ℍ ↦ (p : ℂ) ≠ (ρ : ℂ) ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0),
          orderOfVanishingAt f p := by
  classical
  set A₁ := S.filter (fun p : ℍ ↦ (p : ℂ).re = 1 / 2 ∧ 1 < ‖(p : ℂ)‖) with hA₁
  set A₂ := S.filter (fun p : ℍ ↦ (p : ℂ).re = -(1 / 2) ∧ 1 < ‖(p : ℂ)‖) with hA₂
  set A₃ := S.filter (fun p : ℍ ↦ (p : ℂ) ≠ (ρ : ℂ) + 1 ∧ ‖(p : ℂ)‖ = 1 ∧ 0 < (p : ℂ).re) with hA₃
  set A₄ := S.filter (fun p : ℍ ↦ (p : ℂ) ≠ (ρ : ℂ) ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0) with hA₄
  have hd₂ : Disjoint A₁ A₂ := Finset.disjoint_left.mpr fun q hq hq' ↦ by
    simp only [hA₁, hA₂, Finset.mem_filter] at hq hq'
    linarith [hq.2.1, hq'.2.1]
  have hd₃ : Disjoint (A₁ ∪ A₂) A₃ := Finset.disjoint_left.mpr fun q hq hq' ↦ by
    simp only [hA₁, hA₂, hA₃, Finset.mem_union, Finset.mem_filter] at hq hq'
    rcases hq with h | h <;> linarith [h.2.2, hq'.2.2.1]
  have hd₄ : Disjoint (A₁ ∪ A₂ ∪ A₃) A₄ := Finset.disjoint_left.mpr fun q hq hq' ↦ by
    simp only [hA₁, hA₂, hA₃, hA₄, Finset.mem_union, Finset.mem_filter] at hq hq'
    rcases hq with (h | h) | h
    · linarith [h.2.2, hq'.2.2.1]
    · linarith [h.2.2, hq'.2.2.1]
    · linarith [h.2.2.2, hq'.2.2.2]
  have hunion : (S.filter (fun p : ℍ ↦ (p : ℂ) ∉ ({Complex.I, (ρ : ℂ), (ρ : ℂ) + 1} : Finset ℂ) ∧
      ¬(1 < ‖(p : ℂ)‖ ∧ |(p : ℂ).re| < 1 / 2))).filter (fun p ↦ orderOfVanishingAt f p ≠ 0) =
      (A₁ ∪ A₂ ∪ A₃ ∪ A₄).filter (fun p ↦ orderOfVanishingAt f p ≠ 0) := by
    ext q
    simp only [hA₁, hA₂, hA₃, hA₄, Finset.mem_union, Finset.mem_filter]
    refine ⟨fun ⟨⟨hq, hb⟩, hne⟩ ↦ ?_, fun ⟨h, hne⟩ ↦ ?_⟩
    · have := (mem_boundary_iff (hS q hq hne)).mp hb
      tauto
    · have hq : q ∈ S := by tauto
      exact ⟨⟨hq, (mem_boundary_iff (hS q hq hne)).mpr (by tauto)⟩, hne⟩
  rw [← Finset.sum_filter_ne_zero, hunion, Finset.sum_filter_ne_zero,
    Finset.sum_union hd₄, Finset.sum_union hd₃, Finset.sum_union hd₂]

/-- **The boundary sum collapses to left representatives.** Over a divisor set complete for
the closed fundamental domain, the order sum across all non-elliptic boundary points is twice
the sum over one representative per pair — the left vertical and the left arc half without its
corner. Each boundary point carries winding weight `-1/2` in the valence count, so this is the
step that gives each pair a single full-weight representative. -/
theorem sum_orderOfVanishingAt_nonEllipticBoundary_eq_two_mul [SlashInvariantFormClass F Γ k]
    (f : F) (hper : Periodic (⇑f ∘ ofComplex) 1) (hSmem : ModularGroup.S ∈ Γ)
    (hS : ∀ p ∈ S, orderOfVanishingAt f p ≠ 0 → p ∈ 𝒟)
    (hcomp : ∀ p, p ∈ 𝒟 → orderOfVanishingAt f p ≠ 0 → p ∈ S) :
    ∑ p ∈ S.filter (fun p : ℍ ↦ (p : ℂ) ∉ ({Complex.I, (ρ : ℂ), (ρ : ℂ) + 1} : Finset ℂ) ∧
        ¬(1 < ‖(p : ℂ)‖ ∧ |(p : ℂ).re| < 1 / 2)), orderOfVanishingAt f p =
      2 * (∑ p ∈ S.filter (fun p : ℍ ↦ (p : ℂ).re = -(1 / 2) ∧ 1 < ‖(p : ℂ)‖),
          orderOfVanishingAt f p +
        ∑ p ∈ S.filter (fun p : ℍ ↦ (p : ℂ) ≠ (ρ : ℂ) ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0),
          orderOfVanishingAt f p) := by
  rw [sum_orderOfVanishingAt_nonEllipticBoundary_eq_verticals_add_arcs f hS,
    sum_orderOfVanishingAt_rightVertical_eq_leftVertical f hper hS hcomp,
    sum_orderOfVanishingAt_rightArc_ne_ρ_add_one_eq_leftArc_ne_ρ f hper hSmem hS hcomp]
  ring

end ModularForm

end TauCeti

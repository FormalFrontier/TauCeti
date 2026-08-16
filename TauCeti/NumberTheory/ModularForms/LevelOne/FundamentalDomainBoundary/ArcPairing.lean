/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Basic
public import TauCeti.NumberTheory.ModularForms.STransform

import TauCeti.Analysis.Contour.Curve.ExcisionMeasure
import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Deriv

/-!
# The arc self-pairing of the logarithmic-derivative integrand

The reflection `t ↦ 4 - t` carries the unit-circle arc of the boundary contour to its
own reversal through the inversion `S`. Composed with the `S`-transformation law of the
logarithmic derivative of a weight-`k` form, the reflected integrand
`logDeriv g (γ (4 - t)) · γ' (4 - t)` pairs with the direct one up to the weight term
`-k · γ' / γ` — so the two halves of the arc integral collapse to `-k` times the
integral of `γ' / γ`, whose integrand is `π/6 · i` on the open arc and hence almost
everywhere: the arc contributes `-k/12` to the `(2πi)⁻¹`-normalized valence contour,
the term that lands as `k/12` on the divisor side of the valence formula.

## Main declarations

* `TauCeti.ModularForm.logDeriv_comp_ofComplex_fdBoundary_arc_add_four_sub_eq_neg`: the
  direct and reflected arc contour integrands sum to the negated weight term.
* `TauCeti.ModularForm.intervalIntegral_deriv_smul_logDeriv_comp_ofComplex_fdBoundary_arc`:
  the arc contour integral of the form's logarithmic derivative evaluates to
  `-(k * (π/6 * I))`, the arc's `-k/12` contribution to the normalized valence contour.

The same pairing survives `ε`-excision, which is what the principal-value assembly needs:
when the form vanishes at a point *on* the arc the unexcised integrand is not
interval-integrable there, so the boundary integral is assembled from an excised integrand.
Excision is compatible with the reflection whenever the excision set consists of
unit-modulus points closed under the inversion `z ↦ -1/z`.

* `TauCeti.ModularForm.excised_logDeriv_comp_ofComplex_fdBoundary_arc_add_four_sub_eq_neg`:
  the excised pointwise pairing — at an excised parameter both terms vanish, at a retained
  one the direct and reflected excised integrands sum to the excised weight term.
* `two_mul_intervalIntegral_excised_deriv_smul_logDeriv_comp_ofComplex_fdBoundary_arc`
  (in `TauCeti.ModularForm`, unqualified here only to stay inside the line limit) — the
  excised arc integral is `-k/2` times the excised integral of the contour's own
  logarithmic derivative.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development (`ForMathlib/ValenceFormula/PVChain/ArcContribution.lean`) this file ports
  onto the current Mathlib pin.
-/

public section

open Complex MeasureTheory Set UpperHalfPlane

open scoped MatrixGroups Real

namespace TauCeti

namespace ModularForm

variable {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup SL(2, ℤ)} {k : ℤ}

/-- On the open arc, the direct and reflected logarithmic-derivative contour integrands
sum to the negated weight term `-k · logDeriv γ`. -/
theorem logDeriv_comp_ofComplex_fdBoundary_arc_add_four_sub_eq_neg
    [SlashInvariantFormClass F Γ k]
    (f : F) (hS : ModularGroup.S ∈ Γ) {H t : ℝ} (ht : t ∈ Ioo (1 : ℝ) 3)
    (hd : DifferentiableAt ℂ (⇑f ∘ ofComplex) (fdBoundary H t))
    (hne : (⇑f ∘ ofComplex) (fdBoundary H t) ≠ 0) :
    deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t) +
      deriv (fdBoundary H) (4 - t) • logDeriv (⇑f ∘ ofComplex) (fdBoundary H (4 - t)) =
      -(k * logDeriv (fdBoundary H) t) := by
  have him := im_fdBoundary_arc_pos H ⟨ht.1.le, ht.2.le⟩
  have h0 : fdBoundary H t ≠ 0 := fun h ↦ absurd him (by simp [h])
  rw [fdBoundary_four_sub_arc H ⟨ht.1.le, ht.2.le⟩, deriv_fdBoundary_four_sub_arc H ht,
    smul_eq_mul, smul_eq_mul, logDeriv_comp_ofComplex_S_transform f hS him hd hne,
    logDeriv_apply (fdBoundary H) t]
  field_simp
  ring


/-- The reflected-half integrability: interval integrability of the arc contour
integrand on `[2, 3]` follows from integrability on `[1, 2]` through the pairing, which
writes the second half as a reflected constant-minus-first-half integrand. -/
theorem intervalIntegrable_deriv_smul_logDeriv_comp_ofComplex_fdBoundarySegment3
    [SlashInvariantFormClass F Γ k] (f : F) (hS : ModularGroup.S ∈ Γ) {H : ℝ}
    (hd : ∀ t ∈ Ioo (1 : ℝ) 2, DifferentiableAt ℂ (⇑f ∘ ofComplex) (fdBoundary H t))
    (hne : ∀ t ∈ Ioo (1 : ℝ) 2, (⇑f ∘ ofComplex) (fdBoundary H t) ≠ 0)
    (hint : IntervalIntegrable
      (fun t ↦ deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t))
      volume 1 2) :
    IntervalIntegrable
      (fun t ↦ deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t))
      volume 2 3 := by
  have hconst : IntervalIntegrable
      (fun u : ℝ ↦ -(↑k * logDeriv (fdBoundary H) u)) volume 1 2 :=
    ((intervalIntegrable_logDeriv_fdBoundary_arc H ⟨le_rfl, by norm_num⟩
      ⟨by norm_num, by norm_num⟩).const_mul _).neg
  have hI := ((hconst.sub hint).comp_sub_left 4).symm
  have h42 : (4 : ℝ) - 2 = 2 := by norm_num
  have h41 : (4 : ℝ) - 1 = 3 := by norm_num
  rw [h42, h41] at hI
  refine hI.congr_uIoo ?_
  rw [Set.uIoo_of_le (by norm_num : (2 : ℝ) ≤ 3)]
  intro x hx
  have hu : 4 - x ∈ Ioo (1 : ℝ) 2 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hp := logDeriv_comp_ofComplex_fdBoundary_arc_add_four_sub_eq_neg f hS
    ⟨hu.1, by linarith [hu.2]⟩ (hd _ hu) (hne _ hu)
  have hxx : (4 : ℝ) - (4 - x) = x := by ring
  rw [hxx] at hp
  simp only [smul_eq_mul] at hp ⊢
  linear_combination -hp

/-- The arc contour integral of a slash-invariant form's logarithmic derivative is
`-(k * (π/6 * I))` — the arc's `-k/12` contribution to the `(2πi)⁻¹`-normalized valence
contour. The two halves of the arc pair through the `S`-transformation under the
substitution `t ↦ 4 - t`, leaving `-k` times the constant arc integral of the contour's
own logarithmic derivative. -/
theorem intervalIntegral_deriv_smul_logDeriv_comp_ofComplex_fdBoundary_arc
    [SlashInvariantFormClass F Γ k] (f : F)
    (hS : ModularGroup.S ∈ Γ) {H : ℝ}
    (hd : ∀ t ∈ Ioo (1 : ℝ) 2, DifferentiableAt ℂ (⇑f ∘ ofComplex) (fdBoundary H t))
    (hne : ∀ t ∈ Ioo (1 : ℝ) 2, (⇑f ∘ ofComplex) (fdBoundary H t) ≠ 0)
    (hint : IntervalIntegrable
      (fun t ↦ deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t))
      volume 1 2) :
    ∫ t in (1 : ℝ)..3,
        deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t) =
      -(k * ((Real.pi / 6 : ℝ) * Complex.I)) := by
  have hpair : ∀ u ∈ Ioo (1 : ℝ) 2,
      deriv (fdBoundary H) (4 - u) • logDeriv (⇑f ∘ ofComplex) (fdBoundary H (4 - u)) =
        -(↑k * logDeriv (fdBoundary H) u) -
          deriv (fdBoundary H) u • logDeriv (⇑f ∘ ofComplex) (fdBoundary H u) := by
    intro u hu
    have hu13 : u ∈ Ioo (1 : ℝ) 3 := ⟨hu.1, by linarith [hu.2]⟩
    have hp := logDeriv_comp_ofComplex_fdBoundary_arc_add_four_sub_eq_neg f hS hu13
      (hd u hu) (hne u hu)
    linear_combination hp
  have hconst : IntervalIntegrable
      (fun u : ℝ ↦ -(↑k * logDeriv (fdBoundary H) u)) volume 1 2 :=
    ((intervalIntegrable_logDeriv_fdBoundary_arc H ⟨le_rfl, by norm_num⟩
      ⟨by norm_num, by norm_num⟩).const_mul _).neg
  have hint' := intervalIntegrable_deriv_smul_logDeriv_comp_ofComplex_fdBoundarySegment3
    f hS hd hne hint
  rw [← intervalIntegral.integral_add_adjacent_intervals hint hint']
  have h23 : (∫ t in (2 : ℝ)..3,
      deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t)) =
      ∫ u in (1 : ℝ)..2,
        deriv (fdBoundary H) (4 - u) • logDeriv (⇑f ∘ ofComplex) (fdBoundary H (4 - u)) := by
    have h42 : (4 : ℝ) - 2 = 2 := by norm_num
    have h41 : (4 : ℝ) - 1 = 3 := by norm_num
    have h := intervalIntegral_comp_fdBoundary_four_sub H
      (logDeriv (⇑f ∘ ofComplex)) (a := 1) (b := 2)
    rwa [h42, h41] at h
  rw [h23, intervalIntegral.integral_congr_Ioo_of_le (by norm_num) hpair,
    intervalIntegral.integral_sub hconst hint, intervalIntegral.integral_neg,
    intervalIntegral.integral_const_mul,
    integral_logDeriv_fdBoundary_arc H (by norm_num) (by norm_num)]
  push_cast
  ring

/-- The inversion `z ↦ -1/z` turns a difference into the negated difference of inverses, the
shape `dist_inv_inv₀` reads. Division by zero being zero, no nonvanishing is needed. -/
private lemma neg_one_div_sub_neg_one_div (z w : ℂ) :
    -1 / z - -1 / w = -(z⁻¹ - w⁻¹) := by
  rw [neg_div, neg_div, one_div, one_div]
  ring

/-- The inversion `z ↦ -1/z` is an involution: the two sign flips cancel and the reciprocal
is Mathlib's `one_div_one_div`, so no nonvanishing hypothesis is needed. -/
private lemma neg_one_div_neg_one_div (z : ℂ) : -1 / (-1 / z) = z := by
  rw [neg_div, neg_div, div_neg, one_div_one_div, neg_neg]

/-- **The arc excision is symmetric under the reflection.** For an excision set of unit-modulus
points closed under the inversion `z ↦ -1/z`, a point of the arc lies within `ε` of the set
exactly when its reflection `t ↦ 4 - t` does.

Inversion is not an isometry in general — `‖z⁻¹ - w⁻¹‖ = ‖z - w‖ / (‖z‖·‖w‖)` — but it is one
between points of unit modulus, which is why `TauCeti.ModularForm.arcSingularSet` is built from
unit-modulus points: on the arc both `fdBoundary H t` and the excision centres have norm `1`, so
the two distances agree and the truncated integrand pairs with itself under the reflection. -/
private theorem excised_fdBoundary_arc_reflection_iff {H : ℝ} {S : Finset ℂ} {ε : ℝ} {t : ℝ}
    (ht : t ∈ Icc (1 : ℝ) 3) (hnorm : ∀ s ∈ S, ‖s‖ = 1) (hinv : ∀ s ∈ S, -1 / s ∈ S) :
    (∃ s ∈ S, ‖fdBoundary H (4 - t) - s‖ ≤ ε) ↔ ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε := by
  have harc : ‖fdBoundary H t‖ = 1 := norm_fdBoundary_arc ht.1 ht.2
  have h0 : fdBoundary H t ≠ 0 := fun h => by simp [h] at harc
  -- On unit-modulus arguments the inversion preserves distances.
  have hkey : ∀ w : ℂ, ‖w‖ = 1 → ‖fdBoundary H (4 - t) - (-1 / w)‖ = ‖fdBoundary H t - w‖ := by
    intro w hw
    have hw0 : w ≠ 0 := norm_ne_zero_iff.mp (by rw [hw]; norm_num)
    -- The inversion-distance formula is Mathlib's; only the unit-modulus factors are ours.
    rw [fdBoundary_four_sub_arc H ht, neg_one_div_sub_neg_one_div,
      norm_neg, ← dist_eq_norm, dist_inv_inv₀ h0 hw0, dist_eq_norm, harc, hw]
    ring
  constructor
  · rintro ⟨s, hs, hle⟩
    refine ⟨-1 / s, hinv s hs, ?_⟩
    have hs0 : s ≠ 0 := norm_ne_zero_iff.mp (by rw [hnorm s hs]; norm_num)
    rwa [← hkey (-1 / s) (by rw [norm_div, norm_neg, norm_one, hnorm s hs, div_one]),
      neg_one_div_neg_one_div]
  · rintro ⟨s, hs, hle⟩
    exact ⟨-1 / s, hinv s hs, by rwa [hkey s (hnorm s hs)]⟩

/-- **The arc pairing under excision.** At an excised parameter both terms vanish; at a
retained one the direct and reflected excised integrands sum to the excised weight term, exactly
as in `TauCeti.ModularForm.logDeriv_comp_ofComplex_fdBoundary_arc_add_four_sub_eq_neg`.

Regularity is asked only where the integrand is retained: at an excised parameter the form may
vanish or fail to be differentiable, which is the point of excising it. -/
theorem excised_logDeriv_comp_ofComplex_fdBoundary_arc_add_four_sub_eq_neg
    [SlashInvariantFormClass F Γ k] (f : F) (hS : ModularGroup.S ∈ Γ)
    {H : ℝ} {S : Finset ℂ} {ε : ℝ} {t : ℝ} (ht : t ∈ Ioo (1 : ℝ) 3)
    (hnorm : ∀ s ∈ S, ‖s‖ = 1) (hinv : ∀ s ∈ S, -1 / s ∈ S)
    (hd : ¬(∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε) →
      DifferentiableAt ℂ (⇑f ∘ ofComplex) (fdBoundary H t))
    (hne : ¬(∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε) →
      (⇑f ∘ ofComplex) (fdBoundary H t) ≠ 0) :
    (if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
        else deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t)) +
      (if ∃ s ∈ S, ‖fdBoundary H (4 - t) - s‖ ≤ ε then 0
        else deriv (fdBoundary H) (4 - t) • logDeriv (⇑f ∘ ofComplex) (fdBoundary H (4 - t))) =
      if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
        else -((k : ℂ) * logDeriv (fdBoundary H) t) := by
  have hsymm := excised_fdBoundary_arc_reflection_iff (H := H) (S := S) (ε := ε)
    ⟨ht.1.le, ht.2.le⟩ hnorm hinv
  by_cases hc : ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε
  · simp only [ite_eq_left hc, ite_eq_left (hsymm.mpr hc), add_zero]
  · simp only [ite_eq_right hc, ite_eq_right fun h => hc (hsymm.mp h)]
    exact logDeriv_comp_ofComplex_fdBoundary_arc_add_four_sub_eq_neg f hS ht (hd hc) (hne hc)

/-- **An excised constant is interval-integrable.** It is measurable, because the excision set
is, and bounded by the constant's norm. -/
theorem intervalIntegrable_excised_const {H ε : ℝ} {S : Finset ℂ} (c : ℂ) (a b : ℝ) :
    IntervalIntegrable
      (fun t => if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then (0 : ℂ) else c) volume a b := by
  have hmeas : Measurable
      (fun t => if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then (0 : ℂ) else c) :=
    measurable_const.ite
      (Contour.measurableSet_excision (continuous_fdBoundary H).measurable S ε) measurable_const
  have hbdd : ∀ t : ℝ,
      ‖(if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then (0 : ℂ) else c)‖ ≤ ‖c‖ := by
    intro t
    by_cases h : ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε <;> simp [h]
  exact ⟨(integrable_const ‖c‖).mono' hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => hbdd t),
    (integrable_const ‖c‖).mono' hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => hbdd t)⟩

/-- **Integrability on the second arc half, excised.** The reflection `t ↦ 4 - t` exchanges
the two halves of the arc, and the excised pointwise pairing identity rewrites the integrand
on `[2, 3]` as the excised weight minus the reflected integrand on `[1, 2]` — both integrable.
This is the excised counterpart of
`intervalIntegrable_deriv_smul_logDeriv_comp_ofComplex_fdBoundarySegment3`. -/
theorem intervalIntegrable_excised_deriv_smul_logDeriv_comp_ofComplex_fdBoundarySegment3
    [SlashInvariantFormClass F Γ k] (f : F) (hS : ModularGroup.S ∈ Γ) {H : ℝ} {S : Finset ℂ}
    {ε : ℝ} (hnorm : ∀ s ∈ S, ‖s‖ = 1) (hinv : ∀ s ∈ S, -1 / s ∈ S)
    (hd : ∀ t ∈ Ioo (1 : ℝ) 2, ¬(∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε) →
      DifferentiableAt ℂ (⇑f ∘ ofComplex) (fdBoundary H t))
    (hne : ∀ t ∈ Ioo (1 : ℝ) 2, ¬(∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε) →
      (⇑f ∘ ofComplex) (fdBoundary H t) ≠ 0)
    (hint : IntervalIntegrable (fun t => if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
      else deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t)) volume 1 2) :
    IntervalIntegrable (fun t => if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
      else deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t)) volume 2 3 := by
  have hconst : IntervalIntegrable (fun u : ℝ =>
      if ∃ s ∈ S, ‖fdBoundary H u - s‖ ≤ ε then 0
        else -((k : ℂ) * logDeriv (fdBoundary H) u)) volume 1 2 := by
    refine (intervalIntegrable_excised_const (H := H) (S := S) (ε := ε)
      (-((k : ℂ) * ((Real.pi / 6 : ℝ) * Complex.I))) 1 2).congr_uIoo fun u hu => ?_
    rw [Set.uIoo_of_le (by norm_num : (1 : ℝ) ≤ 2)] at hu
    by_cases hc : ∃ s ∈ S, ‖fdBoundary H u - s‖ ≤ ε
    · simp only [ite_eq_left hc]
    · simp only [ite_eq_right hc, logDeriv_fdBoundary_arc ⟨hu.1, by linarith [hu.2]⟩]
  have hI := ((hconst.sub hint).comp_sub_left 4).symm
  norm_num at hI
  refine hI.congr_uIoo ?_
  rw [Set.uIoo_of_le (by norm_num : (2 : ℝ) ≤ 3)]
  intro x hx
  have hu : 4 - x ∈ Ioo (1 : ℝ) 2 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hp := excised_logDeriv_comp_ofComplex_fdBoundary_arc_add_four_sub_eq_neg f hS
    ⟨hu.1, by linarith [hu.2]⟩ hnorm hinv (hd _ hu) (hne _ hu)
  rw [sub_sub_self] at hp
  linear_combination -hp

/-- The excised weight term is invariant under the arc reflection `t ↦ 4 - t`: the excision
test is invariant by `excised_fdBoundary_arc_reflection_iff`, and the contour's own
logarithmic derivative is the constant `π/6 · I` on the whole open arc. -/
private lemma excised_weight_fdBoundary_arc_four_sub {H : ℝ} {S : Finset ℂ} {ε : ℝ} {t : ℝ}
    (hnorm : ∀ s ∈ S, ‖s‖ = 1) (hinv : ∀ s ∈ S, -1 / s ∈ S) (ht : t ∈ Ioo (1 : ℝ) 3) :
    (if ∃ s ∈ S, ‖fdBoundary H (4 - t) - s‖ ≤ ε then 0
      else -((k : ℂ) * logDeriv (fdBoundary H) (4 - t))) =
    if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0 else -((k : ℂ) * logDeriv (fdBoundary H) t) := by
  have h4t : 4 - t ∈ Ioo (1 : ℝ) 3 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  rw [logDeriv_fdBoundary_arc ht, logDeriv_fdBoundary_arc h4t]
  exact if_congr (excised_fdBoundary_arc_reflection_iff ⟨ht.1.le, ht.2.le⟩ hnorm hinv) rfl rfl

/-- Integrating the pointwise pairing over `[1, 3]`: the direct and reflected excised
integrands sum to the excised weight term.

The pointwise identity is only assumed on the first half. It is symmetric under `t ↦ 4 - t`,
so on the second half it follows from the first through
`excised_weight_fdBoundary_arc_four_sub`; the reflection's fixed point `t = 2` and the
endpoint `t = 3` are null, which is why this is an almost-everywhere congruence. -/
private lemma intervalIntegral_excised_logDeriv_comp_ofComplex_fdBoundary_arc_add_four_sub_eq_neg
    [SlashInvariantFormClass F Γ k] (f : F)
    (hS : ModularGroup.S ∈ Γ) {H : ℝ} {S : Finset ℂ} {ε : ℝ} (hnorm : ∀ s ∈ S, ‖s‖ = 1)
    (hinv : ∀ s ∈ S, -1 / s ∈ S)
    (hd : ∀ t ∈ Ioo (1 : ℝ) 2, ¬(∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε) →
      DifferentiableAt ℂ (⇑f ∘ ofComplex) (fdBoundary H t))
    (hne : ∀ t ∈ Ioo (1 : ℝ) 2, ¬(∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε) →
      (⇑f ∘ ofComplex) (fdBoundary H t) ≠ 0) :
    (∫ t in (1 : ℝ)..3, ((if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
        else deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t)) +
      (if ∃ s ∈ S, ‖fdBoundary H (4 - t) - s‖ ≤ ε then 0
        else deriv (fdBoundary H) (4 - t) • logDeriv (⇑f ∘ ofComplex) (fdBoundary H (4 - t))))) =
      ∫ t in (1 : ℝ)..3, (if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
        else -((k : ℂ) * logDeriv (fdBoundary H) t)) := by
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [volume.ae_ne (2 : ℝ), volume.ae_ne (3 : ℝ)] with t ht2 ht3 htI
  rw [Set.uIoc_of_le (by norm_num : (1 : ℝ) ≤ 3)] at htI
  have ht13 : t ∈ Ioo (1 : ℝ) 3 := ⟨htI.1, htI.2.lt_of_ne ht3⟩
  rcases ht2.lt_or_gt with h2 | h2
  · exact excised_logDeriv_comp_ofComplex_fdBoundary_arc_add_four_sub_eq_neg f hS ht13 hnorm hinv
      (hd t ⟨ht13.1, h2⟩) (hne t ⟨ht13.1, h2⟩)
  · have hu : 4 - t ∈ Ioo (1 : ℝ) 2 := ⟨by linarith [ht13.2], by linarith⟩
    have h := excised_logDeriv_comp_ofComplex_fdBoundary_arc_add_four_sub_eq_neg f hS
      ⟨hu.1, by linarith [hu.2]⟩ hnorm hinv (hd _ hu) (hne _ hu)
    rw [sub_sub_self (4 : ℝ) t, excised_weight_fdBoundary_arc_four_sub hnorm hinv ht13] at h
    exact (add_comm _ _).trans h

/-- **The excised arc integral collapses to the weight term.** Integrating the pointwise pairing
over `[1, 3]`, where the reflection `t ↦ 4 - t` maps the interval to itself, the excised arc
integral is `-k/2` times the excised integral of the contour's own logarithmic derivative.

The statement is for one fixed `ε` and one fixed excision set `S`; it asserts nothing about a
limit. Its intended use is as the `ε`-uniform input to the principal-value assembly, which
supplies the extra hypotheses that identify a principal value — that `S` captures every zero
of the form on the arc, and the convergence of the excised right-hand side as the excision
shrinks. Neither is assumed here, and neither follows from this statement alone.

The excised form is what the assembly needs because where the form vanishes on the arc the
unexcised integrand is not interval-integrable. Only when the form is zero-free on the arc
does this specialize to the untruncated
`TauCeti.ModularForm.intervalIntegral_deriv_smul_logDeriv_comp_ofComplex_fdBoundary_arc`. -/
theorem two_mul_intervalIntegral_excised_deriv_smul_logDeriv_comp_ofComplex_fdBoundary_arc
    [SlashInvariantFormClass F Γ k]
    (f : F) (hS : ModularGroup.S ∈ Γ) {H : ℝ} {S : Finset ℂ} {ε : ℝ}
    (hnorm : ∀ s ∈ S, ‖s‖ = 1) (hinv : ∀ s ∈ S, -1 / s ∈ S)
    (hd : ∀ t ∈ Ioo (1 : ℝ) 2, ¬(∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε) →
      DifferentiableAt ℂ (⇑f ∘ ofComplex) (fdBoundary H t))
    (hne : ∀ t ∈ Ioo (1 : ℝ) 2, ¬(∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε) →
      (⇑f ∘ ofComplex) (fdBoundary H t) ≠ 0)
    (hint : IntervalIntegrable (fun t => if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
      else deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t)) volume 1 2) :
    2 * ∫ t in (1 : ℝ)..3, (if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
        else deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t)) =
      -(k : ℂ) * ∫ t in (1 : ℝ)..3, (if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
        else logDeriv (fdBoundary H) t) := by
  set G : ℝ → ℂ := fun t => if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
    else deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t) with hG
  -- The reflection maps `[1, 3]` to itself, so the reflected integral is the same integral.
  have h43 : (4 : ℝ) - 3 = 1 := by norm_num
  have h41 : (4 : ℝ) - 1 = 3 := by norm_num
  have hrefl : (∫ t in (1 : ℝ)..3, G (4 - t)) = ∫ t in (1 : ℝ)..3, G t := by
    have h := intervalIntegral.integral_comp_sub_left (a := (1 : ℝ)) (b := 3) (d := (4 : ℝ)) G
    rwa [h43, h41] at h
  -- Integrability on `[2, 3]` is not assumed: the pairing gives it from the `[1, 2]` half.
  have hint13 : IntervalIntegrable G volume 1 3 :=
    hint.trans <| intervalIntegrable_excised_deriv_smul_logDeriv_comp_ofComplex_fdBoundarySegment3
      f hS hnorm hinv hd hne hint
  have hintrefl : IntervalIntegrable (fun t => G (4 - t)) volume 1 3 := by
    have h := hint13.comp_sub_left 4
    rw [h43, h41] at h
    exact h.symm
  -- Stated against `G` rather than taken raw from the lemma: `set` leaves `hsum`'s own
  -- statement spelled out, and the `integral_add` rewrite below is phrased in `G`.
  have hsum : (∫ t in (1 : ℝ)..3, (G t + G (4 - t))) =
      ∫ t in (1 : ℝ)..3, (if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
        else -((k : ℂ) * logDeriv (fdBoundary H) t)) :=
    intervalIntegral_excised_logDeriv_comp_ofComplex_fdBoundary_arc_add_four_sub_eq_neg
      f hS hnorm hinv hd hne
  rw [intervalIntegral.integral_add hint13 hintrefl, hrefl] at hsum
  rw [two_mul, hsum, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  by_cases hc : ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε <;> simp [hc]

end ModularForm

end TauCeti

end

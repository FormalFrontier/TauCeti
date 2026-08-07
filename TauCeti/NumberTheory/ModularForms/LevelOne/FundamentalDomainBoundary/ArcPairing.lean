/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Basic
public import TauCeti.NumberTheory.ModularForms.STransform

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
theorem intervalIntegrable_deriv_smul_logDeriv_comp_ofComplex_fdBoundary_segment3
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
  have hint' := intervalIntegrable_deriv_smul_logDeriv_comp_ofComplex_fdBoundary_segment3
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

end ModularForm

end TauCeti

end

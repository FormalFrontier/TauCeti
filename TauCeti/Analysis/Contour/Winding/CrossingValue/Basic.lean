/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Winding.Integrand
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# The real winding integrand at a crossing

This file proves the local crossing-value calculation in Hungerbühler–Wasem Proposition 2.3.
For a plane curve `γ` passing through `s` at `t₀` whose chord and velocity have the stated filter
expansions, the apparently singular real winding integrand

`(x ẏ - y ẋ) / (x² + y²)`, where `x + iy = γ - s`,

tends to `(L.re * A.im - L.im * A.re) / (2 * ‖L‖²)`, where `L` and `A` are the coefficients
in those expansions.

The theorem is stated using two Peano expansions, independently of any particular
second-derivative API.

As prescribed by the contour integration roadmap, the answer is given by an explicit coordinate
formula.

## Main results

* `Contour.tendsto_realWindingIntegrand_at_crossing` gives the crossing value for a curve.

## References

N. Hungerbühler and M. Wasem, *Non-integer valued winding numbers and a generalized Residue
Theorem*, arXiv:1808.00997 (2018), Proposition 2.3.
-/

public section

noncomputable section

namespace TauCeti.Contour

open Complex Filter Topology

/-- **The winding integrand of a normalized chord expansion.** For `τ ≠ 0` and `q - L = τ r`, the
real winding integrand at position `τ q` and velocity `L + τ d` is
`(r.re * L.im - r.im * L.re + (q.re * d.im - q.im * d.re)) / ‖q‖²`.

At `q = 0` both sides are `0`, by the junk value of division. -/
private theorem realWindingIntegrand_mul_add_eq_div_of_sub_eq_mul {τ : ℝ} {q r d L : ℂ}
    (hτ : τ ≠ 0) (hqr : q - L = (τ : ℂ) * r) :
    realWindingIntegrand ((τ : ℂ) * q) (L + (τ : ℂ) * d)
      = (r.re * L.im - r.im * L.re + (q.re * d.im - q.im * d.re)) / Complex.normSq q := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  obtain rfl : L = q - (τ : ℂ) * r := by linear_combination -hqr
  rw [realWindingIntegrand_eq_div]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    add_zero, sub_zero, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.normSq_mul, Complex.normSq_ofReal]
  field_simp [hτ, Complex.normSq_eq_zero.not.mpr hq]
  ring

/-- Algebraic form of the crossing limit. If `q → L`, `(q - L) / τ → A/2`, and
`d → A`, then the real winding integrand of position `τq` and velocity `L + τd` tends to
`(L.re * A.im - L.im * A.re) / (2‖L‖²)`.

The hypotheses are precisely the normalized second-order position expansion and first-order
velocity expansion. -/
private theorem tendsto_realWindingIntegrand_mul_add {α : Type*} {l : Filter α}
    {τ : α → ℝ} {q r d : α → ℂ} {L A : ℂ} (hL : L ≠ 0)
    (hq : Tendsto q l (𝓝 L)) (hr : Tendsto r l (𝓝 (A / 2))) (hd : Tendsto d l (𝓝 A))
    (hqr : ∀ᶠ i in l, q i - L = ((τ i : ℝ) : ℂ) * r i) (hτ : ∀ᶠ i in l, τ i ≠ 0) :
    Tendsto (fun i ↦ realWindingIntegrand (((τ i : ℝ) : ℂ) * q i)
      (L + ((τ i : ℝ) : ℂ) * d i)) l
      (𝓝 ((L.re * A.im - L.im * A.re) / (2 * Complex.normSq L))) := by
  have hnorm : Tendsto (fun i ↦ Complex.normSq (q i)) l (𝓝 (Complex.normSq L)) :=
    (Complex.continuous_normSq.tendsto L).comp hq
  have hq_re := (Complex.continuous_re.tendsto L).comp hq
  have hq_im := (Complex.continuous_im.tendsto L).comp hq
  have hr_re := (Complex.continuous_re.tendsto (A / 2)).comp hr
  have hr_im := (Complex.continuous_im.tendsto (A / 2)).comp hr
  have hd_re := (Complex.continuous_re.tendsto A).comp hd
  have hd_im := (Complex.continuous_im.tendsto A).comp hd
  have hnum : Tendsto (fun i ↦
      (r i).re * L.im - (r i).im * L.re +
        ((q i).re * (d i).im - (q i).im * (d i).re)) l
      (𝓝 ((L.re * A.im - L.im * A.re) / 2)) := by
    convert (((hr_re.mul_const L.im).sub (hr_im.mul_const L.re)).add
      ((hq_re.mul hd_im).sub (hq_im.mul hd_re))) using 1
    all_goals simp <;> ring_nf
  have hdiv := hnum.div hnorm ((Complex.normSq_eq_zero.not.mpr hL))
  convert hdiv.congr' ?_ using 1
  · ring_nf
  filter_upwards [hqr, hτ] with i hqi hτi
  simp only [Pi.div_apply]
  exact (realWindingIntegrand_mul_add_eq_div_of_sub_eq_mul hτi hqi).symm

/-- **Hungerbühler–Wasem Proposition 2.3, crossing value.** At a crossing `γ t₀ = s`,
a normalized second-order chord expansion with coefficients `L` and `A`, together with the
matching first-order velocity expansion, implies

`(x ẏ - y ẋ) / (x² + y²) → (L.re * A.im - L.im * A.re) / (2 * ‖L‖²)`.

The conclusion refers only to the coefficients in the assumed filter expansions. -/
theorem tendsto_realWindingIntegrand_at_crossing {α : Type*} {l : Filter α}
    {t : α → ℝ} {t₀ : ℝ} {γ : ℝ → ℂ} {s L A : ℂ} (hL : L ≠ 0)
    (htend : Tendsto t l (𝓝 t₀)) (hcross : γ t₀ = s) (hpos₂ : Tendsto (fun i ↦
      (((γ (t i) - s) / (((t i - t₀ : ℝ) : ℂ))) - L) / (((t i - t₀ : ℝ) : ℂ))) l (𝓝 (A / 2)))
    (hvel : Tendsto (fun i ↦ (deriv γ (t i) - L) / (((t i - t₀ : ℝ) : ℂ))) l (𝓝 A))
    (ht : ∀ᶠ i in l, t i ≠ t₀) :
    Tendsto (fun i ↦ realWindingIntegrand (γ (t i) - s) (deriv γ (t i))) l
      (𝓝 ((L.re * A.im - L.im * A.re) / (2 * Complex.normSq L))) := by
  subst s
  let τ : α → ℝ := fun i ↦ t i - t₀
  let q : α → ℂ := fun i ↦ (γ (t i) - γ t₀) / ((τ i : ℝ) : ℂ)
  let r : α → ℂ := fun i ↦ (q i - L) / ((τ i : ℝ) : ℂ)
  let d : α → ℂ := fun i ↦ (deriv γ (t i) - L) / ((τ i : ℝ) : ℂ)
  -- `r`, `d` are `hpos₂`, `hvel` with `s = γ t₀` and `τ = t - t₀` folded into the wrappers.
  have hr : Tendsto r l (𝓝 (A / 2)) := by simpa only [r, q, τ] using hpos₂
  have hd : Tendsto d l (𝓝 A) := by simpa only [d, τ] using hvel
  have hτ : ∀ᶠ i in l, τ i ≠ 0 := ht.mono fun i hi ↦ sub_ne_zero.mpr hi
  have hqr : ∀ᶠ i in l, q i - L = ((τ i : ℝ) : ℂ) * r i := hτ.mono fun i hi ↦ by
    simp only [r]
    field_simp [Complex.ofReal_ne_zero.mpr hi]
  have hτ_zero : Tendsto τ l (𝓝 0) := by
    simpa only [τ, sub_self] using htend.sub_const t₀
  have hq : Tendsto q l (𝓝 L) := by
    have hmul : Tendsto (fun i ↦ ((τ i : ℝ) : ℂ) * r i) l (𝓝 0) := by
      convert ((Complex.continuous_ofReal.tendsto 0).comp hτ_zero).mul hr using 1 <;> simp
    have hadd := hmul.add_const L
    simpa only [zero_add] using hadd.congr' (hqr.mono fun i hi ↦ by
      rw [← hi, sub_add_cancel])
  have hmain := tendsto_realWindingIntegrand_mul_add hL hq hr hd hqr hτ
  apply hmain.congr'
  filter_upwards [hτ] with i hi
  have hiℂ : ((τ i : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hi
  congr 1
  · simp only [q, τ] at hiℂ ⊢
    field_simp [hiℂ]
  · simp only [d, τ] at hiℂ ⊢
    field_simp [hiℂ]
    ring

end TauCeti.Contour

end

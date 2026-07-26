/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Complex.Conformal.Reflection.Basic
public import Mathlib.Analysis.Complex.HasPrimitives

/-!
# The Schwarz reflection principle across the real axis

This file proves the summit of the conformal-mapping roadmap's Schwarz-reflection layer (L4 in
`ConformalMapping/README.md`, the `sorry`-goal stated in `ConformalMapping/Suggested.lean`): on a
conjugation-symmetric open set `Ω`, a function that is continuous on the closed upper part,
holomorphic on the open upper part, and real on `Ω ∩ ℝ` extends *holomorphically* across the real
axis. The extension is the explicit witness `schwarzReflection f` from `Reflection/Basic.lean`,
whose gluing calculus (continuity on all of `Ω`, holomorphy off the axis, the derivative formulas
and the conjugation symmetry) is already established there. What remains — and is proved here — is
holomorphy *at* the axis, the one step that needs Morera's theorem.

The proof is the classical Morera argument. By
`Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn`, holomorphy on the open set `Ω`
is equivalent to continuity together with the vanishing of every rectangle-boundary integral
(`Complex.IsConservativeOn`). Continuity is already available; for the rectangle integrals we split
each rectangle at the real axis into its part above and its part below. Each half is bounded by the
axis, so its *open interior* misses the axis entirely, where `schwarzReflection f` is holomorphic;
Mathlib's continuous-on-closed Cauchy–Goursat lemma
`Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn` then makes each half's
boundary integral vanish, and the shared axis edge cancels when the two halves are recombined.

The Cauchy foundations consumed here are Mathlib's: the rectangle Cauchy–Goursat theorem
(`Analysis/Complex/CauchyIntegral.lean`) and the disc Morera theorem
(`Analysis/Complex/HasPrimitives.lean`). As with the rest of the L0–L3/L4 conformal-mapping
material, this is coordinated with the upstream Mathlib Riemann-mapping effort
leanprover-community/mathlib4#33505; L4 (reflection) is not part of that draft, so this is genuinely
new Lean formalization, but any shared foundational API should be refactored to Mathlib's once it
lands.
-/

public section

namespace TauCeti

open Complex Set intervalIntegral MeasureTheory
open scoped ComplexConjugate Interval

variable {f : ℂ → ℂ}

/-- A rectangle whose open interior avoids the real axis has a vanishing boundary integral for
any function continuous on a domain `Ω` containing the (closed) rectangle and holomorphic on the
part of `Ω` off the real axis. This is the per-rectangle input to Morera's theorem; it is applied
both to axis-avoiding rectangles directly and to the two axis-bounded halves of a straddling
rectangle. -/
private lemma boundaryIntegral_eq_zero_off_axis {Ω : Set ℂ} {F : ℂ → ℂ}
    (hFcont : ContinuousOn F Ω)
    (hFdiff : DifferentiableOn ℂ F (Ω ∩ {z : ℂ | z.im ≠ 0}))
    {z w : ℂ} (hsub : Complex.Rectangle z w ⊆ Ω)
    (haxis : (0 : ℝ) ∉ Set.Ioo (min z.im w.im) (max z.im w.im)) :
    ((∫ x : ℝ in z.re..w.re, F (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, F (x + w.im * I)) +
        I • (∫ y : ℝ in z.im..w.im, F (w.re + y * I)) -
        I • (∫ y : ℝ in z.im..w.im, F (z.re + y * I))) = 0 := by
  refine integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn F z w
    (hFcont.mono hsub) (hFdiff.mono fun p hp => ?_)
  rw [Complex.mem_reProdIm] at hp
  refine ⟨hsub ?_, ?_⟩
  · rw [Complex.Rectangle, Complex.mem_reProdIm]
    refine ⟨?_, ?_⟩
    · rw [Ioo_min_max] at hp; exact uIoo_subset_uIcc_self hp.1
    · rw [Ioo_min_max] at hp; exact uIoo_subset_uIcc_self hp.2
  · exact fun h0 => haxis (h0 ▸ hp.2)

/-- A rectangle with a horizontal edge *on* the real axis — one of its imaginary coordinates is `0`
— has a vanishing boundary integral. This is `boundaryIntegral_eq_zero_off_axis` in the case where
the axis meets an edge rather than being avoided outright: an endpoint at `0` still keeps `0` out of
the *open* imaginary interior. It is the form applied to the two axis-bounded halves of a straddling
rectangle. -/
private lemma boundaryIntegral_eq_zero_of_edge_on_axis {Ω : Set ℂ} {F : ℂ → ℂ}
    (hFcont : ContinuousOn F Ω)
    (hFdiff : DifferentiableOn ℂ F (Ω ∩ {z : ℂ | z.im ≠ 0}))
    {z w : ℂ} (hsub : Complex.Rectangle z w ⊆ Ω) (haxis : z.im = 0 ∨ w.im = 0) :
    ((∫ x : ℝ in z.re..w.re, F (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, F (x + w.im * I)) +
        I • (∫ y : ℝ in z.im..w.im, F (w.re + y * I)) -
        I • (∫ y : ℝ in z.im..w.im, F (z.re + y * I))) = 0 := by
  refine boundaryIntegral_eq_zero_off_axis hFcont hFdiff hsub fun hm => ?_
  -- One imaginary coordinate being `0` puts `0` on the boundary of the imaginary interval, not
  -- inside its open interior `Ioo (min …) (max …)`.
  rcases haxis with h | h <;> rw [h] at hm
  · rcases le_total (0 : ℝ) w.im with hw | hw
    · rw [min_eq_left hw] at hm; exact lt_irrefl (0 : ℝ) hm.1
    · rw [max_eq_left hw] at hm; exact lt_irrefl (0 : ℝ) hm.2
  · rcases le_total z.im 0 with hz | hz
    · rw [max_eq_right hz] at hm; exact lt_irrefl (0 : ℝ) hm.2
    · rw [min_eq_right hz] at hm; exact lt_irrefl (0 : ℝ) hm.1

/-- The integral of `F` along a vertical edge of the rectangle — the edge with fixed real part `a`
— splits at the real axis: the interval integral over `[[z.im, w.im]]` equals the sum of the
integrals over `z.im → 0` and `0 → w.im`, whenever `F` is continuous on a domain `Ω` containing the
rectangle and `0` lies in the imaginary range `[[z.im, w.im]]`. This is the edge-splitting step
used to recombine the two halves of a straddling rectangle. -/
private lemma vertical_edge_split_at_zero {Ω : Set ℂ} {F : ℂ → ℂ}
    (hFcont : ContinuousOn F Ω) {z w : ℂ} (hsub : Complex.Rectangle z w ⊆ Ω)
    (h0mem : (0 : ℝ) ∈ [[z.im, w.im]]) {a : ℝ} (ha : a ∈ [[z.re, w.re]]) :
    (∫ y : ℝ in z.im..w.im, F (↑a + ↑y * I)) =
      (∫ y : ℝ in z.im..(0 : ℝ), F (↑a + ↑y * I)) +
        ∫ y : ℝ in (0 : ℝ)..w.im, F (↑a + ↑y * I) := by
  -- `F` is continuous along the edge, hence interval-integrable on the parts below and above `0`.
  have contV : ContinuousOn (fun t : ℝ => F (↑a + ↑t * I)) [[z.im, w.im]] :=
    hFcont.comp (by fun_prop) fun t ht => hsub (by
      rw [Complex.Rectangle, Complex.mem_reProdIm]
      exact ⟨by simpa using ha, by simpa using ht⟩)
  refine (integral_add_adjacent_intervals ?_ ?_).symm
  · exact (contV.mono (uIcc_subset_uIcc left_mem_uIcc h0mem)).intervalIntegrable
  · exact (contV.mono (uIcc_subset_uIcc h0mem right_mem_uIcc)).intervalIntegrable

/-- A rectangle that *straddles* the real axis — `0` lies strictly inside its imaginary range — has
a vanishing boundary integral: split it at the axis into a lower and an upper half, each an
axis-bounded rectangle handled by `boundaryIntegral_eq_zero_of_edge_on_axis`, and recombine, the
shared axis edge cancelling. Same hypotheses as `boundaryIntegral_eq_zero_off_axis`, but with `0`
in the open imaginary interior instead of outside it. -/
private lemma boundaryIntegral_eq_zero_of_straddling {Ω : Set ℂ} {F : ℂ → ℂ}
    (hFcont : ContinuousOn F Ω)
    (hFdiff : DifferentiableOn ℂ F (Ω ∩ {z : ℂ | z.im ≠ 0}))
    {z w : ℂ} (hsub : Complex.Rectangle z w ⊆ Ω)
    (hstr : (0 : ℝ) ∈ Set.Ioo (min z.im w.im) (max z.im w.im)) :
    ((∫ x : ℝ in z.re..w.re, F (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, F (x + w.im * I)) +
        I • (∫ y : ℝ in z.im..w.im, F (w.re + y * I)) -
        I • (∫ y : ℝ in z.im..w.im, F (z.re + y * I))) = 0 := by
  have h0mem : (0 : ℝ) ∈ [[z.im, w.im]] := by
    rw [← Icc_min_max]; exact Ioo_subset_Icc_self hstr
  -- Split each vertical edge at the axis into its part below and its part above.
  have splitVw := vertical_edge_split_at_zero hFcont hsub h0mem right_mem_uIcc
  have splitVz := vertical_edge_split_at_zero hFcont hsub h0mem left_mem_uIcc
  -- The lower half `[z, ↑w.re]` and the upper half `[↑z.re, w]`, each bounded by the axis.
  have hsubR1 : Complex.Rectangle z (↑w.re : ℂ) ⊆ Ω := by
    refine fun p hp => hsub ?_
    rw [Complex.Rectangle, Complex.mem_reProdIm] at hp ⊢
    simp only [Complex.ofReal_re, Complex.ofReal_im] at hp
    exact ⟨hp.1, uIcc_subset_uIcc left_mem_uIcc h0mem hp.2⟩
  have hsubR2 : Complex.Rectangle (↑z.re : ℂ) w ⊆ Ω := by
    refine fun p hp => hsub ?_
    rw [Complex.Rectangle, Complex.mem_reProdIm] at hp ⊢
    simp only [Complex.ofReal_re, Complex.ofReal_im] at hp
    exact ⟨hp.1, uIcc_subset_uIcc h0mem right_mem_uIcc hp.2⟩
  have R1 := boundaryIntegral_eq_zero_of_edge_on_axis hFcont hFdiff hsubR1
    (Or.inr (Complex.ofReal_im w.re))
  have R2 := boundaryIntegral_eq_zero_of_edge_on_axis hFcont hFdiff hsubR2
    (Or.inl (Complex.ofReal_im z.re))
  simp only [Complex.ofReal_re, Complex.ofReal_im] at R1 R2
  rw [splitVw, splitVz, smul_add, smul_add]
  simp only [smul_eq_mul] at R1 R2 ⊢
  linear_combination R1 + R2

/-- **Schwarz reflection principle (real axis).** On a conjugation-symmetric open set `Ω`, if `f`
is continuous on the closed upper part, holomorphic on the open upper part, and real-valued on
the real axis of `Ω`, then the explicit reflection extension `schwarzReflection f` is holomorphic
on all of `Ω` — in particular across the real axis.

The gluing calculus (continuity everywhere, holomorphy off the axis, the conjugation symmetry) is
`Reflection/Basic.lean`; this theorem supplies the missing holomorphy at the axis via Morera's
theorem. -/
theorem differentiableOn_schwarzReflection_of_symmetric {Ω : Set ℂ}
    (hΩopen : IsOpen Ω) (hΩ : Set.MapsTo (starRingEnd ℂ) Ω Ω)
    (hcont : ContinuousOn f (Ω ∩ {z : ℂ | 0 ≤ z.im}))
    (hholo : DifferentiableOn ℂ f (Ω ∩ {z : ℂ | 0 < z.im}))
    (hreal : ∀ z ∈ Ω, z.im = 0 → (f z).im = 0) :
    DifferentiableOn ℂ (schwarzReflection f) Ω := by
  set F := schwarzReflection f with hF
  have hFcont : ContinuousOn F Ω :=
    continuousOn_schwarzReflection_of_symmetric hΩ hcont hreal
  have hFdiff : DifferentiableOn ℂ F (Ω ∩ {z : ℂ | z.im ≠ 0}) :=
    differentiableOn_schwarzReflection_inter_im_ne_zero_of_symmetric hΩ hholo
  refine (isConservativeOn_and_continuousOn_iff_isDifferentiableOn hΩopen).mp ⟨?_, hFcont⟩
  intro z w hsub
  rw [← add_eq_zero_iff_eq_neg, wedgeIntegral_add_wedgeIntegral_eq]
  by_cases hstr : (0 : ℝ) ∈ Set.Ioo (min z.im w.im) (max z.im w.im)
  · exact boundaryIntegral_eq_zero_of_straddling hFcont hFdiff hsub hstr
  · exact boundaryIntegral_eq_zero_off_axis hFcont hFdiff hsub hstr

/-- **Schwarz reflection principle**, packaged existential form (the L4 milestone of
`ConformalMapping/Suggested.lean`). On a conjugation-symmetric open `Ω`, a function continuous on
the closed upper part, holomorphic on the open upper part, and real on the real axis extends to a
function holomorphic on all of `Ω` that agrees with `f` on the closed upper part and satisfies the
reflection symmetry `F (conj z) = conj (F z)`. The explicit witness is `schwarzReflection f`. -/
theorem exists_differentiableOn_eqOn_conj_of_symmetric {Ω : Set ℂ}
    (hΩopen : IsOpen Ω) (hΩ : Set.MapsTo (starRingEnd ℂ) Ω Ω)
    (hcont : ContinuousOn f (Ω ∩ {z : ℂ | 0 ≤ z.im}))
    (hholo : DifferentiableOn ℂ f (Ω ∩ {z : ℂ | 0 < z.im}))
    (hreal : ∀ z ∈ Ω, z.im = 0 → (f z).im = 0) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F Ω ∧ Set.EqOn F f (Ω ∩ {z : ℂ | 0 ≤ z.im}) ∧
      ∀ z ∈ Ω, F ((starRingEnd ℂ) z) = (starRingEnd ℂ) (F z) := by
  refine ⟨schwarzReflection f, differentiableOn_schwarzReflection_of_symmetric hΩopen hΩ hcont
    hholo hreal, ?_, ?_⟩
  · exact eqOn_schwarzReflection_of_subset_im_nonneg fun _ hz => hz.2
  · exact fun z hz => schwarzReflection_conj_of_real_on_axis hreal hz

end TauCeti

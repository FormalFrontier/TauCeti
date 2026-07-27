/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap

/-!
# Painlevé removability across a line

A line is a removable set for *continuous* holomorphic functions: if `F` is continuous on an open
set `Ω ⊆ ℂ` and holomorphic on `Ω` off a line, then `F` is holomorphic on all of `Ω`. This is the
straight-line base case toward the L4 analytic-arc removability result in the conformal-mapping
roadmap (`ConformalMapping/README.md`); curved analytic arcs remain outside this module's scope.
It is the analytic content that makes the Schwarz reflection principle work, and it is what lets
two functions holomorphic on the two open sides of a line be glued along it as soon as the glued
function is continuous.

The proof is the classical Morera argument. By
`Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn`, holomorphy on an open set is
equivalent to continuity together with the vanishing of every rectangle-boundary integral
(`Complex.IsConservativeOn`). Continuity is a hypothesis; for the rectangle integrals we work with
the real axis and split each rectangle there into its part above and its part below. Each half is
bounded by the axis, so its *open interior* misses the axis entirely, where `F` is holomorphic;
Mathlib's continuous-on-closed Cauchy–Goursat lemma
`Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn` then makes each half's
boundary integral vanish, and the shared axis edge cancels when the two halves are recombined. An
arbitrary line is reduced to the real axis by the affine chart `w ↦ p + (q - p) * w`, which is a
biholomorphism of `ℂ` carrying `ℝ` onto the line through `p` and `q`.

In accordance with the conformal-mapping roadmap's generality bar, the results are stated for
scalar-valued functions `F : ℂ → ℂ`, even though the Morera argument and its Mathlib inputs also
support Banach-valued functions. The roadmap deliberately requires every theorem added in layers
L0–L6 to remain scalar; the Banach-valued generalization is therefore outside this module's scope.

## Main results

* `TauCeti.differentiableOn_of_continuousOn_of_differentiableOn_im_ne_zero`: removability of the
  real axis, the base case carrying the Morera argument.
* `TauCeti.differentiableOn_of_continuousOn_of_differentiableOn_of_im_pos_of_im_neg`: the gluing
  form — holomorphic above the axis, holomorphic below it, continuous across it, hence holomorphic.
* `TauCeti.differentiableOn_of_continuousOn_of_differentiableOn_diff_of_subset_range_lineMap`:
  removability of any subset of the line through two distinct points `p ≠ q`.
* `TauCeti.differentiableOn_of_continuousOn_of_differentiableOn_diff_im_eq` and
  `TauCeti.differentiableOn_of_continuousOn_of_differentiableOn_diff_re_eq`: the horizontal and
  vertical special cases `{z | z.im = c}` and `{z | z.re = c}`.

The Cauchy foundations consumed here are Mathlib's: the rectangle Cauchy–Goursat theorem
(`Analysis/Complex/CauchyIntegral.lean`) and the disc Morera theorem
(`Analysis/Complex/HasPrimitives.lean`). Layer L4 of the roadmap is absent from the upstream
Mathlib Riemann-mapping effort leanprover-community/mathlib4#33505, so this is new Lean
formalization rather than a shim; any shared foundational API should still be refactored onto
Mathlib's once that human-curated work lands.

## References

* Ahlfors, *Complex Analysis*, Chapter 4.6.
* Rudin, *Real and Complex Analysis*, Chapter 11.
-/

public section

namespace TauCeti

open Complex Set intervalIntegral MeasureTheory
open scoped Interval

variable {Ω : Set ℂ} {F : ℂ → ℂ}

/-- A rectangle whose open interior avoids the real axis has a vanishing boundary integral for
any function continuous on a domain `Ω` containing the (closed) rectangle and holomorphic on the
part of `Ω` off the real axis. This is the per-rectangle input to Morera's theorem; it is applied
both to axis-avoiding rectangles directly and to the two axis-bounded halves of a straddling
rectangle. -/
private lemma boundaryIntegral_eq_zero_off_axis
    (hcont : ContinuousOn F Ω) (hdiff : DifferentiableOn ℂ F (Ω ∩ {z : ℂ | z.im ≠ 0}))
    {z w : ℂ} (hsub : Complex.Rectangle z w ⊆ Ω)
    (haxis : (0 : ℝ) ∉ Set.Ioo (min z.im w.im) (max z.im w.im)) :
    ((∫ x : ℝ in z.re..w.re, F (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, F (x + w.im * I)) +
        I • (∫ y : ℝ in z.im..w.im, F (w.re + y * I)) -
        I • (∫ y : ℝ in z.im..w.im, F (z.re + y * I))) = 0 := by
  refine integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn F z w
    (hcont.mono hsub) (hdiff.mono fun p hp => ?_)
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
private lemma boundaryIntegral_eq_zero_of_edge_on_axis
    (hcont : ContinuousOn F Ω) (hdiff : DifferentiableOn ℂ F (Ω ∩ {z : ℂ | z.im ≠ 0}))
    {z w : ℂ} (hsub : Complex.Rectangle z w ⊆ Ω) (haxis : z.im = 0 ∨ w.im = 0) :
    ((∫ x : ℝ in z.re..w.re, F (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, F (x + w.im * I)) +
        I • (∫ y : ℝ in z.im..w.im, F (w.re + y * I)) -
        I • (∫ y : ℝ in z.im..w.im, F (z.re + y * I))) = 0 := by
  refine boundaryIntegral_eq_zero_off_axis hcont hdiff hsub fun hm => ?_
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
private lemma vertical_edge_split_at_zero
    (hcont : ContinuousOn F Ω) {z w : ℂ} (hsub : Complex.Rectangle z w ⊆ Ω)
    (h0mem : (0 : ℝ) ∈ [[z.im, w.im]]) {a : ℝ} (ha : a ∈ [[z.re, w.re]]) :
    (∫ y : ℝ in z.im..w.im, F (↑a + ↑y * I)) =
      (∫ y : ℝ in z.im..(0 : ℝ), F (↑a + ↑y * I)) +
        ∫ y : ℝ in (0 : ℝ)..w.im, F (↑a + ↑y * I) := by
  -- `F` is continuous along the edge, hence interval-integrable on the parts below and above `0`.
  have contV : ContinuousOn (fun t : ℝ => F (↑a + ↑t * I)) [[z.im, w.im]] :=
    hcont.comp (by fun_prop) fun t ht => hsub (by
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
private lemma boundaryIntegral_eq_zero_of_straddling
    (hcont : ContinuousOn F Ω) (hdiff : DifferentiableOn ℂ F (Ω ∩ {z : ℂ | z.im ≠ 0}))
    {z w : ℂ} (hsub : Complex.Rectangle z w ⊆ Ω)
    (hstr : (0 : ℝ) ∈ Set.Ioo (min z.im w.im) (max z.im w.im)) :
    ((∫ x : ℝ in z.re..w.re, F (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, F (x + w.im * I)) +
        I • (∫ y : ℝ in z.im..w.im, F (w.re + y * I)) -
        I • (∫ y : ℝ in z.im..w.im, F (z.re + y * I))) = 0 := by
  have h0mem : (0 : ℝ) ∈ [[z.im, w.im]] := by
    rw [← Icc_min_max]; exact Ioo_subset_Icc_self hstr
  -- Split each vertical edge at the axis into its part below and its part above.
  have splitVw := vertical_edge_split_at_zero hcont hsub h0mem right_mem_uIcc
  have splitVz := vertical_edge_split_at_zero hcont hsub h0mem left_mem_uIcc
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
  have R1 := boundaryIntegral_eq_zero_of_edge_on_axis hcont hdiff hsubR1
    (Or.inr (Complex.ofReal_im w.re))
  have R2 := boundaryIntegral_eq_zero_of_edge_on_axis hcont hdiff hsubR2
    (Or.inl (Complex.ofReal_im z.re))
  simp only [Complex.ofReal_re, Complex.ofReal_im] at R1 R2
  rw [splitVw, splitVz, smul_add, smul_add]
  simp only [smul_eq_mul] at R1 R2 ⊢
  linear_combination R1 + R2

/-- **Painlevé removability of the real axis.** A function continuous on an open set `Ω ⊆ ℂ` and
holomorphic on the part of `Ω` off the real axis is holomorphic on all of `Ω`.

This is the base case of removability across a line: an arbitrary line is reduced to it by an
affine change of variable in
`TauCeti.differentiableOn_of_continuousOn_of_differentiableOn_diff_of_subset_range_lineMap`. -/
theorem differentiableOn_of_continuousOn_of_differentiableOn_im_ne_zero
    (hΩ : IsOpen Ω) (hcont : ContinuousOn F Ω)
    (hdiff : DifferentiableOn ℂ F (Ω ∩ {z : ℂ | z.im ≠ 0})) :
    DifferentiableOn ℂ F Ω := by
  refine (isConservativeOn_and_continuousOn_iff_isDifferentiableOn hΩ).mp ⟨?_, hcont⟩
  intro z w hsub
  rw [← add_eq_zero_iff_eq_neg, wedgeIntegral_add_wedgeIntegral_eq]
  by_cases hstr : (0 : ℝ) ∈ Set.Ioo (min z.im w.im) (max z.im w.im)
  · exact boundaryIntegral_eq_zero_of_straddling hcont hdiff hsub hstr
  · exact boundaryIntegral_eq_zero_off_axis hcont hdiff hsub hstr

/-- **Gluing across the real axis.** A function on an open set `Ω ⊆ ℂ` that is holomorphic on the
open upper part and on the open lower part of `Ω`, and merely *continuous* on `Ω`, is holomorphic
on all of `Ω`. This is the form in which removability is used to glue two separately defined
holomorphic branches along the axis, as in the Schwarz reflection principle. -/
theorem differentiableOn_of_continuousOn_of_differentiableOn_of_im_pos_of_im_neg
    (hΩ : IsOpen Ω) (hcont : ContinuousOn F Ω)
    (hpos : DifferentiableOn ℂ F (Ω ∩ {z : ℂ | 0 < z.im}))
    (hneg : DifferentiableOn ℂ F (Ω ∩ {z : ℂ | z.im < 0})) :
    DifferentiableOn ℂ F Ω := by
  apply differentiableOn_of_continuousOn_of_differentiableOn_im_ne_zero hΩ hcont
  have hoffAxis :
      Ω ∩ {z : ℂ | z.im ≠ 0} =
        (Ω ∩ {z : ℂ | 0 < z.im}) ∪ (Ω ∩ {z : ℂ | z.im < 0}) := by
    ext z
    simp only [mem_inter_iff, mem_setOf_eq, mem_union]
    constructor
    · rintro ⟨hz, him⟩
      rcases lt_or_gt_of_ne him with h | h
      · exact Or.inr ⟨hz, h⟩
      · exact Or.inl ⟨hz, h⟩
    · rintro (⟨hz, h⟩ | ⟨hz, h⟩)
      · exact ⟨hz, ne_of_gt h⟩
      · exact ⟨hz, ne_of_lt h⟩
  rw [hoffAxis]
  exact hpos.union_of_isOpen hneg
    (hΩ.inter (isOpen_lt continuous_const Complex.continuous_im))
    (hΩ.inter (isOpen_lt Complex.continuous_im continuous_const))

/-- Membership in the line through two points, in the "base point plus real multiple of the
direction" form used by the affine chart below. -/
private lemma mem_range_lineMap_iff {p q z : ℂ} :
    z ∈ Set.range (AffineMap.lineMap (k := ℝ) p q) ↔ ∃ t : ℝ, z = p + t * (q - p) := by
  simp only [Set.mem_range, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
    Complex.real_smul, eq_comm (a := z)]
  exact exists_congr fun t => by rw [add_comm]

/-- **Painlevé removability across a line.** Let `p ≠ q` be points of `ℂ` and let `S` be any subset
of the line through them, such as the whole line or a segment. A function continuous on an open set
`Ω ⊆ ℂ` and holomorphic on `Ω \ S` is holomorphic on all of `Ω`.

The line is straightened to the real axis by the affine chart `w ↦ p + (q - p) * w`, a
biholomorphism of `ℂ` carrying `ℝ` onto it, reducing the statement to
`TauCeti.differentiableOn_of_continuousOn_of_differentiableOn_im_ne_zero`. -/
theorem differentiableOn_of_continuousOn_of_differentiableOn_diff_of_subset_range_lineMap
    {p q : ℂ} {S : Set ℂ}
    (hpq : p ≠ q) (hS : S ⊆ Set.range (AffineMap.lineMap (k := ℝ) p q))
    (hΩ : IsOpen Ω) (hcont : ContinuousOn F Ω) (hdiff : DifferentiableOn ℂ F (Ω \ S)) :
    DifferentiableOn ℂ F Ω := by
  have hd : q - p ≠ 0 := sub_ne_zero.mpr hpq.symm
  have hφdiff : Differentiable ℂ (fun w : ℂ => p + (q - p) * w) := by fun_prop
  have hψdiff : Differentiable ℂ (fun z : ℂ => (z - p) / (q - p)) :=
    (differentiable_id.sub_const p).div_const _
  -- `w ↦ p + (q - p) * w` is a biholomorphism of `ℂ`, with inverse `z ↦ (z - p) / (q - p)`.
  have hφinv : ∀ z : ℂ, p + (q - p) * ((z - p) / (q - p)) = z := fun z => by
    rw [mul_div_cancel₀ _ hd]; ring
  have hΩ'open : IsOpen ((fun w : ℂ => p + (q - p) * w) ⁻¹' Ω) := hΩ.preimage hφdiff.continuous
  -- Pulled back along the chart, the removable set is swallowed by the real axis.
  have key : DifferentiableOn ℂ (F ∘ fun w : ℂ => p + (q - p) * w)
      ((fun w : ℂ => p + (q - p) * w) ⁻¹' Ω) := by
    refine differentiableOn_of_continuousOn_of_differentiableOn_im_ne_zero hΩ'open
      (hcont.comp hφdiff.continuous.continuousOn fun w hw => hw) ?_
    refine hdiff.comp hφdiff.differentiableOn fun w hw => ⟨hw.1, fun hmem => hw.2 ?_⟩
    obtain ⟨t, ht⟩ := mem_range_lineMap_iff.mp (hS hmem)
    -- `p + (q - p) * w = p + t * (q - p)` forces `w = t`, hence `w.im = 0`.
    have hwt : (q - p) * w = (q - p) * (t : ℂ) := by linear_combination ht
    simp [mul_left_cancel₀ hd hwt]
  -- Transport back along the inverse chart.
  refine (key.comp hψdiff.differentiableOn fun z hz => ?_).congr fun z hz => ?_
  · simpa only [Set.mem_preimage, hφinv z] using hz
  · simp only [Function.comp_apply, hφinv z]

/-- **Painlevé removability across a horizontal line.** A function continuous on an open set
`Ω ⊆ ℂ` and holomorphic off the horizontal line `{z | z.im = c}` is holomorphic on all of `Ω`. -/
theorem differentiableOn_of_continuousOn_of_differentiableOn_diff_im_eq {c : ℝ}
    (hΩ : IsOpen Ω) (hcont : ContinuousOn F Ω)
    (hdiff : DifferentiableOn ℂ F (Ω \ {z : ℂ | z.im = c})) :
    DifferentiableOn ℂ F Ω := by
  refine differentiableOn_of_continuousOn_of_differentiableOn_diff_of_subset_range_lineMap
    (p := c * I) (q := 1 + c * I) (by simp) (fun z hz => ?_) hΩ hcont hdiff
  refine mem_range_lineMap_iff.mpr ⟨z.re, ?_⟩
  simp only [add_sub_cancel_right, mul_one]
  exact Complex.ext (by simp) (by simpa using hz)

/-- **Painlevé removability across a vertical line.** A function continuous on an open set
`Ω ⊆ ℂ` and holomorphic off the vertical line `{z | z.re = c}` is holomorphic on all of `Ω`. -/
theorem differentiableOn_of_continuousOn_of_differentiableOn_diff_re_eq {c : ℝ}
    (hΩ : IsOpen Ω) (hcont : ContinuousOn F Ω)
    (hdiff : DifferentiableOn ℂ F (Ω \ {z : ℂ | z.re = c})) :
    DifferentiableOn ℂ F Ω := by
  refine differentiableOn_of_continuousOn_of_differentiableOn_diff_of_subset_range_lineMap
    (p := (c : ℂ)) (q := (c : ℂ) + I) (by simp) (fun z hz => ?_) hΩ hcont hdiff
  refine mem_range_lineMap_iff.mpr ⟨z.im, ?_⟩
  simp only [add_sub_cancel_left]
  exact Complex.ext (by simpa using hz) (by simp)

end TauCeti

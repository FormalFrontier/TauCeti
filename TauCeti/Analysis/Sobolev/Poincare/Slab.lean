/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
-- `TauCeti.MeasureTheory.Function.Lp.LIntegralRpow` is imported publicly: every estimate below is
-- proved as a bound between `∫⁻ ‖·‖ₑ ^ p` integrals and converted by
-- `TauCeti.eLpNorm_le_eLpNorm_of_lintegral_rpow_le`, which a reader of either form will want.
public import TauCeti.MeasureTheory.Function.Lp.LIntegralRpow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The Poincaré inequality on a slab

This file proves the **Poincaré inequality** (also called the Friedrichs inequality) for `C¹`
functions supported in a slab: if `u` vanishes outside the slab
`{x | x i ∈ Set.Icc a b}` of width `b - a`, then

`‖u‖_p ≤ (b - a) * ‖Du‖_p`

for every exponent `1 ≤ p < ∞`. This is the PDE roadmap's Lane A, item 5, the estimate that
`W^{1,p}_0(Ω)` inherits by passing to the closure of `C_c^∞(Ω)`, and the coercivity input for the
energy method of Lane D.

The constant is `b - a` exactly: the hypothesis a bound of this shape needs is not that `Ω` be
bounded but only that it be **bounded in one direction**, and the constant depends on nothing
except the width of the slab containing the support — not on the dimension, not on `p`, and not
on the shape of the domain. `TauCeti.not_exists_eLpNorm_le_const_mul_eLpNorm_fderiv` shows that
some such hypothesis is genuinely needed: no constant works on the whole space.

The proof is the classical one-dimensional argument. Along the line through `x` in the direction
of the `i`-th coordinate the function starts at `0`, so the fundamental theorem of calculus gives
`‖u‖ ≤ ∫ ‖∂ᵢ u‖` over the width of the slab; Hölder's inequality — in the form of the nesting
`L^p ⊆ L^1` of the `Lᵖ` scale, `TauCeti.rpow_lintegral_le_measure_univ_rpow_mul` — turns
that into
`‖u‖^p ≤ (b - a)^{p-1} ∫ ‖∂ᵢ u‖^p`, and integrating in the remaining variables by Fubini gives
the result. See Evans, *Partial Differential Equations*, Section 5.6.

Since the estimate compares the function with a single partial derivative, the one-dimensional
statement `TauCeti.eLpNorm_le_eLpNorm_deriv_of_support_subset_Icc` is proved first for a
function on `ℝ` and is the whole analytic content; the `n`-dimensional statement is Fubini plus
the bound `‖Du x (eᵢ)‖ ≤ ‖Du x‖`.

## Main declarations

* `TauCeti.eLpNorm_le_eLpNorm_deriv_of_support_subset_Icc`: the one-dimensional inequality
  `‖g‖_p ≤ (b - a) ‖g'‖_p` for a `C¹` function on `ℝ` supported in `Set.Icc a b`.
* `TauCeti.eLpNorm_le_eLpNorm_fderiv_of_support_subset_slab`: the Poincaré inequality on
  `EuclideanSpace ℝ (Fin (n + 1))` for a `C¹` function supported in a slab of width `b - a`.
* `TauCeti.eLpNorm_le_eLpNorm_fderiv_of_support_subset_ball`: the form for a support inside a
  ball, with twice the radius as the constant.

The passage from a bound between the `∫⁻ ‖·‖ₑ ^ p` integrals to one between the `Lᵖ` seminorms is
generic measure theory and lives in `TauCeti.MeasureTheory.Function.Lp.LIntegralRpow`.
-/

public section

namespace TauCeti

open Filter MeasureTheory Set
open scoped ENNReal Topology

section OneDimensional

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {g g' : ℝ → F} {a b : ℝ}

omit [NormedSpace ℝ F] [CompleteSpace F] in
/-- A continuous function supported in `Set.Icc a b` vanishes at the left endpoint: approaching
`a` from the left it is identically zero. -/
private theorem eq_zero_of_support_subset_Icc (hg : Continuous g)
    (hsupp : Function.support g ⊆ Icc a b) : g a = 0 := by
  refine tendsto_nhds_unique (f := g) (l := 𝓝[<] a) hg.continuousAt.continuousWithinAt.tendsto ?_
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [self_mem_nhdsWithin] with t ht
  by_contra h
  exact absurd (hsupp (Function.mem_support.2 fun h' => h h'.symm)).1 (not_le.2 ht)

omit [NormedSpace ℝ F] [CompleteSpace F] in
/-- A function supported in the degenerate interval `Set.Icc a a` and vanishing at `a` vanishes
identically. -/
private theorem eq_zero_of_support_subset_Icc_self (hsupp : Function.support g ⊆ Icc a a)
    (hga : g a = 0) (t : ℝ) : g t = 0 := by
  by_cases h : g t = 0
  · exact h
  · have htm := hsupp (Function.mem_support.2 h)
    rw [le_antisymm htm.2 htm.1]
    exact hga

omit [NormedSpace ℝ F] [CompleteSpace F] in
/-- The support of `‖g ·‖ₑ ^ r` lies in the half-open interval `Set.Ioc a b`: the left endpoint
is excluded because `g` vanishes there. -/
private theorem support_enorm_rpow_subset_Ioc (hsupp : Function.support g ⊆ Icc a b)
    (hga : g a = 0) {r : ℝ} (hr0 : 0 < r) :
    Function.support (fun t => ‖g t‖ₑ ^ r) ⊆ Ioc a b := by
  intro t ht
  have hgt : g t ≠ 0 := fun h => ht (by simp [h, ENNReal.zero_rpow_of_pos hr0])
  have htm := hsupp (Function.mem_support.2 hgt)
  exact ⟨htm.1.lt_of_ne fun h => hgt (h ▸ hga), htm.2⟩

omit [CompleteSpace F] in
/-- **The fundamental theorem of calculus, in `∫⁻` form**: a function vanishing at `a` is bounded
throughout `Set.Icc a b` by its total variation `∫ ‖g'‖` over the interval.

Only `g a = 0` is used, not a support hypothesis, and the conclusion is pointwise in `t`; the
order `a ≤ b` is not assumed separately, being implied by `t ∈ Set.Icc a b`; and `F` need not be
complete. -/
private theorem enorm_le_lintegral_enorm_deriv
    (hg : ∀ t, HasDerivAt g (g' t) t) (hg' : Continuous g') (hga : g a = 0)
    {t : ℝ} (ht : t ∈ Icc a b) : ‖g t‖ₑ ≤ ∫⁻ s in Ioc a b, ‖g' s‖ₑ := by
  -- Completeness would only be needed for the fundamental theorem of calculus, and
  -- `enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc` passes to the completion itself.
  have hderiv : deriv g = g' := funext fun x => (hg x).deriv
  have hC1 : ContDiff ℝ 1 g :=
    contDiff_one_iff_deriv.2 ⟨fun x => (hg x).differentiableAt, hderiv ▸ hg'⟩
  calc ‖g t‖ₑ = ‖g t - g a‖ₑ := by rw [hga, sub_zero]
    _ ≤ ∫⁻ s in Icc a t, ‖deriv g s‖ₑ :=
        enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hC1.contDiffOn ht.1
    _ = ∫⁻ s in Ioc a t, ‖g' s‖ₑ := by rw [hderiv, setLIntegral_congr Ioc_ae_eq_Icc]
    _ ≤ ∫⁻ s in Ioc a b, ‖g' s‖ₑ := lintegral_mono_set (Ioc_subset_Ioc_right ht.2)

omit [CompleteSpace F] in
/-- **The one-dimensional Poincaré inequality**, in the `∫⁻` form the Fubini argument below
consumes: a `C¹` function on `ℝ` that vanishes outside `Set.Icc a b` satisfies
`∫ ‖g‖^r ≤ (b - a)^r ∫ ‖g'‖^r` for every `1 ≤ r`.

The two ingredients are the fundamental theorem of calculus, which bounds `‖g t‖` by the total
variation `∫ ‖g'‖` over the interval, and the nesting `L^r ⊆ L^1` of the `Lᵖ` scale on the
finite measure space `Set.Ioc a b`, which converts that `L^1` bound into an `L^r` one at the cost
of the factor `(b - a)^{r-1}`.

`F` need not be complete. -/
theorem lintegral_enorm_rpow_le_of_support_subset_Icc (hab : a ≤ b)
    (hg : ∀ t, HasDerivAt g (g' t) t) (hg' : Continuous g')
    (hsupp : Function.support g ⊆ Icc a b) {r : ℝ} (hr : 1 ≤ r) :
    ∫⁻ t, ‖g t‖ₑ ^ r ≤ ENNReal.ofReal ((b - a) ^ r) * ∫⁻ t, ‖g' t‖ₑ ^ r := by
  have hr0 : (0 : ℝ) < r := one_pos.trans_le hr
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun t => (hg t).continuousAt
  have hga : g a = 0 := eq_zero_of_support_subset_Icc hgc hsupp
  -- The degenerate slab carries no function at all.
  rcases hab.eq_or_lt with rfl | hab'
  · simp [eq_zero_of_support_subset_Icc_self hsupp hga, ENNReal.zero_rpow_of_pos hr0]
  have hba : (0 : ℝ) < b - a := sub_pos.2 hab'
  have hpow : ENNReal.ofReal (b - a) ^ (r - 1) * ENNReal.ofReal (b - a)
      = ENNReal.ofReal ((b - a) ^ r) := by
    nth_rewrite 2 [← ENNReal.rpow_one (ENNReal.ofReal (b - a))]
    have hsum : r - 1 + 1 = r := by ring
    rw [← ENNReal.rpow_add _ _ (by simpa using hba) ENNReal.ofReal_ne_top, hsum,
      ENNReal.ofReal_rpow_of_pos hba]
  calc ∫⁻ t, ‖g t‖ₑ ^ r
      = ∫⁻ t in Ioc a b, ‖g t‖ₑ ^ r :=
        (setLIntegral_eq_of_support_subset (support_enorm_rpow_subset_Ioc hsupp hga hr0)).symm
    _ ≤ ∫⁻ _ in Ioc a b, (∫⁻ s in Ioc a b, ‖g' s‖ₑ) ^ r := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact ENNReal.rpow_le_rpow
          (enorm_le_lintegral_enorm_deriv hg hg' hga (Ioc_subset_Icc_self ht)) hr0.le
    _ = (∫⁻ s in Ioc a b, ‖g' s‖ₑ) ^ r * ENNReal.ofReal (b - a) := by
        rw [setLIntegral_const, Real.volume_Ioc]
    _ ≤ (ENNReal.ofReal (b - a) ^ (r - 1) * ∫⁻ s in Ioc a b, ‖g' s‖ₑ ^ r) *
          ENNReal.ofReal (b - a) := by
        gcongr
        have hmu : (volume.restrict (Ioc a b)) Set.univ = ENNReal.ofReal (b - a) := by
          rw [Measure.restrict_apply_univ, Real.volume_Ioc]
        simpa only [hmu] using rpow_lintegral_le_measure_univ_rpow_mul
          (μ := volume.restrict (Ioc a b)) hg'.enorm.measurable.aemeasurable hr
    _ = ENNReal.ofReal ((b - a) ^ r) * ∫⁻ s in Ioc a b, ‖g' s‖ₑ ^ r := by
        rw [mul_right_comm, hpow]
    _ ≤ ENNReal.ofReal ((b - a) ^ r) * ∫⁻ t, ‖g' t‖ₑ ^ r :=
        mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)

omit [CompleteSpace F] in
/-- **The one-dimensional Poincaré inequality**: a `C¹` function on `ℝ` supported in an interval
of length `b - a` obeys `‖g‖_p ≤ (b - a) ‖g'‖_p` for every `1 ≤ p < ∞`.

The interval hypothesis is essential; `TauCeti.not_exists_eLpNorm_le_const_mul_eLpNorm_fderiv`
shows no such bound holds uniformly over all compactly supported functions. -/
theorem eLpNorm_le_eLpNorm_deriv_of_support_subset_Icc (hab : a ≤ b)
    (hg : ∀ t, HasDerivAt g (g' t) t) (hg' : Continuous g')
    (hsupp : Function.support g ⊆ Icc a b) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) :
    eLpNorm g p volume ≤ ENNReal.ofReal (b - a) * eLpNorm g' p volume :=
  eLpNorm_le_eLpNorm_of_lintegral_rpow_le (sub_nonneg.2 hab) (zero_lt_one.trans_le hp).ne' hp'
    (lintegral_enorm_rpow_le_of_support_subset_Icc hab hg hg' hsupp
      (by simpa using ENNReal.toReal_mono hp' hp))

end OneDimensional

section Slab

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {n : ℕ} {u : EuclideanSpace ℝ (Fin (n + 1)) → F} {i : Fin (n + 1)} {a b : ℝ}

/-- The parametrization of `ℝ^{n+1}` that isolates the `i`-th coordinate: the point with `i`-th
coordinate `t` and remaining coordinates `y`. -/
private def slabChart (i : Fin (n + 1)) (z : ℝ × (Fin n → ℝ)) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (i.insertNth z.1 z.2)

@[simp]
private theorem slabChart_apply_same (z : ℝ × (Fin n → ℝ)) : slabChart i z i = z.1 := by
  simp [slabChart]

/-- Read along its first argument, `slabChart` is the straight line through the point with `i`-th
coordinate `0` and remaining coordinates `y`, in the direction of the `i`-th basis vector. -/
private theorem slabChart_eq_add_smul_single (y : Fin n → ℝ) (t : ℝ) :
    slabChart i (t, y) =
      WithLp.toLp 2 (i.insertNth (0 : ℝ) y) + t • EuclideanSpace.single i (1 : ℝ) := by
  have hpi : i.insertNth t y = i.insertNth (0 : ℝ) y + t • Pi.single i (1 : ℝ) := by
    funext j
    refine Fin.succAboveCases i ?_ ?_ j <;> simp
  simp [slabChart, hpi]

/-- Isolating one coordinate turns the Lebesgue measure of `ℝ^{n+1}` into a product measure. -/
private theorem measurePreserving_slabChart :
    MeasurePreserving (slabChart i) (volume.prod volume) volume := by
  have h1 : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm
      ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)))
      (volume : Measure (Fin (n + 1) → ℝ)) := by
    simpa [volume_pi] using
      (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => (volume : Measure ℝ)) i).symm
  exact (PiLp.volume_preserving_toLp (Fin (n + 1))).comp h1

/-- Fubini's theorem in the coordinates supplied by `slabChart`. -/
private theorem lintegral_eq_lintegral_slabChart {w : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞}
    (hw : Measurable w) : ∫⁻ x, w x = ∫⁻ y, ∫⁻ t, w (slabChart i (t, y)) := by
  rw [← (measurePreserving_slabChart (i := i)).lintegral_comp hw]
  exact lintegral_prod_symm (fun z => w (slabChart i z))
    (hw.comp (measurePreserving_slabChart (i := i)).measurable).aemeasurable

omit [CompleteSpace F] in
/-- Along the line `t ↦ slabChart i (t, y)`, the function `u` has derivative the directional
derivative of `u` in the `i`-th coordinate direction. Only differentiability at the single point
of the line is needed. -/
private theorem hasDerivAt_comp_slabChart (y : Fin n → ℝ) {t : ℝ}
    (hu : DifferentiableAt ℝ u (slabChart i (t, y))) :
    HasDerivAt (fun s => u (slabChart i (s, y)))
      (fderiv ℝ u (slabChart i (t, y)) (EuclideanSpace.single i 1)) t := by
  have hl : HasDerivAt (fun s : ℝ => slabChart i (s, y)) (EuclideanSpace.single i 1) t := by
    simp only [slabChart_eq_add_smul_single]
    have hid : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
    simpa using _root_.HasDerivAt.const_add (WithLp.toLp 2 (i.insertNth (0 : ℝ) y))
      (_root_.HasDerivAt.smul_const hid (EuclideanSpace.single i (1 : ℝ)))
  exact hu.hasFDerivAt.comp_hasDerivAt t hl

omit [CompleteSpace F] in
/-- The one-dimensional estimate on a single line of the slab: the `r`-th power integral of `u`
along the line is at most `(b - a) ^ r` times that of the full derivative. Everything is asked of
the restricted line only: differentiability of `u` along it, continuity of the *directional*
derivative along it, and the support of the restriction. -/
private theorem lintegral_enorm_rpow_comp_slabChart_le {y : Fin n → ℝ}
    (hu : ∀ t : ℝ, DifferentiableAt ℝ u (slabChart i (t, y)))
    (hfc : Continuous fun t : ℝ => fderiv ℝ u (slabChart i (t, y)) (EuclideanSpace.single i 1))
    (hab : a ≤ b) (hsupp : Function.support (fun t : ℝ => u (slabChart i (t, y))) ⊆ Icc a b)
    {r : ℝ} (hr : 1 ≤ r) :
    ∫⁻ t, ‖u (slabChart i (t, y))‖ₑ ^ r
      ≤ ENNReal.ofReal ((b - a) ^ r) * ∫⁻ t, ‖fderiv ℝ u (slabChart i (t, y))‖ₑ ^ r := by
  refine le_trans (lintegral_enorm_rpow_le_of_support_subset_Icc hab
    (fun t => hasDerivAt_comp_slabChart y (hu t)) hfc hsupp hr) ?_
  gcongr with t
  rw [← ofReal_norm, ← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ?_
  simpa using (fderiv ℝ u (slabChart i (t, y))).le_opNorm (EuclideanSpace.single i 1)

omit [CompleteSpace F] in
/-- **The Poincaré inequality on a slab.** A `C¹` function on `ℝ^{n+1}` that vanishes outside
the slab `{x | x i ∈ Set.Icc a b}` satisfies `‖u‖_p ≤ (b - a) ‖Du‖_p` for every `1 ≤ p < ∞`.

Only the width of the slab enters the constant: neither the dimension nor the exponent nor the
shape of the region where `u` lives has any effect. In particular that region need not be
bounded — being trapped between two parallel hyperplanes is enough — and the hypothesis cannot
be dropped, by `TauCeti.not_exists_eLpNorm_le_const_mul_eLpNorm_fderiv`.

This is the estimate that passes to `W^{1,p}_0(Ω)` by density of `C_c^∞(Ω)`, for any `Ω`
contained in such a slab. -/
theorem eLpNorm_le_eLpNorm_fderiv_of_support_subset_slab (hu : ContDiff ℝ 1 u) (hab : a ≤ b)
    (hsupp : ∀ x ∈ Function.support u, x i ∈ Icc a b) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) :
    eLpNorm u p volume ≤ ENNReal.ofReal (b - a) * eLpNorm (fderiv ℝ u) p volume := by
  have hr : 1 ≤ p.toReal := by simpa using ENNReal.toReal_mono hp' hp
  have hfc : Continuous (fderiv ℝ u) := hu.continuous_fderiv one_ne_zero
  refine eLpNorm_le_eLpNorm_of_lintegral_rpow_le (sub_nonneg.2 hab)
    (zero_lt_one.trans_le hp).ne' hp' ?_
  set r := p.toReal
  have hmu : Measurable fun x : EuclideanSpace ℝ (Fin (n + 1)) => ‖u x‖ₑ ^ r :=
    (ENNReal.continuous_rpow_const.comp hu.continuous.enorm).measurable
  have hmf : Measurable fun x : EuclideanSpace ℝ (Fin (n + 1)) => ‖fderiv ℝ u x‖ₑ ^ r :=
    (ENNReal.continuous_rpow_const.comp hfc.enorm).measurable
  have hline : ∀ y : Fin n → ℝ, ∫⁻ t, ‖u (slabChart i (t, y))‖ₑ ^ r
      ≤ ENNReal.ofReal ((b - a) ^ r) * ∫⁻ t, ‖fderiv ℝ u (slabChart i (t, y))‖ₑ ^ r := fun y =>
    lintegral_enorm_rpow_comp_slabChart_le
      (fun _ => (hu.differentiable one_ne_zero).differentiableAt)
      (((hfc.comp (by simp only [slabChart_eq_add_smul_single]; fun_prop)).clm_apply
        continuous_const)) hab
      (fun t ht => by simpa using hsupp _ (Function.mem_support.2 ht)) hr
  calc ∫⁻ x, ‖u x‖ₑ ^ r
      = ∫⁻ y, ∫⁻ t, ‖u (slabChart i (t, y))‖ₑ ^ r := lintegral_eq_lintegral_slabChart hmu
    _ ≤ ∫⁻ y, ENNReal.ofReal ((b - a) ^ r) * ∫⁻ t, ‖fderiv ℝ u (slabChart i (t, y))‖ₑ ^ r :=
        lintegral_mono hline
    _ = ENNReal.ofReal ((b - a) ^ r) *
          ∫⁻ y, ∫⁻ t, ‖fderiv ℝ u (slabChart i (t, y))‖ₑ ^ r :=
        lintegral_const_mul' _ _ (by finiteness)
    _ = ENNReal.ofReal ((b - a) ^ r) * ∫⁻ x, ‖fderiv ℝ u x‖ₑ ^ r := by
        rw [lintegral_eq_lintegral_slabChart hmf]

omit [CompleteSpace F] in
/-- Membership in a Euclidean ball bounds every coordinate by the corresponding slab. -/
theorem apply_mem_Icc_of_mem_ball {c x : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ}
    (hx : x ∈ Metric.ball c R) (i : Fin (n + 1)) : x i ∈ Icc (c i - R) (c i + R) := by
  have hnorm : ‖x - c‖ < R := by simpa only [Metric.mem_ball, dist_eq_norm] using hx
  have hi := (PiLp.norm_apply_le (x - c) i).trans hnorm.le
  rw [Real.norm_eq_abs, WithLp.ofLp_sub, Pi.sub_apply, abs_le] at hi
  constructor <;> linarith

omit [CompleteSpace F] in
/-- **The Poincaré inequality on a ball.** A `C¹` function on `ℝ^{n+1}` supported in a ball of
radius `R` satisfies `‖u‖_p ≤ 2R ‖Du‖_p` for every `1 ≤ p < ∞`.

This is the shape the estimate takes on a bounded domain: any `Ω ⊆ Metric.ball c R` sits inside a
slab of width `2R`, so the constant may be taken to be twice the radius. It is not the optimal
constant — for the ball the sharp one is smaller — but it is explicit and depends on nothing but
`R`, as the roadmap asks. -/
theorem eLpNorm_le_eLpNorm_fderiv_of_support_subset_ball
    {c : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ} (hu : ContDiff ℝ 1 u)
    (hsupp : Function.support u ⊆ Metric.ball c R) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) :
    eLpNorm u p volume ≤ ENNReal.ofReal (2 * R) * eLpNorm (fderiv ℝ u) p volume := by
  rcases le_or_gt R 0 with hR | hR
  · rw [Metric.ball_eq_empty.2 hR, subset_empty_iff, Function.support_eq_empty_iff] at hsupp
    simp [hsupp]
  have hslab : ∀ x ∈ Function.support u,
      x (0 : Fin (n + 1)) ∈ Icc (c 0 - R) (c 0 + R) :=
    fun x hx => apply_mem_Icc_of_mem_ball (hsupp hx) 0
  have hwidth : (c 0 + R) - (c 0 - R) = 2 * R := by ring
  simpa [hwidth] using
    eLpNorm_le_eLpNorm_fderiv_of_support_subset_slab hu
      (by linarith : c 0 - R ≤ c 0 + R) hslab hp hp'

end Slab

end TauCeti

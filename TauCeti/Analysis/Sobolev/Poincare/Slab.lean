/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
-- `TauCeti.MeasureTheory.Function.Lp.LIntegralRpow` is imported publicly: every estimate below is
-- proved as a bound between `∫⁻ ‖·‖ₑ ^ p` integrals and converted by
-- `TauCeti.eLpNorm_le_eLpNorm_of_lintegral_rpow_le`, which a reader of either form will want.
public import TauCeti.MeasureTheory.Function.Lp.LIntegralRpow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
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
`L^p ⊆ L^1` of the `Lᵖ` scale on a finite measure space,
`MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ` — turns that into
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

/-- **The one-dimensional Poincaré inequality**, in the `∫⁻` form the Fubini argument below
consumes: a `C¹` function on `ℝ` that vanishes outside `Set.Icc a b` satisfies
`∫ ‖g‖^r ≤ (b - a)^r ∫ ‖g'‖^r` for every `1 ≤ r`.

The two ingredients are the fundamental theorem of calculus, which bounds `‖g t‖` by the total
variation `∫ ‖g'‖` over the interval, and the nesting `L^r ⊆ L^1` of the `Lᵖ` scale on the
finite measure space `Set.Ioc a b`, which converts that `L^1` bound into an `L^r` one at the cost
of the factor `(b - a)^{r-1}`. -/
theorem lintegral_enorm_rpow_le_of_support_subset_Icc (hab : a ≤ b)
    (hg : ∀ t, HasDerivAt g (g' t) t) (hg' : Continuous g')
    (hsupp : Function.support g ⊆ Icc a b) {r : ℝ} (hr : 1 ≤ r) :
    ∫⁻ t, ‖g t‖ₑ ^ r ≤ ENNReal.ofReal ((b - a) ^ r) * ∫⁻ t, ‖g' t‖ₑ ^ r := by
  have hr0 : (0 : ℝ) < r := one_pos.trans_le hr
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun t => (hg t).continuousAt
  have hga : g a = 0 := eq_zero_of_support_subset_Icc hgc hsupp
  -- The degenerate slab carries no function at all.
  rcases hab.eq_or_lt with rfl | hab'
  · have hgz : ∀ t, g t = 0 := by
      intro t
      by_cases h : g t = 0
      · exact h
      · have htm := hsupp (Function.mem_support.2 h)
        rw [le_antisymm htm.2 htm.1]
        exact hga
    simp [hgz, ENNReal.zero_rpow_of_pos hr0]
  have hba : (0 : ℝ) < b - a := sub_pos.2 hab'
  set C : ℝ≥0∞ := ∫⁻ s in Ioc a b, ‖g' s‖ₑ with hCdef
  -- Step 1: the fundamental theorem of calculus bounds `g` by the total variation of `g'`.
  have hkey : ∀ t ∈ Icc a b, ‖g t‖ₑ ≤ C := by
    intro t ht
    have h1 : ∫ s in a..t, g' s = g t - g a :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hg s) (hg'.intervalIntegrable a t)
    have h2 : ‖g t‖ ≤ ∫ s in a..t, ‖g' s‖ := by
      have hgt : g t = ∫ s in a..t, g' s := by rw [h1, hga, sub_zero]
      rw [hgt]
      exact intervalIntegral.norm_integral_le_integral_norm ht.1
    have h3 : ∫ s in a..t, ‖g' s‖ ≤ ∫ s in a..b, ‖g' s‖ :=
      intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
        (.of_forall fun s => norm_nonneg _) (hg'.norm.intervalIntegrable a b)
    calc ‖g t‖ₑ = ENNReal.ofReal ‖g t‖ := (ofReal_norm _).symm
      _ ≤ ENNReal.ofReal (∫ s in a..b, ‖g' s‖) := ENNReal.ofReal_le_ofReal (h2.trans h3)
      _ = C := by
          rw [intervalIntegral.integral_of_le hab, hCdef]
          exact ofReal_integral_norm_eq_lintegral_enorm (hg'.integrableOn_Ioc)
  -- Step 2: Hölder, as the inclusion `L^r (Ioc a b) ⊆ L^1 (Ioc a b)`.
  have hvol : (volume.restrict (Ioc a b)) univ = ENNReal.ofReal (b - a) := by
    rw [Measure.restrict_apply_univ, Real.volume_Ioc]
  have hCr : eLpNorm g' (ENNReal.ofReal r) (volume.restrict (Ioc a b))
      = (∫⁻ s in Ioc a b, ‖g' s‖ₑ ^ r) ^ (1 / r) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hr0) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hr0.le]
  have holder : C ≤ (∫⁻ s in Ioc a b, ‖g' s‖ₑ ^ r) ^ (1 / r) *
      ENNReal.ofReal (b - a) ^ (1 - 1 / r) := by
    have hle : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hr
    have := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (f := g')
      (μ := volume.restrict (Ioc a b)) hle hg'.aestronglyMeasurable
    rwa [eLpNorm_one_eq_lintegral_enorm, ← hCdef, hCr, hvol, ENNReal.toReal_one,
      ENNReal.toReal_ofReal hr0.le, div_one] at this
  have holder' : C ^ r ≤ ENNReal.ofReal (b - a) ^ (r - 1) * ∫⁻ s in Ioc a b, ‖g' s‖ₑ ^ r := by
    have hexp : (1 - r⁻¹) * r = r - 1 := by field_simp
    calc C ^ r
        ≤ ((∫⁻ s in Ioc a b, ‖g' s‖ₑ ^ r) ^ (1 / r) * ENNReal.ofReal (b - a) ^ (1 - 1 / r)) ^ r :=
          ENNReal.rpow_le_rpow holder hr0.le
      _ = _ := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hr0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
            one_div, inv_mul_cancel₀ hr0.ne', ENNReal.rpow_one, hexp, mul_comm]
  -- Step 3: integrate the pointwise bound over the slab.
  have hpow : ENNReal.ofReal (b - a) ^ (r - 1) * ENNReal.ofReal (b - a)
      = ENNReal.ofReal ((b - a) ^ r) := by
    have hsum : r - 1 + 1 = r := by ring
    nth_rewrite 2 [← ENNReal.rpow_one (ENNReal.ofReal (b - a))]
    rw [← ENNReal.rpow_add _ _ (by simpa using hba) ENNReal.ofReal_ne_top, hsum,
      ENNReal.ofReal_rpow_of_pos hba]
  have hsupp' : Function.support (fun t => ‖g t‖ₑ ^ r) ⊆ Ioc a b := by
    intro t ht
    have hgt : g t ≠ 0 := by
      intro h
      exact ht (by simp [h, ENNReal.zero_rpow_of_pos hr0])
    have htm := hsupp (Function.mem_support.2 hgt)
    exact ⟨htm.1.lt_of_ne fun h => hgt (h ▸ hga), htm.2⟩
  calc ∫⁻ t, ‖g t‖ₑ ^ r
      = ∫⁻ t in Ioc a b, ‖g t‖ₑ ^ r := by
        rw [← lintegral_indicator measurableSet_Ioc, Set.indicator_eq_self.2 hsupp']
    _ ≤ ∫⁻ _ in Ioc a b, C ^ r := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact ENNReal.rpow_le_rpow (hkey t (Ioc_subset_Icc_self ht)) hr0.le
    _ = C ^ r * ENNReal.ofReal (b - a) := by rw [setLIntegral_const, Real.volume_Ioc]
    _ ≤ (ENNReal.ofReal (b - a) ^ (r - 1) * ∫⁻ s in Ioc a b, ‖g' s‖ₑ ^ r) *
          ENNReal.ofReal (b - a) := by gcongr
    _ = ENNReal.ofReal ((b - a) ^ r) * ∫⁻ s in Ioc a b, ‖g' s‖ₑ ^ r := by
        rw [mul_right_comm, hpow]
    _ ≤ ENNReal.ofReal ((b - a) ^ r) * ∫⁻ t, ‖g' t‖ₑ ^ r :=
        mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)

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
  -- Restricted to a line in the `i`-th coordinate direction, `u` is a `C¹` function of one
  -- variable supported in `Set.Icc a b`.
  have hlinecont : ∀ y : Fin n → ℝ, Continuous fun t : ℝ => slabChart i (t, y) := by
    intro y
    simp only [slabChart_eq_add_smul_single]
    fun_prop
  have hderiv : ∀ (y : Fin n → ℝ) (t : ℝ),
      HasDerivAt (fun s => u (slabChart i (s, y)))
        (fderiv ℝ u (slabChart i (t, y)) (EuclideanSpace.single i 1)) t := by
    intro y t
    have hl : HasDerivAt (fun s : ℝ => slabChart i (s, y)) (EuclideanSpace.single i 1) t := by
      simp only [slabChart_eq_add_smul_single]
      have hid : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
      simpa using _root_.HasDerivAt.const_add (WithLp.toLp 2 (i.insertNth (0 : ℝ) y))
        (_root_.HasDerivAt.smul_const hid (EuclideanSpace.single i (1 : ℝ)))
    exact (hu.differentiable one_ne_zero).differentiableAt.hasFDerivAt.comp_hasDerivAt t hl
  have hcont : ∀ y : Fin n → ℝ,
      Continuous fun t => fderiv ℝ u (slabChart i (t, y)) (EuclideanSpace.single i 1) :=
    fun y => (hfc.comp (hlinecont y)).clm_apply continuous_const
  have hsuppline : ∀ y : Fin n → ℝ,
      Function.support (fun t => u (slabChart i (t, y))) ⊆ Icc a b := by
    intro y t ht
    simpa using hsupp _ (Function.mem_support.2 ht)
  have hmu : Measurable fun x : EuclideanSpace ℝ (Fin (n + 1)) => ‖u x‖ₑ ^ r :=
    (ENNReal.continuous_rpow_const.comp hu.continuous.enorm).measurable
  have hmf : Measurable fun x : EuclideanSpace ℝ (Fin (n + 1)) => ‖fderiv ℝ u x‖ₑ ^ r :=
    (ENNReal.continuous_rpow_const.comp hfc.enorm).measurable
  calc ∫⁻ x, ‖u x‖ₑ ^ r
      = ∫⁻ y, ∫⁻ t, ‖u (slabChart i (t, y))‖ₑ ^ r := lintegral_eq_lintegral_slabChart hmu
    _ ≤ ∫⁻ y, ENNReal.ofReal ((b - a) ^ r) *
          ∫⁻ t, ‖fderiv ℝ u (slabChart i (t, y)) (EuclideanSpace.single i 1)‖ₑ ^ r :=
        lintegral_mono fun y => lintegral_enorm_rpow_le_of_support_subset_Icc hab (hderiv y)
          (hcont y) (hsuppline y) hr
    _ ≤ ∫⁻ y, ENNReal.ofReal ((b - a) ^ r) * ∫⁻ t, ‖fderiv ℝ u (slabChart i (t, y))‖ₑ ^ r := by
        refine lintegral_mono fun y => ?_
        gcongr with t
        rw [← ofReal_norm, ← ofReal_norm]
        refine ENNReal.ofReal_le_ofReal ?_
        simpa using (fderiv ℝ u (slabChart i (t, y))).le_opNorm (EuclideanSpace.single i 1)
    _ = ENNReal.ofReal ((b - a) ^ r) *
          ∫⁻ y, ∫⁻ t, ‖fderiv ℝ u (slabChart i (t, y))‖ₑ ^ r :=
        lintegral_const_mul' _ _ (by finiteness)
    _ = ENNReal.ofReal ((b - a) ^ r) * ∫⁻ x, ‖fderiv ℝ u x‖ₑ ^ r := by
        rw [lintegral_eq_lintegral_slabChart hmf]

/-- **The Poincaré inequality on a ball.** A `C¹` function on `ℝ^{n+1}` supported in the ball of
radius `R` about the origin satisfies `‖u‖_p ≤ 2R ‖Du‖_p` for every `1 ≤ p < ∞`.

This is the shape the estimate takes on a bounded domain: any `Ω ⊆ Metric.ball 0 R` sits inside
a slab of width `2R`, so the constant may be taken to be twice the radius. It is not the optimal
constant — for the ball the sharp one is smaller — but it is explicit and depends on nothing but
`R`, as the roadmap asks. -/
theorem eLpNorm_le_eLpNorm_fderiv_of_support_subset_ball {R : ℝ} (hu : ContDiff ℝ 1 u)
    (hsupp : Function.support u ⊆ Metric.ball 0 R) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) :
    eLpNorm u p volume ≤ ENNReal.ofReal (2 * R) * eLpNorm (fderiv ℝ u) p volume := by
  rcases le_or_gt R 0 with hR | hR
  · rw [Metric.ball_eq_empty.2 hR, subset_empty_iff, Function.support_eq_empty_iff] at hsupp
    simp [hsupp]
  have hslab : ∀ x ∈ Function.support u, x (0 : Fin (n + 1)) ∈ Icc (-R) R := by
    intro x hx
    have hx' : ‖x‖ < R := by simpa using hsupp hx
    have := (PiLp.norm_apply_le x (0 : Fin (n + 1))).trans hx'.le
    rw [Real.norm_eq_abs, abs_le] at this
    exact this
  have hwidth : R - -R = 2 * R := by ring
  simpa [hwidth] using
    eLpNorm_le_eLpNorm_fderiv_of_support_subset_slab hu (by linarith : (-R : ℝ) ≤ R) hslab hp hp'

end Slab

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Zero
public import TauCeti.MeasureTheory.Function.Lp.LIntegralRpow
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The `Lᵖ` translation estimate

This file proves the **translation estimate** for Sobolev functions: for `1 ≤ p < ∞` and a vector
`h`,

`‖u(· + h) - u‖_p ≤ ‖h‖ ‖∇u‖_p`.

It is the quantitative form of the continuity of translation in `Lᵖ`, with a modulus that is
linear in `‖h‖` and controlled by one Sobolev seminorm.  Together with the extension of a
`W^{1,p}_0(Ω)` function by zero, it supplies the *uniform smallness of translations* hypothesis of
the Fréchet--Kolmogorov compactness criterion, and so is the analytic input for
Rellich--Kondrachov, Lane A.6 of `TauCetiRoadmap/PDE/README.md`.

## The estimate for a `C¹` function

`TauCeti.eLpNorm_sub_comp_add_le` is the estimate for a `C¹` function, and carries no support,
integrability or boundedness hypothesis: the derivative not being `Lᵖ` makes the right-hand side
infinite, not the statement false.  The proof is the classical one.  Along the segment from `x`
to `x + h` the fundamental theorem of calculus gives

`‖u(x + h) - u(x)‖ ≤ ∫_0^1 ‖Du(x + th) h‖ dt ≤ ‖h‖ ∫_0^1 ‖Du(x + th)‖ dt`,

and since the segment is parametrized by a *probability* space, raising this to the power `p`
costs nothing: the `L¹`-versus-`Lᵖ` factor of
`TauCeti.rpow_lintegral_le_measure_univ_rpow_mul` is the total mass, here `1`.  Integrating in
`x` and exchanging the order of integration reduces the inner integral to `∫ ‖Du(x + th)‖^p dx`,
which is independent of `t` because the measure is translation invariant.  That is where the
Haar hypothesis enters, and it is the only place it does.

## The estimate on `W^{1,p}_0(ℝⁿ)`

`TauCeti.W1p.eLpNorm_sub_comp_add_value_le` transports the estimate to the Sobolev space by
density: the set of jets satisfying it is closed — the translation increment is a continuous
function of the `Lᵖ` class, being the difference of the identity and the isometry induced by a
measure-preserving map — and it contains every test-function jet, so
`TauCeti.w1p0Submodule_subset_of_isClosed` gives it on all of `W^{1,p}_0(ℝⁿ)`.  Note that the
whole space is where a translation estimate can be stated without further data: translating a
function defined on a proper open `Ω` moves it off `Ω`, so the general case is this statement
composed with an extension of `W^{1,p}_0(Ω)` by zero.

Neither statement holds on `W^{1,p}(Ω)` in place of `W^{1,p}_0(Ω)` for a proper `Ω`, since the
zero-extension of a general Sobolev function on `Ω` need not be weakly differentiable across
`∂Ω` at all; the boundary condition is what is doing the work.

## Main declarations

* `TauCeti.enorm_sub_le_lintegral_enorm_fderiv_apply`: the fundamental theorem of calculus along
  the segment from `x` to `x + h`.
* `TauCeti.eLpNorm_sub_comp_add_le`: the translation estimate for a `C¹` function.
* `TauCeti.tendsto_eLpNorm_sub_comp_add`: continuity of translation in `Lᵖ` for a `C¹` function
  with `Lᵖ` derivative.
* `TauCeti.W1p.eLpNorm_sub_comp_add_value_le`: the translation estimate on `W^{1,p}_0(ℝⁿ)`.
* `TauCeti.W1p.tendsto_eLpNorm_sub_comp_add_value`: continuity of translation in `Lᵖ` on
  `W^{1,p}_0(ℝⁿ)`.

## References

Lane A.6 of `TauCetiRoadmap/PDE/README.md`; H. Brezis, *Functional Analysis, Sobolev Spaces and
Partial Differential Equations*, Proposition 9.3, for the estimate, and Theorem 4.26 for the
Fréchet--Kolmogorov criterion it feeds; L. C. Evans, *Partial Differential Equations*,
Chapter 5, for the difference-quotient form of the same bound.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal Gradient InnerProductSpace

section Calculus

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {u : E → F}

/-- Along the segment `s ↦ x + s • h` a `C¹` function has derivative the directional derivative
of `u` in the direction `h`. -/
private theorem hasDerivAt_comp_segment (hu : ContDiff ℝ 1 u) (x h : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => u (x + s • h)) (fderiv ℝ u (x + t • h) h) t := by
  have hl : HasDerivAt (fun s : ℝ => x + s • h) h t := by
    simpa using ((hasDerivAt_id t).smul_const h).const_add x
  exact ((hu.differentiable one_ne_zero) _).hasFDerivAt.comp_hasDerivAt t hl

/-- **The fundamental theorem of calculus along a segment**: the increment of a `C¹` function
between `x` and `x + h` is at most the total variation of its directional derivative in the
direction `h` along the segment joining the two points. -/
theorem enorm_sub_le_lintegral_enorm_fderiv_apply (hu : ContDiff ℝ 1 u) (x h : E) :
    ‖u (x + h) - u x‖ₑ ≤ ∫⁻ t in Icc (0 : ℝ) 1, ‖fderiv ℝ u (x + t • h) h‖ₑ := by
  have hderiv : deriv (fun s : ℝ => u (x + s • h)) = fun t => fderiv ℝ u (x + t • h) h :=
    funext fun t => (hasDerivAt_comp_segment hu x h t).deriv
  have hC1 : ContDiff ℝ 1 fun s : ℝ => u (x + s • h) :=
    hu.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have h01 := enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc
    (f := fun s : ℝ => u (x + s • h)) hC1.contDiffOn zero_le_one
  rw [hderiv] at h01
  simpa using h01

/-- The `r`-th power of the segment estimate.  Raising to the power `r ≥ 1` costs nothing because
the segment is parametrized by the *probability* space `Set.Icc 0 1`, so the `Lʳ`-versus-`L¹`
factor is `1`; the operator norm then splits off `‖h‖ ^ r`. -/
private theorem enorm_sub_rpow_le (hu : ContDiff ℝ 1 u) {r : ℝ} (hr : 1 ≤ r) (x h : E) :
    ‖u (x + h) - u x‖ₑ ^ r
      ≤ ‖h‖ₑ ^ r * ∫⁻ t in Icc (0 : ℝ) 1, ‖fderiv ℝ u (x + t • h)‖ₑ ^ r := by
  have hr0 : (0 : ℝ) < r := one_pos.trans_le hr
  have hmeas : AEMeasurable (fun t : ℝ => ‖fderiv ℝ u (x + t • h) h‖ₑ)
      (volume.restrict (Icc (0 : ℝ) 1)) :=
    (((hu.continuous_fderiv one_ne_zero).comp
      (by fun_prop : Continuous fun t : ℝ => x + t • h)).clm_apply
      continuous_const).enorm.aemeasurable
  have huniv : (volume.restrict (Icc (0 : ℝ) 1)) univ = 1 := by
    rw [Measure.restrict_apply_univ, Real.volume_Icc]
    simp
  calc ‖u (x + h) - u x‖ₑ ^ r
      ≤ (∫⁻ t in Icc (0 : ℝ) 1, ‖fderiv ℝ u (x + t • h) h‖ₑ) ^ r :=
        ENNReal.rpow_le_rpow (enorm_sub_le_lintegral_enorm_fderiv_apply hu x h) hr0.le
    _ ≤ ∫⁻ t in Icc (0 : ℝ) 1, ‖fderiv ℝ u (x + t • h) h‖ₑ ^ r := by
        simpa [huniv] using rpow_lintegral_le_measure_univ_rpow_mul hmeas hr
    _ ≤ ∫⁻ t in Icc (0 : ℝ) 1, (‖fderiv ℝ u (x + t • h)‖ₑ * ‖h‖ₑ) ^ r := by
        gcongr with t
        exact ContinuousLinearMap.le_opENorm _ _
    _ = ‖h‖ₑ ^ r * ∫⁻ t in Icc (0 : ℝ) 1, ‖fderiv ℝ u (x + t • h)‖ₑ ^ r := by
        simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hr0.le]
        rw [lintegral_mul_const' _ _ (by finiteness), mul_comm]

end Calculus

section Vanishing

variable {E : Type*} [NormedAddCommGroup E]

/-- A nonnegative quantity dominated by `‖h‖` times a finite constant vanishes as `h → 0`. -/
private theorem tendsto_nhds_zero_of_le_ofReal_norm_mul {G : E → ℝ≥0∞} {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hG : ∀ h : E, G h ≤ ENNReal.ofReal ‖h‖ * C) :
    Filter.Tendsto G (nhds 0) (nhds 0) := by
  have h0 : Filter.Tendsto (fun h : E => ENNReal.ofReal ‖h‖) (nhds 0) (nhds 0) := by
    simpa [Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 0).comp
      (continuous_norm.tendsto' (0 : E) 0 norm_zero)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using ENNReal.Tendsto.mul_const h0 (Or.inr hC)) (fun _ => zero_le) hG

end Vanishing

section Translation

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {mu : Measure E} [mu.IsAddHaarMeasure] {u : E → F}

/-- **The translation estimate in `∫⁻` form**: for a `C¹` function and `1 ≤ r`,
`∫ ‖u(x + h) - u(x)‖ ^ r dx ≤ ‖h‖ ^ r ∫ ‖Du‖ ^ r`.

The segment estimate is integrated in `x`, the order of integration in `x` and in the segment
parameter is exchanged, and the inner integral is then independent of the parameter because the
measure is translation invariant. -/
theorem lintegral_enorm_sub_comp_add_rpow_le (hu : ContDiff ℝ 1 u) {r : ℝ} (hr : 1 ≤ r) (h : E) :
    ∫⁻ x, ‖u (x + h) - u x‖ₑ ^ r ∂mu ≤ ‖h‖ₑ ^ r * ∫⁻ x, ‖fderiv ℝ u x‖ₑ ^ r ∂mu := by
  have hjoint : Measurable fun z : E × ℝ => ‖fderiv ℝ u (z.1 + z.2 • h)‖ₑ ^ r :=
    (ENNReal.continuous_rpow_const.comp
      (((hu.continuous_fderiv one_ne_zero).comp (by fun_prop)).enorm)).measurable
  calc ∫⁻ x, ‖u (x + h) - u x‖ₑ ^ r ∂mu
      ≤ ∫⁻ x, (‖h‖ₑ ^ r * ∫⁻ t in Icc (0 : ℝ) 1, ‖fderiv ℝ u (x + t • h)‖ₑ ^ r) ∂mu :=
        lintegral_mono fun x => enorm_sub_rpow_le hu hr x h
    _ = ‖h‖ₑ ^ r * ∫⁻ x, (∫⁻ t in Icc (0 : ℝ) 1, ‖fderiv ℝ u (x + t • h)‖ₑ ^ r) ∂mu :=
        lintegral_const_mul' _ _ (by finiteness)
    _ = ‖h‖ₑ ^ r * ∫⁻ t in Icc (0 : ℝ) 1, (∫⁻ x, ‖fderiv ℝ u (x + t • h)‖ₑ ^ r ∂mu) := by
        rw [lintegral_lintegral_swap hjoint.aemeasurable]
    _ = ‖h‖ₑ ^ r * ∫⁻ x, ‖fderiv ℝ u x‖ₑ ^ r ∂mu := by
        congr 1
        rw [setLIntegral_congr_fun measurableSet_Icc fun t _ =>
          lintegral_add_right_eq_self (fun y => ‖fderiv ℝ u y‖ₑ ^ r) (t • h),
          lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]
        simp

/-- **The `Lᵖ` translation estimate**: a `C¹` function moves in `Lᵖ` at most linearly in the
translation, at the rate given by the `Lᵖ` seminorm of its derivative,

`‖u(· + h) - u‖_p ≤ ‖h‖ ‖Du‖_p`, `1 ≤ p < ∞`.

No support, integrability or boundedness hypothesis is needed: the estimate is trivially true,
both sides being infinite, unless `Du` is already `Lᵖ`. -/
theorem eLpNorm_sub_comp_add_le (hu : ContDiff ℝ 1 u) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (h : E) :
    eLpNorm (fun x => u (x + h) - u x) p mu ≤ ENNReal.ofReal ‖h‖ * eLpNorm (fderiv ℝ u) p mu := by
  have hr : 1 ≤ p.toReal := by simpa using ENNReal.toReal_mono hp' hp
  refine eLpNorm_le_eLpNorm_of_lintegral_rpow_le (norm_nonneg h) (zero_lt_one.trans_le hp).ne'
    hp' ?_
  rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg h) (zero_lt_one.trans_le hr).le, ofReal_norm]
  exact lintegral_enorm_sub_comp_add_rpow_le hu hr h

/-- **Continuity of translation in `Lᵖ`** for a `C¹` function with `Lᵖ` derivative: the `Lᵖ`
distance between `u` and its translate tends to `0` with the translation.  This is the uniform
smallness of translations that the Fréchet--Kolmogorov compactness criterion asks for, and it is
here quantified: the modulus is linear in `‖h‖`. -/
theorem tendsto_eLpNorm_sub_comp_add (hu : ContDiff ℝ 1 u) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hfin : eLpNorm (fderiv ℝ u) p mu ≠ ∞) :
    Filter.Tendsto (fun h : E => eLpNorm (fun x => u (x + h) - u x) p mu) (nhds 0) (nhds 0) :=
  tendsto_nhds_zero_of_le_ofReal_norm_mul hfin fun h => eLpNorm_sub_comp_add_le hu hp hp' h

end Translation

section Sobolev

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {p : ENNReal} [Fact (1 ≤ p)]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [mu.IsAddHaarMeasure] in
/-- Restricting a measure to the whole space, presented as the open set `⊤`, changes nothing. -/
private theorem restrict_coe_top (mu : Measure E) :
    mu.restrict ((⊤ : Opens E) : Set E) = mu := by
  rw [Opens.coe_top, Measure.restrict_univ]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [mu.IsAddHaarMeasure] in
/-- The `Lᵖ` seminorm over the whole space, presented as the open set `⊤`, is the ambient one. -/
private theorem eLpNorm_restrict_coe_top {F : Type*} [NormedAddCommGroup F] (g : E → F)
    (p : ENNReal) (mu : Measure E) :
    eLpNorm g p (mu.restrict ((⊤ : Opens E) : Set E)) = eLpNorm g p mu :=
  congrArg (fun nu : Measure E => eLpNorm g p nu) (restrict_coe_top mu)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [mu.IsAddHaarMeasure] in
/-- An almost-everywhere statement over the whole space, presented as the open set `⊤`, is one
over the ambient measure. -/
private theorem ae_le_ae_restrict_coe_top (mu : Measure E) :
    ae mu ≤ ae (mu.restrict ((⊤ : Opens E) : Set E)) :=
  ae_mono (le_of_eq (restrict_coe_top mu).symm)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Translation by `h` preserves a Haar measure restricted to the whole space, the measure
underlying `W^{1,p}(ℝⁿ)`. -/
theorem measurePreserving_add_right_restrict_top (mu : Measure E) [mu.IsAddHaarMeasure] (h : E) :
    MeasurePreserving (· + h) (mu.restrict ((⊤ : Opens E) : Set E))
      (mu.restrict ((⊤ : Opens E) : Set E)) := by
  rw [restrict_coe_top]
  exact measurePreserving_add_right mu h

/-- Translation of an `Lᵖ` class on the whole space, as a linear isometry.  It is used only to
see the translation increment as a *continuous* function of the class, which is what makes the
translation estimate a closed condition. -/
private def translateLp (mu : Measure E) [mu.IsAddHaarMeasure] (p : ENNReal) [Fact (1 ≤ p)]
    (h : E) :
    Lp ℝ p (mu.restrict ((⊤ : Opens E) : Set E)) →ₗᵢ[ℝ]
      Lp ℝ p (mu.restrict ((⊤ : Opens E) : Set E)) :=
  Lp.compMeasurePreservingₗᵢ ℝ (· + h) (measurePreserving_add_right_restrict_top mu h)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The `Lᵖ` seminorm of a translation increment, computed on the ambient measure. -/
private theorem enorm_translateLp_sub (h : E)
    (f : Lp ℝ p (mu.restrict ((⊤ : Opens E) : Set E))) :
    ‖translateLp mu p h f - f‖ₑ = eLpNorm (fun x => f (x + h) - f x) p mu := by
  have htr : ⇑(translateLp mu p h f) =ᵐ[mu.restrict ((⊤ : Opens E) : Set E)]
      ⇑f ∘ (· + h) :=
    Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right_restrict_top mu h)
  have hae : ⇑(translateLp mu p h f - f) =ᵐ[mu.restrict ((⊤ : Opens E) : Set E)]
      fun x => f (x + h) - f x := by
    filter_upwards [Lp.coeFn_sub (translateLp mu p h f) f, htr] with x hx hy
    rw [hx, Pi.sub_apply, hy]
    rfl
  rw [Lp.enorm_def, eLpNorm_congr_ae hae, eLpNorm_restrict_coe_top]

/-- The translation estimate for a single test function, in the shape the jets of `W^{1,p}(ℝⁿ)`
present it. -/
private theorem eLpNorm_sub_comp_add_testFunctionLp_le (hp : p ≠ ∞) (h : E)
    (phi : 𝓓((⊤ : Opens E), ℝ)) :
    eLpNorm (fun x => testFunctionLp (mu := mu) p phi (x + h)
        - testFunctionLp (mu := mu) p phi x) p mu
      ≤ ENNReal.ofReal ‖h‖ * ‖gradientTestFunctionLp (mu := mu) p phi‖ₑ := by
  have hvalue : ⇑(testFunctionLp (mu := mu) p phi) =ᵐ[mu] (phi : E → ℝ) :=
    (testFunctionLp_apply_ae p phi).filter_mono (ae_le_ae_restrict_coe_top mu)
  have htrans := hvalue.comp_tendsto
    (measurePreserving_add_right mu h).quasiMeasurePreserving.tendsto_ae
  have hL : eLpNorm (fun x => testFunctionLp (mu := mu) p phi (x + h)
        - testFunctionLp (mu := mu) p phi x) p mu
      = eLpNorm (fun x => (phi : E → ℝ) (x + h) - phi x) p mu := by
    refine eLpNorm_congr_ae ?_
    filter_upwards [hvalue, htrans] with x h1 h2
    rw [h1]
    exact congrArg (· - phi x) h2
  have hR : ‖gradientTestFunctionLp (mu := mu) p phi‖ₑ
      = eLpNorm (fderiv ℝ (phi : E → ℝ)) p mu := by
    have hgrad : ⇑(gradientTestFunctionLp (mu := mu) p phi) =ᵐ[mu]
        fun x => ∇ (phi : E → ℝ) x :=
      (gradientTestFunctionLp_apply_ae p phi).filter_mono (ae_le_ae_restrict_coe_top mu)
    rw [Lp.enorm_def, eLpNorm_restrict_coe_top, eLpNorm_congr_ae hgrad,
      eLpNorm_congr_norm_ae
        (ae_of_all _ fun x => norm_gradient_eq_norm_fderiv (𝕜 := ℝ) (phi : E → ℝ) x)]
  rw [hL, hR]
  exact eLpNorm_sub_comp_add_le (phi.contDiff.of_le (by simp)) Fact.out hp h

/-- **The translation estimate on `W^{1,p}_0(ℝⁿ)`**: for `1 ≤ p < ∞`, every `u` in the closure of
the test functions satisfies

`‖u(· + h) - u‖_p ≤ ‖h‖ ‖∇u‖_p`.

The estimate for a single test function is `TauCeti.eLpNorm_sub_comp_add_le`; the set of jets
obeying it is closed, so `TauCeti.w1p0Submodule_subset_of_isClosed` passes it to the closure.
Composing with a zero-extension operator turns this into the corresponding estimate on
`W^{1,p}_0(Ω)` for an arbitrary open `Ω`, which is the form the Fréchet--Kolmogorov compactness
criterion consumes in the proof of Rellich--Kondrachov. -/
theorem W1p.eLpNorm_sub_comp_add_value_le (hp : p ≠ ∞) (h : E) {u : W1p mu ⊤ p}
    (hu : u ∈ w1p0Submodule mu ⊤ p) :
    eLpNorm (fun x => W1p.value u (x + h) - W1p.value u x) p mu
      ≤ ENNReal.ofReal ‖h‖ * ‖W1p.gradient u‖ₑ := by
  have hrw : ∀ v : W1p mu (⊤ : Opens E) p,
      eLpNorm (fun x => W1p.value v (x + h) - W1p.value v x) p mu
        = ‖translateLp mu p h (W1p.valueL v) - W1p.valueL v‖ₑ := fun v => by
    rw [enorm_translateLp_sub, W1p.valueL_apply]
  have hclosed : IsClosed {v : W1p mu ⊤ p |
      eLpNorm (fun x => W1p.value v (x + h) - W1p.value v x) p mu
        ≤ ENNReal.ofReal ‖h‖ * ‖W1p.gradient v‖ₑ} := by
    simp only [hrw, ← W1p.gradientL_apply]
    exact isClosed_le
      ((((translateLp mu p h).toContinuousLinearMap.comp W1p.valueL) -
        W1p.valueL).continuous.enorm)
      ((ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp
        W1p.gradientL.continuous.enorm)
  refine w1p0Submodule_subset_of_isClosed hclosed (fun phi => ?_) hu
  simpa only [Set.mem_ofPred_eq, W1p.value_ofTestFunctionₗ, W1p.gradient_ofTestFunctionₗ] using
    eLpNorm_sub_comp_add_testFunctionLp_le hp h phi

/-- **Continuity of translation in `Lᵖ` on `W^{1,p}_0(ℝⁿ)`**: a Sobolev function moves
continuously in `Lᵖ` under translation, at a rate linear in the translation.  This is the uniform
smallness of translations asked for by the Fréchet--Kolmogorov compactness criterion, in its
quantitative form: the modulus depends on `u` only through `‖∇u‖_p`, so it is uniform over any
family of gradient-bounded Sobolev functions. -/
theorem W1p.tendsto_eLpNorm_sub_comp_add_value (hp : p ≠ ∞) {u : W1p mu ⊤ p}
    (hu : u ∈ w1p0Submodule mu ⊤ p) :
    Filter.Tendsto (fun h : E => eLpNorm (fun x => W1p.value u (x + h) - W1p.value u x) p mu)
      (nhds 0) (nhds 0) :=
  tendsto_nhds_zero_of_le_ofReal_norm_mul (by finiteness)
    fun h => W1p.eLpNorm_sub_comp_add_value_le hp h hu

end Sobolev

end TauCeti

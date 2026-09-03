/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Cycle.Winding
import TauCeti.Analysis.Contour.Dixon.H1Diff
import TauCeti.Analysis.Contour.Dixon.H2.Bound
import TauCeti.Analysis.Contour.Dixon.H2.Diff
import TauCeti.Analysis.Contour.Dixon.FunctionDiff
import Mathlib.Analysis.Complex.Liouville

/-!
# The homology Cauchy theorem for contour cycles

This file extends the homology form of Cauchy's theorem from one parametrized closed curve to a
finite formal integer cycle. If a cycle `C` lies in an open set `U`, is null-homologous there, and
`f` is holomorphic on `U`, then `Cycle.integral f C = 0`.

The point is that null-homology belongs to the whole cycle: cancellation between different
generators may make `C` null-homologous even when no individual generator is. Thus the result does
not follow by applying the single-curve theorem termwise. Instead, Dixon's two auxiliary integrals
are summed over the finite support of `C`. Their jump across the boundary of `U` is the winding
number of the whole cycle, so cycle-level null-homology makes the sum entire; decay at infinity and
Liouville then make it zero.

## Main result

* `TauCeti.Contour.Cycle.homologyCauchyTheorem` — Cauchy's theorem for a null-homologous cycle.

## References

* J. D. Dixon, *A brief proof of Cauchy's integral theorem*, Proc. Amer. Math. Soc. 29 (1971).
* N. Hungerbühler and M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997 (2018), Section 2.

## Provenance

No formal implementation is vendored. The proof extends the repository's single-curve Dixon
development to the cycle type by finite additivity.
-/

public section

noncomputable section

open Complex MeasureTheory Set Filter

open scoped Interval Real Topology

namespace TauCeti.Contour.Cycle

/-- An open set containing the trace of a nonzero cycle contains a point outside that trace. -/
private theorem exists_mem_not_mem_trace {C : Cycle} {U : Set ℂ} (hU : IsOpen U)
    (hCU : IsIn C U) (hC : C ≠ 0) : ∃ w ∈ U, w ∉ trace C := by
  have hsupp : (FreeAbelianGroup.support C).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, FreeAbelianGroup.support_eq_empty] at h
    exact hC h
  obtain ⟨γ, hγ⟩ := hsupp
  have htrace_ne : (trace C).Nonempty :=
    ⟨γ γ.a, mem_trace_iff.mpr ⟨γ, hγ, γ.a, left_mem_uIcc, rfl⟩⟩
  have htrace_compact : IsCompact (trace C) := isCompact_trace C
  by_contra h
  push Not at h
  have hCU' := isIn_iff.mp hCU
  have heq : trace C = U := hCU'.antisymm h
  have hcompactU : IsCompact U := heq ▸ htrace_compact
  have huniv : U = Set.univ :=
    IsClopen.eq_univ ⟨hcompactU.isClosed, hU⟩ ⟨htrace_ne.some, hCU' htrace_ne.some_mem⟩
  exact noncompact_univ ℂ (huniv ▸ hcompactU)

/-- Dixon's first auxiliary function, additively extended over the support of a cycle. -/
private def cycleDixonH1 (f : ℂ → ℂ) (C : Cycle) (w : ℂ) : ℂ :=
  ∑ γ ∈ FreeAbelianGroup.support C,
    (FreeAbelianGroup.coeff γ C : ℂ) * TauCeti.Contour.dixonH1 f γ γ.a γ.b w

/-- Dixon's second auxiliary function, additively extended over the support of a cycle. -/
private def cycleDixonH2 (f : ℂ → ℂ) (C : Cycle) (w : ℂ) : ℂ :=
  ∑ γ ∈ FreeAbelianGroup.support C,
    (FreeAbelianGroup.coeff γ C : ℂ) * TauCeti.Contour.dixonH2 f γ γ.a γ.b w

/-- Dixon's glued function for a cycle: the finite sum of `h₁` terms on `U` and of `h₂` terms
off `U`. -/
private def cycleDixonFunction (f : ℂ → ℂ) (U : Set ℂ) (C : Cycle) (w : ℂ) : ℂ :=
  by
    classical
    exact if w ∈ U then cycleDixonH1 f C w else cycleDixonH2 f C w

/-- Every supported curve of a cycle contained in `U` maps its parameter interval into `U`. -/
private theorem mapsTo_of_mem_support {C : Cycle} {U : Set ℂ} (hCU : IsIn C U)
    {γ : PiecewiseC1ClosedCurve} (hγ : γ ∈ FreeAbelianGroup.support C) :
    ∀ t ∈ uIcc γ.a γ.b, γ t ∈ U := by
  intro t ht
  exact isIn_iff.mp hCU (mem_trace_iff.mpr ⟨γ, hγ, t, ht, rfl⟩)

/-- The cycle `h₁`/`h₂` identity. Away from the trace, their difference is the winding number
of the whole cycle, not a separate hypothesis on each generator. -/
private theorem cycleDixonH1_eq_cycleDixonH2_sub {f : ℂ → ℂ} {C : Cycle} {U : Set ℂ}
    (hf : ContinuousOn f U) (hCU : IsIn C U) {w : ℂ} (hw : w ∉ trace C) :
    cycleDixonH1 f C w = cycleDixonH2 f C w -
      2 * (Real.pi : ℂ) * Complex.I * windingNumber w C * f w := by
  rw [cycleDixonH1, cycleDixonH2, windingNumber_eq_sum_support]
  have hterm : ∀ γ ∈ FreeAbelianGroup.support C,
      TauCeti.Contour.dixonH1 f γ γ.a γ.b w =
        TauCeti.Contour.dixonH2 f γ γ.a γ.b w -
          2 * (Real.pi : ℂ) * Complex.I *
            TauCeti.Contour.windingNumber γ γ.a γ.b w * f w := by
    intro γ hγ
    have hoff := avoids_of_mem_support hw hγ
    have hγU := mapsTo_of_mem_support hCU hγ
    exact TauCeti.Contour.dixonH1_eq_dixonH2_sub_windingNumber_mul_f γ.continuousOn hoff
      (TauCeti.Contour.cauchy_integrand_intervalIntegrable hf γ.continuousOn hγU
        γ.intervalIntegrable_deriv hoff)
      (TauCeti.Contour.intervalIntegrable_inv_sub_mul_deriv γ.continuousOn hoff
        γ.intervalIntegrable_deriv)
  calc
    ∑ γ ∈ FreeAbelianGroup.support C,
        (FreeAbelianGroup.coeff γ C : ℂ) * TauCeti.Contour.dixonH1 f γ γ.a γ.b w =
      ∑ γ ∈ FreeAbelianGroup.support C, (FreeAbelianGroup.coeff γ C : ℂ) *
        (TauCeti.Contour.dixonH2 f γ γ.a γ.b w - 2 * (Real.pi : ℂ) * Complex.I *
          TauCeti.Contour.windingNumber γ γ.a γ.b w * f w) :=
      Finset.sum_congr rfl fun γ hγ ↦ by rw [hterm γ hγ]
    _ = (∑ γ ∈ FreeAbelianGroup.support C,
          (FreeAbelianGroup.coeff γ C : ℂ) * TauCeti.Contour.dixonH2 f γ γ.a γ.b w) -
        2 * (Real.pi : ℂ) * Complex.I *
          (∑ γ ∈ FreeAbelianGroup.support C, (FreeAbelianGroup.coeff γ C : ℂ) *
            TauCeti.Contour.windingNumber γ γ.a γ.b w) * f w := by
      simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun _ _ ↦ by ring

/-- The cycle Dixon function agrees with `h₂` at an off-trace point where the cycle winding
number vanishes. -/
private theorem cycleDixonFunction_eq_cycleDixonH2 {f : ℂ → ℂ} {C : Cycle} {U : Set ℂ}
    (hf : ContinuousOn f U) (hCU : IsIn C U) {w : ℂ} (hw : w ∉ trace C)
    (hwind : windingNumber w C = 0) :
    cycleDixonFunction f U C w = cycleDixonH2 f C w := by
  by_cases hwU : w ∈ U
  · rw [cycleDixonFunction, ite_eq_left hwU, cycleDixonH1_eq_cycleDixonH2_sub hf hCU hw,
      hwind]
    ring
  · rw [cycleDixonFunction, ite_eq_right hwU]

/-- The cycle Dixon function is entire. Null-homology makes the finite sum of the boundary jumps
vanish, even though the individual generator jumps need not vanish. -/
private theorem differentiable_cycleDixonFunction {f : ℂ → ℂ} {C : Cycle} {U : Set ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hCU : IsIn C U)
    (hnull : IsNullHomologous C U) : Differentiable ℂ (cycleDixonFunction f U C) := by
  have hH1 : DifferentiableOn ℂ (cycleDixonH1 f C) U := by
    unfold cycleDixonH1
    exact DifferentiableOn.fun_sum fun γ hγ ↦
      (TauCeti.Contour.differentiableOn_dixonH1 hU hf γ.continuousOn
        (mapsTo_of_mem_support hCU hγ) γ.intervalIntegrable_deriv).const_mul
          (FreeAbelianGroup.coeff γ C : ℂ)
  intro w
  by_cases hwU : w ∈ U
  · refine (hH1.differentiableAt (hU.mem_nhds hwU)).congr_of_eventuallyEq ?_
    filter_upwards [hU.mem_nhds hwU] with w' hw'U
    rw [cycleDixonFunction, ite_eq_left hw'U]
  · have hwtrace : w ∉ trace C := fun hw ↦ hwU (isIn_iff.mp hCU hw)
    have hH2 : DifferentiableAt ℂ (cycleDixonH2 f C) w := by
      unfold cycleDixonH2
      exact DifferentiableAt.fun_sum fun γ hγ ↦ by
        have hoff := avoids_of_mem_support hwtrace hγ
        exact (TauCeti.Contour.differentiableAt_dixonH2 γ.continuousOn hoff
          (TauCeti.Contour.cauchy_integrand_intervalIntegrable hf.continuousOn γ.continuousOn
            (mapsTo_of_mem_support hCU hγ) γ.intervalIntegrable_deriv hoff)).const_mul
              (FreeAbelianGroup.coeff γ C : ℂ)
    obtain ⟨ε, hε, hball⟩ :=
      Metric.isOpen_iff.mp (isCompact_trace C).isClosed.isOpen_compl w hwtrace
    refine hH2.congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds w hε] with w' hw'
    have hw'trace : w' ∉ trace C := hball hw'
    have hw'comp : w' ∈ connectedComponentIn (trace C)ᶜ w :=
      (convex_ball w ε).isPreconnected.subset_connectedComponentIn
        (Metric.mem_ball_self hε) hball hw'
    have hw'wind : windingNumber w' C = 0 := by
      rw [windingNumber_eq_of_mem_connectedComponentIn hw'comp]
      exact isNullHomologous_iff.mp hnull w hwU
    exact cycleDixonFunction_eq_cycleDixonH2 hf.continuousOn hCU hw'trace hw'wind

/-- The cycle `h₂` function tends to zero at infinity, termwise over the finite support. -/
private theorem cycleDixonH2_tendsto_zero {f : ℂ → ℂ} {C : Cycle} {U : Set ℂ}
    (hf : DifferentiableOn ℂ f U) (hCU : IsIn C U) :
    Tendsto (cycleDixonH2 f C) (cocompact ℂ) (nhds 0) := by
  unfold cycleDixonH2
  have hterm : ∀ γ ∈ FreeAbelianGroup.support C,
      Tendsto (fun w ↦ (FreeAbelianGroup.coeff γ C : ℂ) *
        TauCeti.Contour.dixonH2 f γ γ.a γ.b w) (cocompact ℂ) (nhds 0) := by
    intro γ hγ
    obtain ⟨R, hR⟩ := isCompact_uIcc.exists_bound_of_continuousOn γ.continuousOn
    have hγU := mapsTo_of_mem_support hCU hγ
    have hint : IntervalIntegrable (fun t ↦ f (γ t) * deriv γ t) volume γ.a γ.b :=
      γ.intervalIntegrable_deriv.continuousOn_mul (hf.continuousOn.comp γ.continuousOn hγU)
    simpa using (tendsto_const_nhds.mul
      (TauCeti.Contour.dixonH2_tendsto_zero_of_integrable
        (fun t ht ↦ hR t (uIoc_subset_uIcc ht)) hint))
  simpa using tendsto_finsetSum (FreeAbelianGroup.support C) hterm

/-- The cycle Dixon function vanishes by Liouville's theorem. -/
private theorem cycleDixonFunction_eq_zero {f : ℂ → ℂ} {C : Cycle} {U : Set ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hCU : IsIn C U)
    (hnull : IsNullHomologous C U) (w : ℂ) : cycleDixonFunction f U C w = 0 := by
  have hfar : ∀ᶠ w in cocompact ℂ, cycleDixonFunction f U C w = cycleDixonH2 f C w := by
    filter_upwards [windingNumber_eventually_zero_cocompact C] with w hw
    exact cycleDixonFunction_eq_cycleDixonH2 hf.continuousOn hCU hw.1 hw.2
  exact Differentiable.apply_eq_of_tendsto_cocompact
    (differentiable_cycleDixonFunction hU hf hCU hnull) w
    ((cycleDixonH2_tendsto_zero hf hCU).congr' (Filter.EventuallyEq.symm hfar))

/-- Dixon's `h₂` for the twist `(z - w) * f z` is the cycle integral of `f`, provided `w` is
outside the trace. -/
private theorem cycleDixonH2_twist_eq_integral {f : ℂ → ℂ} {C : Cycle} {w : ℂ}
    (hw : w ∉ trace C) :
    cycleDixonH2 (fun z ↦ (z - w) * f z) C w = integral f C := by
  rw [cycleDixonH2, integral_eq_sum_support]
  refine Finset.sum_congr rfl fun γ hγ ↦ ?_
  rw [← Int.cast_smul_eq_zsmul ℂ, smul_eq_mul]
  apply congrArg (fun z : ℂ ↦ (FreeAbelianGroup.coeff γ C : ℂ) * z)
  rw [TauCeti.Contour.dixonH2_def]
  refine intervalIntegral.integral_congr fun t ht ↦ ?_
  rw [mul_div_cancel_left₀ _ (sub_ne_zero.mpr
    (avoids_of_mem_support hw hγ t ht)), smul_eq_mul, mul_comm]

/-- **The homology Cauchy theorem for contour cycles.** Let `C` be a finite formal integer
combination of closed piecewise-`C¹` curves whose trace lies in an open set `U`. If `C` is
null-homologous in `U` and `f` is holomorphic on `U`, then the contour integral of `f` over the
whole cycle vanishes.

The null-homology assumption is imposed only on `C`, not on each supported curve, so the theorem
includes cancellations between different generators. -/
theorem homologyCauchyTheorem {f : ℂ → ℂ} {C : Cycle} {U : Set ℂ} (hU : IsOpen U)
    (hCU : IsIn C U) (hf : DifferentiableOn ℂ f U) (hnull : IsNullHomologous C U) :
    integral f C = 0 := by
  by_cases hC : C = 0
  · subst C
    simp
  · obtain ⟨w, hwU, hwtrace⟩ := exists_mem_not_mem_trace hU hCU hC
    have htwist : DifferentiableOn ℂ (fun z ↦ (z - w) * f z) U :=
      (differentiableOn_id.sub (differentiableOn_const w)).mul hf
    have hzero := cycleDixonFunction_eq_zero hU
      htwist hCU hnull w
    rw [cycleDixonFunction, ite_eq_left hwU,
      cycleDixonH1_eq_cycleDixonH2_sub
        htwist.continuousOn hCU hwtrace,
      cycleDixonH2_twist_eq_integral hwtrace] at hzero
    simpa using hzero

end TauCeti.Contour.Cycle

end

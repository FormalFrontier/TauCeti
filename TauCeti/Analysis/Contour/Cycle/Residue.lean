/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Cycle.HomologyCauchy
public import TauCeti.Analysis.Contour.Residue.Cycle
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The classical residue theorem for contour cycles

This file extends the classical residue theorem from one parametrized closed curve to a finite
formal integer cycle `C` of such curves. For `f` differentiable on `U ∖ S` and meromorphic at each
point of the finite set `S` lying in `U`, and a cycle `C` in `U` that is **null-homologous** there
and whose trace **avoids** `S`,

`Cycle.integral f C = 2πi · ∑_{s ∈ S} n_s(C) · Res_s f`,

each pole weighted by the generalized winding number of the cycle about it.

The extension is not a formal consequence of the single-curve theorem
(`TauCeti.Contour.classicalResidueTheorem_nullHomologous`) applied generator by generator: null
homology is imposed on `C` alone, and its individual generators need not be null-homologous — the
whole point of allowing formal integer combinations is that a cycle can bound while its pieces do
not. What does split over the support is the *residue* half of the argument. So the proof runs one
rung lower down: a fixed polar-part decomposition `f = g + ∑_{s ∈ S} P_s` on `U` is chosen once,
and the null-homology-free identity

`∮_γ f = ∮_γ g + 2πi · ∑_{s ∈ S} n_s(γ) · Res_s f`

(`PolarPartDecomposition.intervalIntegral_deriv_smul_eq_analyticRemainder_add_sum`) is summed over
the generators of `C` with their coefficients. Only then is the analytic remainder `g` discharged,
by the homology Cauchy theorem for cycles
(`TauCeti.Contour.Cycle.homologyCauchyTheorem`), which does see the cancellations between
generators. Its `S = ∅` case is exactly that theorem.

Cauchy's integral formula for a cycle follows, as usual, by applying the residue theorem to the
Cauchy kernel `w ↦ f w / (w − z) ^ (k + 1)`, whose only singularity in `U` is at `z`.

## Main results

* `TauCeti.Contour.Cycle.integral_eq_analyticRemainder_add_sum` — the residue sum splits off the
  cycle integral for a fixed polar-part decomposition, before any null-homology hypothesis is used.
* `TauCeti.Contour.Cycle.classicalResidueTheorem_nullHomologous` — the residue theorem for a
  null-homologous cycle avoiding the poles.
* `TauCeti.Contour.Cycle.cauchyIntegralFormula_iteratedDeriv_nullHomologous`,
  `TauCeti.Contour.Cycle.cauchyIntegralFormula_nullHomologous` and
  `TauCeti.Contour.Cycle.cauchyIntegralFormula_deriv_nullHomologous` — Cauchy's integral formula
  for a cycle, for every iterated derivative and for `f` and `f'` themselves.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997 (2018), §3.
* S. Lang, *Complex Analysis* (GTM 103), Ch. VI (the homology form of the residue theorem for
  cycles).
* L. Ahlfors, *Complex Analysis*, Ch. 4.

## Provenance

No formal source is vendored: the statements are assembled here from the repository's polar-part
decomposition and its homology Cauchy theorem for cycles, which are themselves migrated from the
AINTLIB `LeanModularForms` development.
-/

public section

open Complex MeasureTheory Set

open scoped Interval

namespace TauCeti.Contour.Cycle

variable {f : ℂ → ℂ} {S : Finset ℂ} {U : Set ℂ}

/-- **The residue sum splits off a cycle integral.** For a fixed polar-part decomposition of `f` on
`U` at `S`, a cycle lying in `U` whose trace avoids `S` integrates to the integral of the analytic
remainder plus `2πi` times the winding-weighted residue sum.

Nothing is assumed here about `f` beyond the decomposition, and — crucially for the cycle case —
nothing about null-homology: the identity is summed from its single-curve form
(`TauCeti.Contour.PolarPartDecomposition.intervalIntegral_deriv_smul_eq_analyticRemainder_add_sum`)
over the generators of the cycle, each of which may wind arbitrarily around the holes of `U`. -/
theorem integral_eq_analyticRemainder_add_sum (decomp : PolarPartDecomposition f S U) {C : Cycle}
    (hCU : IsIn C U) (hoff : ∀ s ∈ S, s ∉ trace C) :
    integral f C = integral decomp.analyticRemainder C
      + 2 * (Real.pi : ℂ) * Complex.I * ∑ s ∈ S, windingNumber s C * residue f s := by
  classical
  -- The single-curve splitting, applied to each generator in the canonical support.
  have hgen : ∀ γ ∈ FreeAbelianGroup.support C,
      (∫ t in γ.a..γ.b, deriv (⇑γ) t • f (γ t))
        = (∫ t in γ.a..γ.b, deriv (⇑γ) t • decomp.analyticRemainder (γ t))
          + 2 * (Real.pi : ℂ) * Complex.I *
              ∑ s ∈ S, TauCeti.Contour.windingNumber (⇑γ) γ.a γ.b s * residue f s := fun γ hγ ↦
    decomp.intervalIntegral_deriv_smul_eq_analyticRemainder_add_sum γ.isPiecewiseC1On
      (fun t ht ↦ isIn_iff.mp hCU (mem_trace_iff.mpr ⟨γ, hγ, t, ht, rfl⟩)) γ.source_eq_target
      (fun t ht hmem ↦ hoff _ (Finset.mem_coe.mp hmem) (mem_trace_iff.mpr ⟨γ, hγ, t, ht, rfl⟩))
  -- Regroup the double sum over generators and poles, pole index outermost.
  have hswap : ∀ γ : PiecewiseC1ClosedCurve,
      (FreeAbelianGroup.coeff γ C : ℂ) *
          (2 * (Real.pi : ℂ) * Complex.I *
            ∑ s ∈ S, TauCeti.Contour.windingNumber (⇑γ) γ.a γ.b s * residue f s)
        = ∑ s ∈ S, 2 * (Real.pi : ℂ) * Complex.I *
            ((FreeAbelianGroup.coeff γ C : ℂ) *
              TauCeti.Contour.windingNumber (⇑γ) γ.a γ.b s * residue f s) := fun γ ↦ by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ ↦ by ring
  calc
    integral f C
        = ∑ γ ∈ FreeAbelianGroup.support C, FreeAbelianGroup.coeff γ C •
            ((∫ t in γ.a..γ.b, deriv (⇑γ) t • decomp.analyticRemainder (γ t))
              + 2 * (Real.pi : ℂ) * Complex.I *
                  ∑ s ∈ S, TauCeti.Contour.windingNumber (⇑γ) γ.a γ.b s * residue f s) := by
          rw [integral_eq_sum_support]
          exact Finset.sum_congr rfl fun γ hγ ↦ by rw [hgen γ hγ]
    _ = (∑ γ ∈ FreeAbelianGroup.support C, FreeAbelianGroup.coeff γ C •
            (∫ t in γ.a..γ.b, deriv (⇑γ) t • decomp.analyticRemainder (γ t)))
          + ∑ γ ∈ FreeAbelianGroup.support C, FreeAbelianGroup.coeff γ C •
              (2 * (Real.pi : ℂ) * Complex.I *
                ∑ s ∈ S, TauCeti.Contour.windingNumber (⇑γ) γ.a γ.b s * residue f s) := by
          simp only [smul_add]
          exact Finset.sum_add_distrib
    _ = integral decomp.analyticRemainder C
          + 2 * (Real.pi : ℂ) * Complex.I * ∑ s ∈ S, windingNumber s C * residue f s := by
          rw [← integral_eq_sum_support]
          refine congrArg _ ?_
          simp only [← Int.cast_smul_eq_zsmul ℂ, smul_eq_mul]
          rw [Finset.sum_congr rfl fun γ _ ↦ hswap γ, Finset.sum_comm, Finset.mul_sum]
          refine Finset.sum_congr rfl fun s _ ↦ ?_
          rw [windingNumber_eq_sum_support, Finset.sum_mul, Finset.mul_sum]

/-- **The classical residue theorem for a null-homologous contour cycle.** Let `U` be open, `S` a
finite set, `f` differentiable on `U ∖ S` and meromorphic at each point of `S` lying in `U`, and let
`C` be a contour cycle in `U`, **null-homologous** in `U`, whose trace **avoids** `S`. Then

`Cycle.integral f C = 2πi · ∑_{s ∈ S} n_s(C) · Res_s f`,

each pole weighted by the generalized winding number of `C` about it.

Null-homology is asked of the cycle only, never of its generators, so the theorem covers the
combinations that make cycles worth having: a difference of two loops around a hole of `U`, neither
of them null-homologous, is. Points of `S` outside `U` are harmless rather than excluded, their
winding number vanishing by null-homology, and `S` may list regular points of `f`, whose residues
are `0`.

Its `S = ∅` case is the homology Cauchy theorem for cycles
(`TauCeti.Contour.Cycle.homologyCauchyTheorem`), and its one-generator case is the single-curve
theorem `TauCeti.Contour.classicalResidueTheorem_nullHomologous`. -/
theorem classicalResidueTheorem_nullHomologous (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f (U \ (↑S : Set ℂ))) (hmero : ∀ s ∈ S, s ∈ U → MeromorphicAt f s)
    {C : Cycle} (hCU : IsIn C U) (hoff : ∀ s ∈ S, s ∉ trace C) (hnull : IsNullHomologous C U) :
    integral f C = 2 * (Real.pi : ℂ) * Complex.I * ∑ s ∈ S, windingNumber s C * residue f s := by
  classical
  -- Discard the points of `S` outside `U`: null-homology kills their winding number, so nothing is
  -- asked of `f` there.
  obtain ⟨T, hTS, hfT, hmeroT, hsum⟩ : ∃ T : Finset ℂ, (∀ s ∈ T, s ∈ S) ∧
      DifferentiableOn ℂ f (U \ (↑T : Set ℂ)) ∧ (∀ s ∈ T, MeromorphicAt f s) ∧
      (∑ s ∈ S, windingNumber s C * residue f s)
        = ∑ s ∈ T, windingNumber s C * residue f s :=
    ⟨S.filter (· ∈ U), fun _ hs ↦ (Finset.mem_filter.mp hs).1,
      hf.mono fun z hz ↦ ⟨hz.1, fun hzS ↦
        hz.2 (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hzS, hz.1⟩))⟩,
      fun s hs ↦ hmero s (Finset.mem_filter.mp hs).1 (Finset.mem_filter.mp hs).2,
      (Finset.sum_filter_of_ne fun s _ hs ↦ not_not.mp fun hsU ↦
        hs (by rw [isNullHomologous_iff.mp hnull s hsU, zero_mul])).symm⟩
  rw [hsum]
  have decomp : PolarPartDecomposition f T U := .ofMeromorphic hU hfT hmeroT
  rw [integral_eq_analyticRemainder_add_sum decomp hCU fun s hs ↦ hoff s (hTS s hs),
    homologyCauchyTheorem hU hCU decomp.analyticRemainder_differentiableOn hnull, zero_add]

/-- **Cauchy's integral formula for a cycle, for the `k`-th derivative.** Let `f` be holomorphic on
an open `U`, let `C` be a contour cycle in `U` that is null-homologous there, and let `z ∈ U` lie
off the trace of `C`. Then for every `k`,

`Cycle.integral (fun w ↦ f w / (w − z) ^ (k + 1)) C = 2πi · n_z(C) · f⁽ᵏ⁾(z) / k !`.

Only the residue at `z` contributes: the residue theorem for a null-homologous cycle applied to the
Cauchy kernel `w ↦ f w / (w − z) ^ (k + 1)`, whose only possible singularity in `U` is at `z`. -/
theorem cauchyIntegralFormula_iteratedDeriv_nullHomologous {z : ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {C : Cycle} (hCU : IsIn C U) (hnull : IsNullHomologous C U)
    (hz : z ∈ U) (hoff : z ∉ trace C) (k : ℕ) :
    integral (fun w ↦ f w / (w - z) ^ (k + 1)) C
      = 2 * (Real.pi : ℂ) * Complex.I * windingNumber z C *
          (iteratedDeriv k f z / (k.factorial : ℂ)) := by
  have hfz : AnalyticAt ℂ f z := hf.analyticOnNhd hU z hz
  have hker := classicalResidueTheorem_nullHomologous (f := fun w ↦ f w / (w - z) ^ (k + 1))
    (S := {z}) hU ?_ ?_ hCU ?_ hnull
  · rw [hker, Finset.sum_singleton, residue_div_sub_pow_of_analyticAt hfz k]
    ring
  · -- Off `z` the kernel is a quotient of holomorphic functions with non-vanishing denominator.
    rw [Finset.coe_singleton]
    exact fun w hw ↦ ((hf w hw.1).mono Set.sdiff_subset).div (by fun_prop)
      (pow_ne_zero _ (sub_ne_zero.mpr hw.2))
  · -- At `z` it is meromorphic, `f` being analytic there.
    intro s hs _
    rw [Finset.mem_singleton] at hs
    subst hs
    exact hfz.meromorphicAt.div (by fun_prop)
  · exact fun s hs ↦ (Finset.mem_singleton.mp hs) ▸ hoff

/-- **Cauchy's integral formula for a cycle** (roadmap Layer 3). For `f` holomorphic on an open `U`,
`C` a contour cycle in `U` that is null-homologous there, and `z ∈ U` off the trace of `C`,

`Cycle.integral (fun w ↦ f w / (w − z)) C = 2πi · n_z(C) · f z`,

so that `f z · n_z(C) = (2πi)⁻¹ ∮_C f(w)/(w − z) dw`: the Cauchy-type integral over the cycle
recovers the value of `f` at `z`, counted with the multiplicity with which `C` winds around it. The
`S = ∅` companion of this statement is the homology Cauchy theorem for cycles
(`TauCeti.Contour.Cycle.homologyCauchyTheorem`). -/
theorem cauchyIntegralFormula_nullHomologous {z : ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {C : Cycle} (hCU : IsIn C U) (hnull : IsNullHomologous C U) (hz : z ∈ U)
    (hoff : z ∉ trace C) :
    integral (fun w ↦ f w / (w - z)) C
      = 2 * (Real.pi : ℂ) * Complex.I * windingNumber z C * f z := by
  simpa using cauchyIntegralFormula_iteratedDeriv_nullHomologous hU hf hCU hnull hz hoff 0

/-- **Cauchy's integral formula for a cycle, first derivative.** The `k = 1` case of
`TauCeti.Contour.Cycle.cauchyIntegralFormula_iteratedDeriv_nullHomologous`, stated with
`deriv f z`:

`Cycle.integral (fun w ↦ f w / (w − z) ^ 2) C = 2πi · n_z(C) · f' z`. -/
theorem cauchyIntegralFormula_deriv_nullHomologous {z : ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {C : Cycle} (hCU : IsIn C U) (hnull : IsNullHomologous C U)
    (hz : z ∈ U) (hoff : z ∉ trace C) :
    integral (fun w ↦ f w / (w - z) ^ 2) C
      = 2 * (Real.pi : ℂ) * Complex.I * windingNumber z C * deriv f z := by
  simpa [iteratedDeriv_one] using
    cauchyIntegralFormula_iteratedDeriv_nullHomologous hU hf hCU hnull hz hoff 1

end TauCeti.Contour.Cycle

end

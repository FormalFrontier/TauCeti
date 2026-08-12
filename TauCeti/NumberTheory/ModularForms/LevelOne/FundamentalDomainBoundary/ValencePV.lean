/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.ExcisedAssembly
public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.ExcisedIntegrability
public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.ArcExcisionMeasure
public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.LogDerivPV
public import TauCeti.NumberTheory.ModularForms.Order.Orbits
import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Interior
import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Containment
import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Winding.I.Value
import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Winding.Rho.Value
import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Winding.Rho.AddOne.Value

/-!
# The boundary principal value of a level-one logarithmic derivative

`intervalIntegral_excised_logDeriv_fdBoundary` assembles the boundary integral at a **fixed**
`ε`, as `2πi·ord_∞ − (k/2)·∫₁³ (excised logDeriv γ)`. Two further facts turn that into a
principal value:

* the excised integrand is integrable for every `ε` (`ExcisedIntegrability`), so the assembly's
  assumed hypotheses hold, and the first clause of `HasCauchyPVWith` is immediate;
* the arc term converges, to `(π/3)·I` (`ArcExcisionMeasure`).

So the excised integrals converge, and the limit is `2πi·ord_∞ − k·(π/6)·I` — the same constant
the *unexcised* assembly produces, as it must be, since the excision only buys tolerance of zeros
on the contour.

## Main results

* `TauCeti.ModularForm.hasCauchyPVWith_fdBoundary_logDeriv_comp_ofComplex`: the boundary
  principal value of `logDeriv (f ∘ ofComplex)` is `2πi·ord_∞ − k·(π/6)·I`.
* `TauCeti.ModularForm.two_pi_I_mul_sum_windingNumber_mul_order_eq`: equating that with the
  argument principle gives `2πi·Σ n_z·ord z = 2πi·ord_∞ − k·(π/6)·I`, the analytic identity the
  valence formula rests on.
* `TauCeti.ModularForm.sum_windingNumber_mul_orderOfVanishingAt_eq`: that identity divided by
  `2πi`, giving `Σ n_z·ord z = ord_∞ − k/12`.
* `TauCeti.ModularForm.sum_orderOfVanishingAt_add_qExpansionOrderAtCusp_eq`: the valence formula
  `Σ_q ord_q + ord_∞ = k/12` when every divisor point — zero or pole — lies in the strict
  interior of the truncated fundamental domain.
* `TauCeti.ModularForm.sum_orderOfVanishingAt_add_elliptic_add_qExpansionOrderAtCusp_eq`: the
  valence formula `Σ_q ord_q + ½·ord_i + ⅓·ord_ρ + ord_∞ = k/12`, allowing the divisor to meet
  the two elliptic corners.
* `finsum_orderOfVanishingOnOrbit_mem_image_add_elliptic_add_qExpansionOrderAtCusp_eq`
  (in `TauCeti.ModularForm`):
  the same identity with the interior sum reindexed over the orbits its points represent. ⚠ That
  sum covers only the orbits met by the divisor set `T`, not the whole non-elliptic orbit space.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development. The `ε → 0` step follows `ForMathlib/ValenceFormula/PVChain/Assembly.lean`
  (`cpv_modular_side_tendsto`), and the identification with the argument principle follows
  `ForMathlib/ValenceFormulaFinal.lean`, both ported onto the current Mathlib pin. The
  two-excision-set formulation and the route through `HasCauchyPV.unique` are Tau Ceti's.
-/

public section

open Complex Filter Function MeasureTheory Set Topology UpperHalfPlane

open scoped MatrixGroups Real

namespace TauCeti

namespace ModularForm

variable {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup SL(2, ℤ)} {k : ℤ}

/-- Each excision centre sits strictly below the ceiling, so once `ε` is small enough every
centre's `ε`-neighbourhood does too. -/
private theorem eventually_forall_im_add_lt {H : ℝ} {S : Finset ℂ} (hHgt : ∀ s ∈ S, s.im < H) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ s ∈ S, s.im + ε < H := by
  refine (Filter.eventually_all_finset S).2 fun s hs => ?_
  filter_upwards [Ioo_mem_nhdsGT (sub_pos.mpr (hHgt s hs))] with ε hε
  linarith [hε.2]

/-- The fixed-`ε` assembly, packaged as an eventual identity: for all small `ε` the excised
boundary integral is `2πi·ord_∞` minus `(k/2)` times the excised arc integral. The two
`ε`-dependent side conditions of the assembly are supplied here from their `ε`-free sources. -/
private theorem eventually_intervalIntegral_excised_eq [SlashInvariantFormClass F Γ k] (f : F)
    (hS : ModularGroup.S ∈ Γ) {H : ℝ} {S : Finset ℂ}
    (hnorm : ∀ s ∈ S, ‖s‖ = 1) (hinv : ∀ s ∈ S, -1 / s ∈ S) (hHgt : ∀ s ∈ S, s.im < H)
    (hper : Periodic (⇑f ∘ ofComplex) 1)
    (hoffγ : ∀ t ∈ Icc (0 : ℝ) 5, fdBoundary H t ∉ S →
      AnalyticAt ℂ (⇑f ∘ ofComplex) (fdBoundary H t) ∧ (⇑f ∘ ofComplex) (fdBoundary H t) ≠ 0)
    (hga : ∀ q ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H),
      AnalyticAt ℂ (cuspFunction 1 ⇑f) q)
    (hgz : ∀ q ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H), q ≠ 0 →
      cuspFunction 1 ⇑f q ≠ 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∫ t in (0 : ℝ)..5, if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
          else logDeriv (⇑f ∘ ofComplex) (fdBoundary H t) * deriv (fdBoundary H) t) =
        2 * (Real.pi : ℂ) * Complex.I * qExpansionOrderAtCusp 1 ⇑f -
          (k : ℂ) / 2 * ∫ t in (1 : ℝ)..3, (if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
            else logDeriv (fdBoundary H) t) := by
  have hside : ∀ {ε t : ℝ}, 0 < ε → ¬(∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε) → t ∈ Icc (0 : ℝ) 5 →
      AnalyticAt ℂ (⇑f ∘ ofComplex) (fdBoundary H t) ∧ (⇑f ∘ ofComplex) (fdBoundary H t) ≠ 0 := by
    intro ε t hε hex ht
    refine hoffγ t ht fun hs => hex ?_
    exact ⟨_, hs, by rw [sub_self, norm_zero]; exact hε.le⟩
  have hsub01 : uIcc (0 : ℝ) 1 ⊆ Icc (0 : ℝ) 5 := by
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl (by norm_num)
  have hsub12 : uIcc (1 : ℝ) 2 ⊆ Icc (0 : ℝ) 5 := by
    rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)]
    exact Icc_subset_Icc (by norm_num) (by norm_num)
  have hsub45 : uIcc (4 : ℝ) 5 ⊆ Icc (0 : ℝ) 5 := by
    rw [uIcc_of_le (by norm_num : (4 : ℝ) ≤ 5)]
    exact Icc_subset_Icc (by norm_num) le_rfl
  filter_upwards [eventually_forall_im_add_lt hHgt, self_mem_nhdsWithin] with ε hlt hε
  simpa only [smul_eq_mul, mul_comm] using
    intervalIntegral_excised_logDeriv_fdBoundary f hS hnorm hinv hlt hper
      (fun t ht hex =>
        (hside hε hex ⟨by linarith [ht.1], by linarith [ht.2]⟩).1.differentiableAt)
      (fun t ht hex => (hside hε hex ⟨by linarith [ht.1], by linarith [ht.2]⟩).2)
      hga hgz
      (intervalIntegrable_excised_deriv_smul_logDeriv_comp_ofComplex_fdBoundary hε hsub01
        fun t ht => hoffγ t (hsub01 ht))
      (intervalIntegrable_excised_deriv_smul_logDeriv_comp_ofComplex_fdBoundary hε hsub12
        fun t ht => hoffγ t (hsub12 ht))
      (intervalIntegrable_excised_deriv_smul_logDeriv_comp_ofComplex_fdBoundary hε hsub45
        fun t ht => hoffγ t (hsub45 ht))

/-- **The boundary principal value of a level-one logarithmic derivative.** The excised integrals
converge as `ε → 0⁺`, to `2πi·ord_∞ − k·(π/6)·I`.

The hypotheses are those of the fixed-`ε` assembly, with the two `ε`-dependent ones replaced by
their `ε`-free sources: `hHgt` (each excision centre sits below the ceiling) gives `hlt` once `ε`
is small, and `hoffγ` — analytic and nonvanishing off the centres **at the contour points** —
gives the differentiability and nonvanishing side conditions at every `ε`, as well as the
integrability. Stating it along the contour rather than on an open set is what keeps this
excision set independent of the argument principle's divisor set. -/
theorem hasCauchyPVWith_fdBoundary_logDeriv_comp_ofComplex [SlashInvariantFormClass F Γ k] (f : F)
    (hS : ModularGroup.S ∈ Γ) {H : ℝ} {S : Finset ℂ}
    (hnorm : ∀ s ∈ S, ‖s‖ = 1) (hinv : ∀ s ∈ S, -1 / s ∈ S) (hHgt : ∀ s ∈ S, s.im < H)
    (hper : Periodic (⇑f ∘ ofComplex) 1)
    (hoffγ : ∀ t ∈ Icc (0 : ℝ) 5, fdBoundary H t ∉ S →
      AnalyticAt ℂ (⇑f ∘ ofComplex) (fdBoundary H t) ∧ (⇑f ∘ ofComplex) (fdBoundary H t) ≠ 0)
    (hga : ∀ q ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H),
      AnalyticAt ℂ (cuspFunction 1 ⇑f) q)
    (hgz : ∀ q ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H), q ≠ 0 →
      cuspFunction 1 ⇑f q ≠ 0) :
    Contour.HasCauchyPVWith (fdBoundary H) 0 5 (logDeriv (⇑f ∘ ofComplex)) S
      (2 * (Real.pi : ℂ) * Complex.I * qExpansionOrderAtCusp 1 ⇑f -
        (k : ℂ) * ((Real.pi / 6 : ℝ) * Complex.I)) := by
  refine Contour.hasCauchyPVWith_iff.mpr ⟨?_, ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    simpa only [smul_eq_mul, mul_comm] using
      intervalIntegrable_excised_deriv_smul_logDeriv_comp_ofComplex_fdBoundary hε
        (by rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)])
        fun t ht => hoffγ t (by rwa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)] at ht)
  · refine Tendsto.congr' (Filter.EventuallyEq.symm
      (eventually_intervalIntegral_excised_eq f hS hnorm hinv hHgt hper hoffγ hga hgz)) ?_
    have hval : 2 * (Real.pi : ℂ) * Complex.I * qExpansionOrderAtCusp 1 ⇑f -
        (k : ℂ) / 2 * ((Real.pi / 3 : ℝ) * Complex.I) =
        2 * (Real.pi : ℂ) * Complex.I * qExpansionOrderAtCusp 1 ⇑f -
          (k : ℂ) * ((Real.pi / 6 : ℝ) * Complex.I) := by
      push_cast
      ring
    exact hval ▸ (tendsto_const_nhds.sub
      ((tendsto_intervalIntegral_excised_logDeriv_fdBoundary_arc H S).const_mul _))

/-- **The weighted order sum equals the cusp order minus the weight term.** Both sides are the
same Cauchy principal value along the boundary contour: `hasCauchyPV_fdBoundary_logDeriv`
evaluates it by the argument principle, as `2πi` times the winding-weighted sum of orders over
the **divisor** set `T` — orders, not zero-counts: a point of `T` where the form has a pole
contributes negatively, while `hasCauchyPVWith_fdBoundary_logDeriv_comp_ofComplex` evaluates it
by the excised assembly, excising the **boundary** set `S`. Principal values are unique even
across different excision sets, so the two agree.

Keeping `S` and `T` separate is what makes the statement useful: the assembly forces its excision
set onto the unit circle (`hnorm`, `hinv` — the arc pairing and vertical cancellation need those
symmetries), whereas the divisor set is unrestricted, so zeros in the interior are allowed. The
assembly's side conditions are needed only *along the contour*, which is what `hoffγ` states.

This is the analytic identity the valence formula rests on: dividing by `2πi` and reading off the
corner winding numbers — which are **negative**, the contour running clockwise: `-(1/2)` at `i`
and `-(1/6)` at each `ρ`-corner, against `-1` at an interior point — turns it into
`ord_∞ + ½·ord_i + ⅓·ord_ρ + Σ ord_q = k/12`. -/
theorem two_pi_I_mul_sum_windingNumber_mul_order_eq [SlashInvariantFormClass F Γ k] (f : F)
    (hS : ModularGroup.S ∈ Γ) {H : ℝ} {S T : Finset ℂ} {U : Set ℂ} {ord : ℂ → ℤ} (hH : 1 ≤ H)
    (hnorm : ∀ s ∈ S, ‖s‖ = 1) (hinv : ∀ s ∈ S, -1 / s ∈ S) (hHgt : ∀ s ∈ S, s.im < H)
    (hper : Periodic (⇑f ∘ ofComplex) 1)
    (hoffγ : ∀ t ∈ Icc (0 : ℝ) 5, fdBoundary H t ∉ S →
      AnalyticAt ℂ (⇑f ∘ ofComplex) (fdBoundary H t) ∧ (⇑f ∘ ofComplex) (fdBoundary H t) ≠ 0)
    (hU : IsOpen U)
    (hUdom : UpperHalfPlane.coe '' ModularGroup.truncatedFundamentalDomain H ⊆ U)
    (hoff : ∀ z ∈ U, z ∉ T → AnalyticAt ℂ (⇑f ∘ ofComplex) z ∧ (⇑f ∘ ofComplex) z ≠ 0)
    (hmero : ∀ s ∈ T, s ∈ U → MeromorphicAt (⇑f ∘ ofComplex) s)
    (hord : ∀ s ∈ T, s ∈ U → meromorphicOrderAt (⇑f ∘ ofComplex) s = (ord s : WithTop ℤ))
    (hbase : fdBoundary H 0 ∉ (T : Set ℂ))
    (hga : ∀ q ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H),
      AnalyticAt ℂ (cuspFunction 1 ⇑f) q)
    (hgz : ∀ q ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H), q ≠ 0 →
      cuspFunction 1 ⇑f q ≠ 0) :
    2 * (Real.pi : ℂ) * Complex.I *
        ∑ z ∈ T, Contour.windingNumber (fdBoundary H) 0 5 z * (ord z : ℂ) =
      2 * (Real.pi : ℂ) * Complex.I * qExpansionOrderAtCusp 1 ⇑f -
        (k : ℂ) * ((Real.pi / 6 : ℝ) * Complex.I) :=
  (hasCauchyPV_fdBoundary_logDeriv hH hU hUdom hoff hmero hord hbase).unique
    (hasCauchyPVWith_fdBoundary_logDeriv_comp_ofComplex f hS hnorm hinv hHgt hper hoffγ hga
      hgz).hasCauchyPV

/-- **The weighted order sum in terms of `orderOfVanishingAt`.** With the divisor points in the
upper half plane, the abstract order function of `two_pi_I_mul_sum_windingNumber_mul_order_eq` is
the modular-forms order at each of them.

`orderOfVanishingAt` is by definition the meromorphic order of `f ∘ ofComplex`
(`orderOfVanishingAt_def`), so the abstract hypothesis asks only that those orders be finite —
which `hoff` and the finiteness of `T` already force, so no separate hypothesis is needed. The
sum runs over `T.attach` because the order is taken at each divisor point *as a point of `ℍ`*,
which needs its membership proof. -/
private theorem two_pi_I_mul_sum_windingNumber_mul_orderOfVanishingAt_eq
    [SlashInvariantFormClass F Γ k] (f : F) (hS : ModularGroup.S ∈ Γ) {H : ℝ} {S T : Finset ℂ}
    {U : Set ℂ} (hH : 1 ≤ H) (hnorm : ∀ s ∈ S, ‖s‖ = 1) (hinv : ∀ s ∈ S, -1 / s ∈ S)
    (hHgt : ∀ s ∈ S, s.im < H) (hper : Periodic (⇑f ∘ ofComplex) 1)
    (hoffγ : ∀ t ∈ Icc (0 : ℝ) 5, fdBoundary H t ∉ S →
      AnalyticAt ℂ (⇑f ∘ ofComplex) (fdBoundary H t) ∧ (⇑f ∘ ofComplex) (fdBoundary H t) ≠ 0)
    (hU : IsOpen U)
    (hUdom : UpperHalfPlane.coe '' ModularGroup.truncatedFundamentalDomain H ⊆ U)
    (hoff : ∀ z ∈ U, z ∉ T → AnalyticAt ℂ (⇑f ∘ ofComplex) z ∧ (⇑f ∘ ofComplex) z ≠ 0)
    (hmero : ∀ s ∈ T, s ∈ U → MeromorphicAt (⇑f ∘ ofComplex) s)
    (hpos : ∀ s ∈ T, 0 < s.im) (hbase : fdBoundary H 0 ∉ (T : Set ℂ))
    (hga : ∀ q ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H),
      AnalyticAt ℂ (cuspFunction 1 ⇑f) q)
    (hgz : ∀ q ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H), q ≠ 0 →
      cuspFunction 1 ⇑f q ≠ 0) :
    2 * (Real.pi : ℂ) * Complex.I *
        ∑ z ∈ T.attach, Contour.windingNumber (fdBoundary H) 0 5 (z : ℂ) *
          ((orderOfVanishingAt ⇑f ⟨(z : ℂ), hpos _ z.2⟩ : ℤ) : ℂ) =
      2 * (Real.pi : ℂ) * Complex.I * qExpansionOrderAtCusp 1 ⇑f -
        (k : ℂ) * ((Real.pi / 6 : ℝ) * Complex.I) := by
  have hsummand : ∀ z ∈ T.attach,
      Contour.windingNumber (fdBoundary H) 0 5 (z : ℂ) *
          ((orderOfVanishingAt ⇑f ⟨(z : ℂ), hpos _ z.2⟩ : ℤ) : ℂ) =
        Contour.windingNumber (fdBoundary H) 0 5 (z : ℂ) *
          (((meromorphicOrderAt (⇑f ∘ ofComplex) (z : ℂ)).untop₀ : ℤ) : ℂ) := by
    intro z _
    rw [orderOfVanishingAt_def]
  rw [Finset.sum_congr rfl hsummand,
    Finset.sum_attach T fun z => Contour.windingNumber (fdBoundary H) 0 5 z *
      (((meromorphicOrderAt (⇑f ∘ ofComplex) z).untop₀ : ℤ) : ℂ)]
  exact two_pi_I_mul_sum_windingNumber_mul_order_eq f hS hH hnorm hinv hHgt hper hoffγ hU hUdom
    hoff hmero (fun s hsT hsU => (WithTop.coe_untop₀_of_ne_top
      ((meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hmero s hsT hsU)).2 (by
        filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hsU),
          T.eventually_cofinite_notMem.filter_mono (nhdsNE_le_cofinite s)] with z hzU hzT
        exact (hoff z hzU hzT).2))).symm) hbase hga
    hgz

/-- **The valence identity, divided through.** Cancelling the common factor `2πi` puts the
identity in the shape the valence formula is usually written in: the winding-weighted sum of
orders inside the contour equals the cusp order minus `k/12`. The orders are meromorphic orders,
so a pole contributes negatively.

The weight term matches because `k·(π/6)·I = 2πi·(k/12)`. -/
theorem sum_windingNumber_mul_orderOfVanishingAt_eq [SlashInvariantFormClass F Γ k] (f : F)
    (hS : ModularGroup.S ∈ Γ) {H : ℝ} {S T : Finset ℂ} {U : Set ℂ} (hH : 1 ≤ H)
    (hnorm : ∀ s ∈ S, ‖s‖ = 1) (hinv : ∀ s ∈ S, -1 / s ∈ S) (hHgt : ∀ s ∈ S, s.im < H)
    (hper : Periodic (⇑f ∘ ofComplex) 1)
    (hoffγ : ∀ t ∈ Icc (0 : ℝ) 5, fdBoundary H t ∉ S →
      AnalyticAt ℂ (⇑f ∘ ofComplex) (fdBoundary H t) ∧ (⇑f ∘ ofComplex) (fdBoundary H t) ≠ 0)
    (hU : IsOpen U)
    (hUdom : UpperHalfPlane.coe '' ModularGroup.truncatedFundamentalDomain H ⊆ U)
    (hoff : ∀ z ∈ U, z ∉ T → AnalyticAt ℂ (⇑f ∘ ofComplex) z ∧ (⇑f ∘ ofComplex) z ≠ 0)
    (hmero : ∀ s ∈ T, s ∈ U → MeromorphicAt (⇑f ∘ ofComplex) s)
    (hpos : ∀ s ∈ T, 0 < s.im) (hbase : fdBoundary H 0 ∉ (T : Set ℂ))
    (hga : ∀ q ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H),
      AnalyticAt ℂ (cuspFunction 1 ⇑f) q)
    (hgz : ∀ q ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H), q ≠ 0 →
      cuspFunction 1 ⇑f q ≠ 0) :
    ∑ z ∈ T.attach, Contour.windingNumber (fdBoundary H) 0 5 (z : ℂ) *
        ((orderOfVanishingAt ⇑f ⟨(z : ℂ), hpos _ z.2⟩ : ℤ) : ℂ) =
      qExpansionOrderAtCusp 1 ⇑f - (k : ℂ) / 12 := by
  refine mul_left_cancel₀ Complex.two_pi_I_ne_zero ?_
  rw [two_pi_I_mul_sum_windingNumber_mul_orderOfVanishingAt_eq f hS hH hnorm hinv hHgt hper hoffγ
    hU hUdom hoff hmero hpos hbase hga hgz]
  push_cast
  ring

/-- **The valence formula for a divisor supported in the strict interior.** When every divisor
point — pole as well as zero — lies in the strict interior of the truncated fundamental domain,
each winding number is `-1` (`windingNumber_fdBoundary_eq_neg_one_of_interior`), so the weighted
count collapses to the plain sum of orders and the identity reads

`Σ_q ord_q + ord_∞ = k/12`.

The hypothesis is stronger than merely having no *elliptic* zeros: `hin` excludes every boundary
divisor point, elliptic or not, and poles along with zeros. The general case allows divisor
points on the boundary, and picks up the `½` and `⅓` terms from the corner winding numbers at
`i` and `ρ`. -/
theorem sum_orderOfVanishingAt_add_qExpansionOrderAtCusp_eq [SlashInvariantFormClass F Γ k]
    (f : F) (hS : ModularGroup.S ∈ Γ) {H : ℝ} {S T : Finset ℂ} {U : Set ℂ} (hH : 1 < H)
    (hnorm : ∀ s ∈ S, ‖s‖ = 1) (hinv : ∀ s ∈ S, -1 / s ∈ S)
    (hper : Periodic (⇑f ∘ ofComplex) 1)
    (hoffγ : ∀ t ∈ Icc (0 : ℝ) 5, fdBoundary H t ∉ S →
      AnalyticAt ℂ (⇑f ∘ ofComplex) (fdBoundary H t) ∧ (⇑f ∘ ofComplex) (fdBoundary H t) ≠ 0)
    (hU : IsOpen U)
    (hUdom : UpperHalfPlane.coe '' ModularGroup.truncatedFundamentalDomain H ⊆ U)
    (hoff : ∀ z ∈ U, z ∉ T → AnalyticAt ℂ (⇑f ∘ ofComplex) z ∧ (⇑f ∘ ofComplex) z ≠ 0)
    (hmero : ∀ s ∈ T, s ∈ U → MeromorphicAt (⇑f ∘ ofComplex) s)
    (hpos : ∀ s ∈ T, 0 < s.im)
    (hin : ∀ s ∈ T, 1 < ‖s‖ ∧ |s.re| < 1 / 2 ∧ s.im < H)
    (hga : ∀ q ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H),
      AnalyticAt ℂ (cuspFunction 1 ⇑f) q)
    (hgz : ∀ q ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H), q ≠ 0 →
      cuspFunction 1 ⇑f q ≠ 0) :
    ∑ z ∈ T.attach, ((orderOfVanishingAt ⇑f ⟨(z : ℂ), hpos _ z.2⟩ : ℤ) : ℂ) +
        qExpansionOrderAtCusp 1 ⇑f = (k : ℂ) / 12 := by
  -- Both are forced by the data: excision centres sit on the unit circle, and every divisor
  -- point has `|re| < 1/2` while the basepoint has real part exactly `1/2`.
  have hHgt : ∀ s ∈ S, s.im < H := fun s hs => by
    have h1 : s.im ≤ ‖s‖ := (le_abs_self _).trans (Complex.abs_im_le_norm s)
    rw [hnorm s hs] at h1
    linarith
  have hbase : fdBoundary H 0 ∉ (T : Set ℂ) := fun hmem => by
    have h := (hin _ hmem).2.1
    rw [fdBoundary_apply_zero] at h
    simp at h
  have hw : ∀ z ∈ T.attach,
      Contour.windingNumber (fdBoundary H) 0 5 (z : ℂ) *
          ((orderOfVanishingAt ⇑f ⟨(z : ℂ), hpos _ z.2⟩ : ℤ) : ℂ) =
        -((orderOfVanishingAt ⇑f ⟨(z : ℂ), hpos _ z.2⟩ : ℤ) : ℂ) := by
    intro z _
    obtain ⟨h1, h2, h3⟩ := hin _ z.2
    rw [windingNumber_fdBoundary_eq_neg_one_of_interior hH h1 h2 (hpos _ z.2) h3, neg_one_mul]
  have := sum_windingNumber_mul_orderOfVanishingAt_eq f hS hH.le hnorm hinv hHgt hper hoffγ hU
    hUdom hoff hmero hpos hbase hga hgz
  rw [Finset.sum_congr rfl hw, Finset.sum_neg_distrib] at this
  linear_combination -this


/-- A weighted divisor sum over `X.attach` as a plain sum over `X`. Each term of the attached
sum carries its own membership proof; `ofComplex` is the total map that replaces it, and it
agrees with the attached point because `X` lies in the upper half plane. -/
private lemma sum_attach_mul_orderOfVanishingAt {f : ℍ → ℂ} {X : Finset ℂ}
    (hX : ∀ z ∈ X, 0 < z.im) (c : ℂ → ℂ) :
    ∑ z ∈ X.attach, c (z : ℂ) * ((orderOfVanishingAt f ⟨(z : ℂ), hX _ z.2⟩ : ℤ) : ℂ) =
      ∑ z ∈ X, c z * ((orderOfVanishingAt f (ofComplex z) : ℤ) : ℂ) := by
  rw [← Finset.sum_attach X fun z => c z * ((orderOfVanishingAt f (ofComplex z) : ℤ) : ℂ)]
  exact Finset.sum_congr rfl fun z _ => by rw [ofComplex_apply_of_im_pos (hX _ z.2)]


/-- The height of the `ρ`-corner. -/
private lemma coe_rho_im : (ρ : ℂ).im = Real.sqrt 3 / 2 := by simp [UpperHalfPlane.ρ]

/-- The `i`-corner sits at height `1` and both `ρ`-corners at height `√3/2 < 1`, so the three
elliptic corners are distinct. -/
private lemma corner_notMem :
    Complex.I ∉ ({(ρ : ℂ), (ρ : ℂ) + 1} : Finset ℂ) ∧
      (ρ : ℂ) ∉ ({(ρ : ℂ) + 1} : Finset ℂ) := by
  have hne : (ρ : ℂ).im ≠ Complex.I.im := by
    rw [coe_rho_im, Complex.I_im]
    exact ne_of_lt sqrt_three_div_two_lt_one
  refine ⟨?_, by simp⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨fun h => hne (by simp [h]), fun h => hne (by simp [h])⟩

/-- Both `ρ`-corners lie in the upper half plane. -/
private lemma coe_rho_add_one_im_pos : (0 : ℝ) < ((ρ : ℂ) + 1).im := by
  simp only [Complex.add_im, Complex.one_im, add_zero, coe_rho_im]
  positivity

/-- Off the three corners every divisor point is interior, so its winding weight is `-1` and it
enters the count with its bare order. -/
private lemma sum_sdiff_corner_windingNumber_mul_order {f : ℍ → ℂ} {H : ℝ} {T : Finset ℂ}
    (hH : 1 < H) (hpos : ∀ s ∈ T, 0 < s.im)
    (hin : ∀ z ∈ T, z ∉ ({Complex.I, (ρ : ℂ), (ρ : ℂ) + 1} : Finset ℂ) →
      1 < ‖z‖ ∧ |z.re| < 1 / 2 ∧ z.im < H) :
    ∑ z ∈ T \ ({Complex.I, (ρ : ℂ), (ρ : ℂ) + 1} : Finset ℂ),
        Contour.windingNumber (fdBoundary H) 0 5 z *
          ((orderOfVanishingAt f (ofComplex z) : ℤ) : ℂ) =
      -∑ z ∈ T \ ({Complex.I, (ρ : ℂ), (ρ : ℂ) + 1} : Finset ℂ),
        ((orderOfVanishingAt f (ofComplex z) : ℤ) : ℂ) := by
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun z hz => ?_
  obtain ⟨hzT, hzE⟩ := Finset.mem_sdiff.mp hz
  obtain ⟨h1, h2, h3⟩ := hin z hzT hzE
  rw [windingNumber_fdBoundary_eq_neg_one_of_interior hH h1 h2 (hpos _ hzT) h3, neg_one_mul]

/-- The three corners carry weights `-(1/2)` at `i` and `-(1/6)` at each `ρ`-corner. Periodicity
gives the two `ρ`-corners the same order, so their two `1/6`s merge into a single `1/3`. -/
private lemma sum_corner_windingNumber_mul_order {f : ℍ → ℂ} {H : ℝ} (hH : 1 < H)
    (hper : Periodic (f ∘ ofComplex) 1) :
    ∑ z ∈ ({Complex.I, (ρ : ℂ), (ρ : ℂ) + 1} : Finset ℂ),
        Contour.windingNumber (fdBoundary H) 0 5 z *
          ((orderOfVanishingAt f (ofComplex z) : ℤ) : ℂ) =
      -(1 / 2) * ((orderOfVanishingAt f UpperHalfPlane.I : ℤ) : ℂ) -
        1 / 3 * ((orderOfVanishingAt f ρ : ℤ) : ℂ) := by
  have hρH : Real.sqrt 3 / 2 < H := sqrt_three_div_two_lt_one.trans hH
  have hofI : ofComplex Complex.I = UpperHalfPlane.I := by
    rw [← UpperHalfPlane.coe_I, ofComplex_apply]
  -- The two `ρ`-corners are a unit translate apart, so periodicity equates their orders.
  have hordρ1 : orderOfVanishingAt f (ofComplex ((ρ : ℂ) + 1)) = orderOfVanishingAt f ρ :=
    orderOfVanishingAt_eq_of_coe_eq_add hper
      (by rw [ofComplex_apply_of_im_pos coe_rho_add_one_im_pos])
  rw [Finset.sum_insert corner_notMem.1, Finset.sum_insert corner_notMem.2, Finset.sum_singleton,
    windingNumber_fdBoundary_I hH, windingNumber_fdBoundary_rho hρH,
    windingNumber_fdBoundary_rho_add_one hρH, hofI, ofComplex_apply ρ, hordρ1]
  ring

/-- A corner the divisor set misses contributes nothing: it lies on the contour, hence in `U`, so
`hoff` makes the form analytic and nonvanishing there and its order is `0`. -/
private lemma orderOfVanishingAt_corner_eq_zero [SlashInvariantFormClass F Γ k] (f : F) {H : ℝ}
    {T : Finset ℂ} {U : Set ℂ} (hH : 1 < H)
    (hUdom : UpperHalfPlane.coe '' ModularGroup.truncatedFundamentalDomain H ⊆ U)
    (hoff : ∀ z ∈ U, z ∉ T → AnalyticAt ℂ (⇑f ∘ ofComplex) z ∧ (⇑f ∘ ofComplex) z ≠ 0)
    {c : ℂ} (hc : c ∈ ({Complex.I, (ρ : ℂ), (ρ : ℂ) + 1} : Finset ℂ)) (hcT : c ∉ T) :
    orderOfVanishingAt ⇑f (ofComplex c) = 0 := by
  have hIm : 0 < c.im := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl
    · simp
    · rw [coe_rho_im]; positivity
    · exact coe_rho_add_one_im_pos
  have hcU : c ∈ U := by
    refine hUdom ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl | rfl
    · exact fdBoundary_apply_two H ▸
        fdBoundary_mem_coe_truncatedFundamentalDomain hH.le (by norm_num)
    · exact fdBoundary_apply_three H ▸
        fdBoundary_mem_coe_truncatedFundamentalDomain hH.le (by norm_num)
    · exact fdBoundary_apply_one H ▸
        fdBoundary_mem_coe_truncatedFundamentalDomain hH.le (by norm_num)
  obtain ⟨han, hne⟩ := hoff c hcU hcT
  rw [ofComplex_apply_of_im_pos hIm]
  exact orderOfVanishingAt_eq_zero_of_ne_zero han.meromorphicNFAt
    (by simpa [Function.comp_apply, ofComplex_apply_of_im_pos hIm] using hne)


/-- **The valence formula, with the elliptic points.** The divisor may now meet the two elliptic
corners of the truncated fundamental domain, `i` and `ρ` (the `ρ`-corner appearing twice on the
contour, at `ρ` and at `ρ + 1`); every other divisor point is required to lie in the strict
interior.

The corner winding numbers are `-(1/2)` at `i` and `-(1/6)` at each `ρ`-corner, against `-1` in
the interior, so those points enter the count with weights `½` and `⅙`. Periodicity makes the two
`ρ`-corners carry the same order, and the two `⅙`s combine:

`Σ_q ord_q + ½·ord_i + ⅓·ord_ρ + ord_∞ = k/12`.

A corner that `T` misses is no special case: it lies on the contour, so `hUdom` and `hoff` make
the form analytic and nonzero there, and at such a point the order is `0`. -/
theorem sum_orderOfVanishingAt_add_elliptic_add_qExpansionOrderAtCusp_eq
    [SlashInvariantFormClass F Γ k] (f : F) (hS : ModularGroup.S ∈ Γ) {H : ℝ} {S T : Finset ℂ}
    {U : Set ℂ} (hH : 1 < H) (hnorm : ∀ s ∈ S, ‖s‖ = 1) (hinv : ∀ s ∈ S, -1 / s ∈ S)
    (hper : Periodic (⇑f ∘ ofComplex) 1)
    (hoffγ : ∀ t ∈ Icc (0 : ℝ) 5, fdBoundary H t ∉ S →
      AnalyticAt ℂ (⇑f ∘ ofComplex) (fdBoundary H t) ∧ (⇑f ∘ ofComplex) (fdBoundary H t) ≠ 0)
    (hU : IsOpen U)
    (hUdom : UpperHalfPlane.coe '' ModularGroup.truncatedFundamentalDomain H ⊆ U)
    (hoff : ∀ z ∈ U, z ∉ T → AnalyticAt ℂ (⇑f ∘ ofComplex) z ∧ (⇑f ∘ ofComplex) z ≠ 0)
    (hmero : ∀ s ∈ T, s ∈ U → MeromorphicAt (⇑f ∘ ofComplex) s)
    (hpos : ∀ s ∈ T, 0 < s.im)
    (hin : ∀ z ∈ T, z ∉ ({Complex.I, (ρ : ℂ), (ρ : ℂ) + 1} : Finset ℂ) →
      1 < ‖z‖ ∧ |z.re| < 1 / 2 ∧ z.im < H)
    (hga : ∀ q ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H),
      AnalyticAt ℂ (cuspFunction 1 ⇑f) q)
    (hgz : ∀ q ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H), q ≠ 0 →
      cuspFunction 1 ⇑f q ≠ 0) :
    ∑ z ∈ T \ ({Complex.I, (ρ : ℂ), (ρ : ℂ) + 1} : Finset ℂ),
          ((orderOfVanishingAt ⇑f (ofComplex z) : ℤ) : ℂ)
        + 1 / 2 * ((orderOfVanishingAt ⇑f UpperHalfPlane.I : ℤ) : ℂ)
        + 1 / 3 * ((orderOfVanishingAt ⇑f ρ : ℤ) : ℂ)
        + qExpansionOrderAtCusp 1 ⇑f = (k : ℂ) / 12 := by
  have hHgt : ∀ s ∈ S, s.im < H := fun s hs => by
    have h1 : s.im ≤ ‖s‖ := (le_abs_self _).trans (Complex.abs_im_le_norm s)
    rw [hnorm s hs] at h1
    linarith
  -- The basepoint sits at height `H`, above all three corners, and its real part is exactly
  -- `1/2`, which `hin` forbids off the corners.
  have hbase : fdBoundary H 0 ∉ (T : Set ℂ) := fun hmem => by
    have hre : (fdBoundary H 0).re = 1 / 2 := by rw [fdBoundary_apply_zero]; simp
    have him : (fdBoundary H 0).im = H := by rw [fdBoundary_apply_zero]; simp
    by_cases hE : fdBoundary H 0 ∈ ({Complex.I, (ρ : ℂ), (ρ : ℂ) + 1} : Finset ℂ)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hE
      rcases hE with h | h | h <;> rw [h] at him <;>
        simp only [Complex.I_im, Complex.add_im, Complex.one_im, add_zero, coe_rho_im] at him <;>
        linarith [sqrt_three_div_two_lt_one]
    · have := (hin _ (Finset.mem_coe.mp hmem) hE).2.1
      rw [hre] at this
      norm_num at this
  -- A corner outside `T` contributes nothing, so the count may be taken over all three.
  have hmiss : ∀ c ∈ ({Complex.I, (ρ : ℂ), (ρ : ℂ) + 1} : Finset ℂ),
      c ∉ T ∩ ({Complex.I, (ρ : ℂ), (ρ : ℂ) + 1} : Finset ℂ) →
      Contour.windingNumber (fdBoundary H) 0 5 c *
        ((orderOfVanishingAt ⇑f (ofComplex c) : ℤ) : ℂ) = 0 := fun c hc hcni => by
    rw [orderOfVanishingAt_corner_eq_zero f hH hUdom hoff hc
      fun hcT => hcni (Finset.mem_inter.mpr ⟨hcT, hc⟩)]
    simp
  -- Named because `Finset.sum_sdiff` is rewritten right-to-left, so the subset's two `Finset`
  -- arguments are not determined by the goal and must be pinned here.
  have hTE : T ∩ ({Complex.I, (ρ : ℂ), (ρ : ℂ) + 1} : Finset ℂ) ⊆ T := Finset.inter_subset_left
  have key := sum_windingNumber_mul_orderOfVanishingAt_eq f hS hH.le hnorm hinv hHgt hper hoffγ hU
    hUdom hoff hmero hpos hbase hga hgz
  rw [sum_attach_mul_orderOfVanishingAt hpos fun z => Contour.windingNumber (fdBoundary H) 0 5 z,
    ← Finset.sum_sdiff hTE,
    Finset.sdiff_inter_self_left, Finset.sum_subset Finset.inter_subset_right hmiss,
    sum_sdiff_corner_windingNumber_mul_order hH hpos hin,
    sum_corner_windingNumber_mul_order hH hper] at key
  linear_combination -key


/-- **The valence formula, with its divisor sum reindexed over orbits.** The order is constant
along the `SL₂(ℤ)`-action, so the interior divisor points may be replaced by the orbits they
represent; this is faithful because distinct points of the open fundamental domain lie in
distinct orbits.

⚠ The sum here runs over the orbits *met by the divisor set* `T`, **not** over the whole
non-elliptic orbit space, which is what the roadmap's Layer-1 target states. Reaching that needs
the further step that an orbit missed by `T` contributes `0`.

Level one is forced: `orderOfVanishingOnOrbit` is defined for `𝒮ℒ`-invariant forms, so this
theorem takes the level-one class rather than a general `Γ`. -/
theorem finsum_orderOfVanishingOnOrbit_mem_image_add_elliptic_add_qExpansionOrderAtCusp_eq
    [SlashInvariantFormClass F 𝒮ℒ k] (f : F) {H : ℝ} {S T : Finset ℂ} {U : Set ℂ} (hH : 1 < H)
    (hnorm : ∀ s ∈ S, ‖s‖ = 1) (hinv : ∀ s ∈ S, -1 / s ∈ S)
    (hoffγ : ∀ t ∈ Icc (0 : ℝ) 5, fdBoundary H t ∉ S →
      AnalyticAt ℂ (⇑f ∘ ofComplex) (fdBoundary H t) ∧ (⇑f ∘ ofComplex) (fdBoundary H t) ≠ 0)
    (hU : IsOpen U)
    (hUdom : UpperHalfPlane.coe '' ModularGroup.truncatedFundamentalDomain H ⊆ U)
    (hoff : ∀ z ∈ U, z ∉ T → AnalyticAt ℂ (⇑f ∘ ofComplex) z ∧ (⇑f ∘ ofComplex) z ≠ 0)
    (hmero : ∀ s ∈ T, s ∈ U → MeromorphicAt (⇑f ∘ ofComplex) s)
    (hpos : ∀ s ∈ T, 0 < s.im)
    (hin : ∀ z ∈ T, z ∉ ({Complex.I, (ρ : ℂ), (ρ : ℂ) + 1} : Finset ℂ) →
      1 < ‖z‖ ∧ |z.re| < 1 / 2 ∧ z.im < H)
    (hga : ∀ q ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H),
      AnalyticAt ℂ (cuspFunction 1 ⇑f) q)
    (hgz : ∀ q ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H), q ≠ 0 →
      cuspFunction 1 ⇑f q ≠ 0) :
    ((∑ᶠ q ∈ (fun z : ℂ ↦ (Quotient.mk'' (ofComplex z) :
              MulAction.orbitRel.Quotient SL(2, ℤ) ℍ)) ''
            ↑(T \ ({Complex.I, (ρ : ℂ), (ρ : ℂ) + 1} : Finset ℂ)),
          orderOfVanishingOnOrbit f q : ℤ) : ℂ)
        + 1 / 2 * ((orderOfVanishingAt ⇑f UpperHalfPlane.I : ℤ) : ℂ)
        + 1 / 3 * ((orderOfVanishingAt ⇑f ρ : ℤ) : ℂ)
        + qExpansionOrderAtCusp 1 ⇑f = (k : ℂ) / 12 := by
  have horb : ∑ z ∈ T \ ({Complex.I, (ρ : ℂ), (ρ : ℂ) + 1} : Finset ℂ),
        orderOfVanishingAt (⇑f) (ofComplex z) =
      ∑ᶠ q ∈ (fun z : ℂ ↦ (Quotient.mk'' (ofComplex z) :
            MulAction.orbitRel.Quotient SL(2, ℤ) ℍ)) ''
          ↑(T \ ({Complex.I, (ρ : ℂ), (ρ : ℂ) + 1} : Finset ℂ)),
        orderOfVanishingOnOrbit (k := k) f q :=
    sum_orderOfVanishingAt_ofComplex_eq_finsum_orbit (k := k) f
      (fun z hz => hpos z (Finset.mem_sdiff.mp hz).1)
      (fun z hz => (hin z (Finset.mem_sdiff.mp hz).1 (Finset.mem_sdiff.mp hz).2).1)
      (fun z hz => (hin z (Finset.mem_sdiff.mp hz).1 (Finset.mem_sdiff.mp hz).2).2.1)
  have : SlashInvariantFormClass F ((⊤ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k :=
    MonoidHom.range_eq_map (Matrix.SpecialLinearGroup.mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) ▸ ‹_›
  have key := sum_orderOfVanishingAt_add_elliptic_add_qExpansionOrderAtCusp_eq
    (Γ := ⊤) f (Subgroup.mem_top _) hH hnorm hinv
    (SlashInvariantFormClass.periodic_comp_ofComplex f
      (MonoidHom.range_eq_map (Matrix.SpecialLinearGroup.mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) ▸
        one_mem_strictPeriods_SL)) hoffγ hU hUdom hoff hmero hpos hin hga hgz
  rw [← horb]
  push_cast
  exact key

end ModularForm

end TauCeti

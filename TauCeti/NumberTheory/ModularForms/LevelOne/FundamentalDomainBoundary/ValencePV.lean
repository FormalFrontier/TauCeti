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
import TauCeti.Analysis.Complex.UpperHalfPlane.Rho
import TauCeti.NumberTheory.Modular.Orbits
import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.BoundaryPairing
import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.ExcisionSeparation
import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Interior
import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Containment
import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.OnCurveCapture
import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Winding.NonCorner.Arc
import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Winding.NonCorner.Vertical
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
  principal value of `logDeriv (f ∘ ofComplex)` is `2πi·ord_∞ − k·(π/6)·I`, for a unit-norm
  inversion-closed excision set.
* `hasCauchyPVWith_fdBoundary_logDeriv_arcSingularSet_union_verticalSingularSet` (in
  `TauCeti.ModularForm`): the same principal value for the union-shaped excision set
  `arcSingularSet S ∪ verticalSingularSet S`, which tolerates contour zeros on the vertical
  edges as well as on the arc.
* `TauCeti.ModularForm.two_pi_I_mul_sum_windingNumber_mul_order_eq`: equating either with the
  argument principle gives `2πi·Σ n_z·ord z = 2πi·ord_∞ − k·(π/6)·I`, the analytic identity the
  valence formula rests on.
* `TauCeti.ModularForm.sum_windingNumber_mul_orderOfVanishingAt_eq`: that identity divided by
  `2πi`, giving `Σ n_z·ord z = ord_∞ − k/12`.
* `TauCeti.ModularForm.sum_orderOfVanishingAt_add_qExpansionOrderAtCusp_eq`: the valence formula
  `Σ_q ord_q + ord_∞ = k/12` when every divisor point — zero or pole — lies in the strict
  interior of the truncated fundamental domain.
* `TauCeti.ModularForm.sum_orderOfVanishingAt_add_elliptic_add_qExpansionOrderAtCusp_eq`: the
  valence formula `Σ_int ord_q + Σ_leftVert ord_q + Σ_{leftArc∖ρ} ord_q + ½·ord_i + ⅓·ord_ρ +
  ord_∞ = k/12` for a nonzero level-one form and a divisor set that is complete for the
  closed fundamental domain and confined to it: every point of `𝒟` of nonzero order lies in
  `S` (`hcomp`), and every point of `S` of nonzero order lies in `𝒟` (`hSfd`). The divisor
  may meet the corners, the vertical edges and the unit arc — each boundary pair enters by
  its left representative — and the truncation height and every analytic input are chosen
  internally.
* `finsum_orderOfVanishingOnOrbit_mem_image_add_elliptic_add_qExpansionOrderAtCusp_eq`
  (in `TauCeti.ModularForm`):
  the same identity with the interior sum reindexed over the orbits its points represent. ⚠ That
  sum covers only the orbits met by the divisor set `S`, not the whole non-elliptic orbit space.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) (commit
  `2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, Chris Birkbeck) — the
  valence-formula development. The `ε → 0` step follows
  `ForMathlib/ValenceFormula/PVChain/Assembly.lean` (`cpv_modular_side_tendsto`), the
  identification with the argument principle follows `ForMathlib/ValenceFormulaFinal.lean`,
  and the internal-height threshold assembly follows `valence_formula_general_S_FM` in
  `ForMathlib/ValenceFormula.lean`, all ported onto the current Mathlib pin. The
  two-excision-set formulation and the route through `HasCauchyPV.unique` are Tau Ceti's.
* J.-P. Serre, *A Course in Arithmetic*, VII §3 Theorem 3 — the classical statement and
  contour argument this file formalizes.
-/

public section

open Complex Filter Function MeasureTheory Set Topology UpperHalfPlane

open scoped MatrixGroups Modular Real Manifold

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

/-- Excised integrability on a subinterval of the contour, with the endpoints given
numerically: the along-contour analyticity and non-vanishing off the excision set restrict to
the subinterval. -/
private lemma intervalIntegrable_excised_of_subset {g : ℂ → ℂ} {H ε : ℝ} {Sx : Finset ℂ}
    (hε : 0 < ε) {a b : ℝ} (h0 : 0 ≤ a) (hab : a ≤ b) (h5 : b ≤ 5)
    (hoffγ : ∀ t ∈ Icc (0 : ℝ) 5, fdBoundary H t ∉ Sx →
      AnalyticAt ℂ g (fdBoundary H t) ∧ g (fdBoundary H t) ≠ 0) :
    IntervalIntegrable (fun t ↦ if ∃ s ∈ Sx, ‖fdBoundary H t - s‖ ≤ ε then 0
      else deriv (fdBoundary H) t • logDeriv g (fdBoundary H t)) volume a b := by
  have hsub : uIcc a b ⊆ Icc (0 : ℝ) 5 := by
    rw [uIcc_of_le hab]
    exact Icc_subset_Icc h0 h5
  exact intervalIntegrable_excised_deriv_smul_logDeriv_comp_ofComplex_fdBoundary hε hsub
    fun t ht => hoffγ t (hsub ht)

/-- Off the `ε`-excision the contour point avoids the excision set itself, so the along-contour
analyticity and non-vanishing hypothesis applies to it. -/
private theorem analyticAt_and_ne_zero_of_not_excised {g : ℂ → ℂ} {H : ℝ} {Sx : Finset ℂ}
    (hoffγ : ∀ t ∈ Icc (0 : ℝ) 5, fdBoundary H t ∉ Sx →
      AnalyticAt ℂ g (fdBoundary H t) ∧ g (fdBoundary H t) ≠ 0)
    {ε t : ℝ} (hε : 0 < ε) (hex : ¬(∃ s ∈ Sx, ‖fdBoundary H t - s‖ ≤ ε))
    (ht : t ∈ Icc (0 : ℝ) 5) :
    AnalyticAt ℂ g (fdBoundary H t) ∧ g (fdBoundary H t) ≠ 0 := by
  refine hoffγ t ht fun hs => hex ?_
  exact ⟨_, hs, by rw [sub_self, norm_zero]; exact hε.le⟩

/-- The boundary principal value from an eventual fixed-`ε` identity: once each small-`ε`
excised boundary integral is `c` minus `w/2` times the excised arc integral, the arc limit
`(π/3)·I` makes the boundary principal value `c − w·(π/6)·I`, whatever the excision set. -/
private theorem hasCauchyPVWith_fdBoundary_logDeriv_of_eventually_eq {g : ℂ → ℂ} {H : ℝ}
    {Sx : Finset ℂ} {c w : ℂ}
    (hoffγ : ∀ t ∈ Icc (0 : ℝ) 5, fdBoundary H t ∉ Sx →
      AnalyticAt ℂ g (fdBoundary H t) ∧ g (fdBoundary H t) ≠ 0)
    (heq : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∫ t in (0 : ℝ)..5, if ∃ s ∈ Sx, ‖fdBoundary H t - s‖ ≤ ε then 0
          else logDeriv g (fdBoundary H t) * deriv (fdBoundary H) t) =
        c - w / 2 * ∫ t in (1 : ℝ)..3, (if ∃ s ∈ Sx, ‖fdBoundary H t - s‖ ≤ ε then 0
          else logDeriv (fdBoundary H) t)) :
    Contour.HasCauchyPVWith (fdBoundary H) 0 5 (logDeriv g) Sx
      (c - w * ((Real.pi / 6 : ℝ) * Complex.I)) := by
  refine Contour.hasCauchyPVWith_iff.mpr ⟨?_, ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    simpa only [smul_eq_mul, mul_comm] using
      intervalIntegrable_excised_of_subset hε le_rfl (by norm_num) le_rfl hoffγ
  · refine Tendsto.congr' (Filter.EventuallyEq.symm heq) ?_
    have hval : c - w / 2 * ((Real.pi / 3 : ℝ) * Complex.I) =
        c - w * ((Real.pi / 6 : ℝ) * Complex.I) := by
      push_cast
      ring
    exact hval ▸ (tendsto_const_nhds.sub
      ((tendsto_intervalIntegral_excised_logDeriv_fdBoundary_arc H Sx).const_mul _))

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
  filter_upwards [eventually_forall_im_add_lt hHgt, self_mem_nhdsWithin] with ε hlt hε
  simpa only [smul_eq_mul, mul_comm] using
    intervalIntegral_excised_logDeriv_fdBoundary f hS hnorm hinv hlt hper
      (fun t ht hex => (analyticAt_and_ne_zero_of_not_excised hoffγ hε hex
        ⟨by linarith [ht.1], by linarith [ht.2]⟩).1.differentiableAt)
      (fun t ht hex => (analyticAt_and_ne_zero_of_not_excised hoffγ hε hex
        ⟨by linarith [ht.1], by linarith [ht.2]⟩).2)
      hga hgz
      (intervalIntegrable_excised_of_subset hε le_rfl (by norm_num) (by norm_num) hoffγ)
      (intervalIntegrable_excised_of_subset hε (by norm_num) (by norm_num) (by norm_num) hoffγ)
      (intervalIntegrable_excised_of_subset hε (by norm_num) (by norm_num) le_rfl hoffγ)

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
        (k : ℂ) * ((Real.pi / 6 : ℝ) * Complex.I)) :=
  hasCauchyPVWith_fdBoundary_logDeriv_of_eventually_eq hoffγ
    (eventually_intervalIntegral_excised_eq f hS hnorm hinv hHgt hper hoffγ hga hgz)

/-- The union-excised assembly, packaged as an eventual identity: for all small `ε` the
`arcSingularSet S ∪ verticalSingularSet S`-excised boundary integral is `2πi·ord_∞` minus
`(k/2)` times the excised arc integral. Beyond the ceiling clearance the smallness of `ε` is
what puts it under the arc/vertical separation, so the union assembly's `hfar` holds. -/
private theorem eventually_intervalIntegral_union_excised_eq [SlashInvariantFormClass F Γ k]
    (f : F) (hS : ModularGroup.S ∈ Γ) {H : ℝ} {S : Finset ℍ} (hH : 1 < H)
    (hHgt : ∀ p ∈ S, (p : ℂ).im < H) (hper : Periodic (⇑f ∘ ofComplex) 1)
    (hoffγ : ∀ t ∈ Icc (0 : ℝ) 5,
      fdBoundary H t ∉ arcSingularSet S ∪ verticalSingularSet S →
      AnalyticAt ℂ (⇑f ∘ ofComplex) (fdBoundary H t) ∧ (⇑f ∘ ofComplex) (fdBoundary H t) ≠ 0)
    (hga : ∀ q ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H),
      AnalyticAt ℂ (cuspFunction 1 ⇑f) q)
    (hgz : ∀ q ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H), q ≠ 0 →
      cuspFunction 1 ⇑f q ≠ 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∫ t in (0 : ℝ)..5,
          if ∃ s ∈ arcSingularSet S ∪ verticalSingularSet S, ‖fdBoundary H t - s‖ ≤ ε then 0
          else logDeriv (⇑f ∘ ofComplex) (fdBoundary H t) * deriv (fdBoundary H) t) =
        2 * (Real.pi : ℂ) * Complex.I * qExpansionOrderAtCusp 1 ⇑f -
          (k : ℂ) / 2 * ∫ t in (1 : ℝ)..3,
            (if ∃ s ∈ arcSingularSet S ∪ verticalSingularSet S, ‖fdBoundary H t - s‖ ≤ ε
            then 0 else logDeriv (fdBoundary H) t) := by
  filter_upwards [eventually_forall_im_add_lt fun s hs =>
      im_lt_of_mem_arcSingularSet_union_verticalSingularSet hH hHgt hs,
    eventually_forall_lt_norm_fdBoundary_sub_of_mem_verticalSingularSet H S,
    self_mem_nhdsWithin] with ε hlt hfar hε
  simpa only [smul_eq_mul, mul_comm] using
    intervalIntegral_excised_logDeriv_fdBoundary_arcSingularSet_union_verticalSingularSet f hS
      hfar hlt hper
      (fun t ht hex => (analyticAt_and_ne_zero_of_not_excised hoffγ hε hex
        ⟨by linarith [ht.1], by linarith [ht.2]⟩).1.differentiableAt)
      (fun t ht hex => (analyticAt_and_ne_zero_of_not_excised hoffγ hε hex
        ⟨by linarith [ht.1], by linarith [ht.2]⟩).2)
      hga hgz
      (intervalIntegrable_excised_of_subset hε le_rfl (by norm_num) (by norm_num) hoffγ)
      (intervalIntegrable_excised_of_subset hε (by norm_num) (by norm_num) (by norm_num) hoffγ)
      (intervalIntegrable_excised_of_subset hε (by norm_num) (by norm_num) le_rfl hoffγ)

/-- **The boundary principal value against the union excision set.** The excised integrals
for `arcSingularSet S ∪ verticalSingularSet S` converge as `ε → 0⁺`, to the same constant
`2πi·ord_∞ − k·(π/6)·I` as the unit-norm assembly: the union shape buys tolerance of contour
zeros on the vertical edges as well as on the arc, which is exactly what a divisor set
complete for the closed fundamental domain can force. Compare
`hasCauchyPVWith_fdBoundary_logDeriv_comp_ofComplex`, the unit-norm inversion-closed shape. -/
theorem hasCauchyPVWith_fdBoundary_logDeriv_arcSingularSet_union_verticalSingularSet
    [SlashInvariantFormClass F Γ k] (f : F) (hS : ModularGroup.S ∈ Γ) {H : ℝ} {S : Finset ℍ}
    (hH : 1 < H) (hHgt : ∀ p ∈ S, (p : ℂ).im < H) (hper : Periodic (⇑f ∘ ofComplex) 1)
    (hoffγ : ∀ t ∈ Icc (0 : ℝ) 5,
      fdBoundary H t ∉ arcSingularSet S ∪ verticalSingularSet S →
      AnalyticAt ℂ (⇑f ∘ ofComplex) (fdBoundary H t) ∧ (⇑f ∘ ofComplex) (fdBoundary H t) ≠ 0)
    (hga : ∀ q ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H),
      AnalyticAt ℂ (cuspFunction 1 ⇑f) q)
    (hgz : ∀ q ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H), q ≠ 0 →
      cuspFunction 1 ⇑f q ≠ 0) :
    Contour.HasCauchyPVWith (fdBoundary H) 0 5 (logDeriv (⇑f ∘ ofComplex))
      (arcSingularSet S ∪ verticalSingularSet S)
      (2 * (Real.pi : ℂ) * Complex.I * qExpansionOrderAtCusp 1 ⇑f -
        (k : ℂ) * ((Real.pi / 6 : ℝ) * Complex.I)) :=
  hasCauchyPVWith_fdBoundary_logDeriv_of_eventually_eq hoffγ
    (eventually_intervalIntegral_union_excised_eq f hS hH hHgt hper hoffγ hga hgz)

/-- **The weighted order sum equals the cusp order minus the weight term.** Both sides are the
same Cauchy principal value along the boundary contour: `hasCauchyPV_fdBoundary_logDeriv`
evaluates it by the argument principle, as `2πi` times the winding-weighted sum of orders over
the **divisor** set `T` — orders, not zero-counts: a point of `T` where the form has a pole
contributes negatively, while `hpv` evaluates it by an excised assembly, excising some
**boundary** set. Principal values are unique even across different excision sets, so the two
agree.

Keeping the excision set and `T` separate is what makes the statement useful: the assemblies
constrain their excision sets — to the unit circle
(`hasCauchyPVWith_fdBoundary_logDeriv_comp_ofComplex`) or to the two singular families
(`hasCauchyPVWith_fdBoundary_logDeriv_arcSingularSet_union_verticalSingularSet`) — whereas the
divisor set is unrestricted, so zeros in the interior are allowed.

This is the analytic identity the valence formula rests on: dividing by `2πi` and reading off the
corner winding numbers — which are **negative**, the contour running clockwise: `-(1/2)` at `i`
and `-(1/6)` at each `ρ`-corner, against `-1` at an interior point — turns it into
`ord_∞ + ½·ord_i + ⅓·ord_ρ + Σ ord_q = k/12`. -/
theorem two_pi_I_mul_sum_windingNumber_mul_order_eq (g : ℍ → ℂ) {H : ℝ} {Sx T : Finset ℂ}
    {U : Set ℂ} {ord : ℂ → ℤ} (hH : 1 ≤ H)
    (hpv : Contour.HasCauchyPVWith (fdBoundary H) 0 5 (logDeriv (g ∘ ofComplex)) Sx
      (2 * (Real.pi : ℂ) * Complex.I * qExpansionOrderAtCusp 1 g -
        (k : ℂ) * ((Real.pi / 6 : ℝ) * Complex.I)))
    (hU : IsOpen U)
    (hUdom : UpperHalfPlane.coe '' ModularGroup.truncatedFundamentalDomain H ⊆ U)
    (hoff : ∀ z ∈ U, z ∉ T → AnalyticAt ℂ (g ∘ ofComplex) z ∧ (g ∘ ofComplex) z ≠ 0)
    (hmero : ∀ s ∈ T, s ∈ U → MeromorphicAt (g ∘ ofComplex) s)
    (hord : ∀ s ∈ T, s ∈ U → meromorphicOrderAt (g ∘ ofComplex) s = (ord s : WithTop ℤ))
    (hbase : fdBoundary H 0 ∉ (T : Set ℂ)) :
    2 * (Real.pi : ℂ) * Complex.I *
        ∑ z ∈ T, Contour.windingNumber (fdBoundary H) 0 5 z * (ord z : ℂ) =
      2 * (Real.pi : ℂ) * Complex.I * qExpansionOrderAtCusp 1 g -
        (k : ℂ) * ((Real.pi / 6 : ℝ) * Complex.I) :=
  (hasCauchyPV_fdBoundary_logDeriv hH hU hUdom hoff hmero hord hbase).unique hpv.hasCauchyPV

/-- **The weighted order sum in terms of `orderOfVanishingAt`.** With the divisor points in the
upper half plane, the abstract order function of `two_pi_I_mul_sum_windingNumber_mul_order_eq` is
the modular-forms order at each of them.

`orderOfVanishingAt` is by definition the meromorphic order of `f ∘ ofComplex`
(`orderOfVanishingAt_def`), so the abstract hypothesis asks only that those orders be finite —
which `hoff` and the finiteness of `T` already force, so no separate hypothesis is needed. The
sum runs over `T.attach` because the order is taken at each divisor point *as a point of `ℍ`*,
which needs its membership proof. -/
private theorem two_pi_I_mul_sum_windingNumber_mul_orderOfVanishingAt_eq (g : ℍ → ℂ) {H : ℝ}
    {Sx T : Finset ℂ} {U : Set ℂ} (hH : 1 ≤ H)
    (hpv : Contour.HasCauchyPVWith (fdBoundary H) 0 5 (logDeriv (g ∘ ofComplex)) Sx
      (2 * (Real.pi : ℂ) * Complex.I * qExpansionOrderAtCusp 1 g -
        (k : ℂ) * ((Real.pi / 6 : ℝ) * Complex.I)))
    (hU : IsOpen U)
    (hUdom : UpperHalfPlane.coe '' ModularGroup.truncatedFundamentalDomain H ⊆ U)
    (hoff : ∀ z ∈ U, z ∉ T → AnalyticAt ℂ (g ∘ ofComplex) z ∧ (g ∘ ofComplex) z ≠ 0)
    (hmero : ∀ s ∈ T, s ∈ U → MeromorphicAt (g ∘ ofComplex) s)
    (hpos : ∀ s ∈ T, 0 < s.im) (hbase : fdBoundary H 0 ∉ (T : Set ℂ)) :
    2 * (Real.pi : ℂ) * Complex.I *
        ∑ z ∈ T.attach, Contour.windingNumber (fdBoundary H) 0 5 (z : ℂ) *
          ((orderOfVanishingAt g ⟨(z : ℂ), hpos _ z.2⟩ : ℤ) : ℂ) =
      2 * (Real.pi : ℂ) * Complex.I * qExpansionOrderAtCusp 1 g -
        (k : ℂ) * ((Real.pi / 6 : ℝ) * Complex.I) := by
  have hsummand : ∀ z ∈ T.attach,
      Contour.windingNumber (fdBoundary H) 0 5 (z : ℂ) *
          ((orderOfVanishingAt g ⟨(z : ℂ), hpos _ z.2⟩ : ℤ) : ℂ) =
        Contour.windingNumber (fdBoundary H) 0 5 (z : ℂ) *
          (((meromorphicOrderAt (g ∘ ofComplex) (z : ℂ)).untop₀ : ℤ) : ℂ) := by
    intro z _
    rw [orderOfVanishingAt_def]
  rw [Finset.sum_congr rfl hsummand,
    Finset.sum_attach T fun z => Contour.windingNumber (fdBoundary H) 0 5 z *
      (((meromorphicOrderAt (g ∘ ofComplex) z).untop₀ : ℤ) : ℂ)]
  exact two_pi_I_mul_sum_windingNumber_mul_order_eq g hH hpv hU hUdom
    hoff hmero (fun s hsT hsU => (WithTop.coe_untop₀_of_ne_top
      ((meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hmero s hsT hsU)).2 (by
        filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hsU),
          T.eventually_cofinite_notMem.filter_mono (nhdsNE_le_cofinite s)] with z hzU hzT
        exact (hoff z hzU hzT).2))).symm) hbase

/-- **The valence identity, divided through.** Cancelling the common factor `2πi` puts the
identity in the shape the valence formula is usually written in: the winding-weighted sum of
orders inside the contour equals the cusp order minus `k/12`. The orders are meromorphic orders,
so a pole contributes negatively.

The weight term matches because `k·(π/6)·I = 2πi·(k/12)`. -/
theorem sum_windingNumber_mul_orderOfVanishingAt_eq (g : ℍ → ℂ) {H : ℝ} {Sx T : Finset ℂ}
    {U : Set ℂ} (hH : 1 ≤ H)
    (hpv : Contour.HasCauchyPVWith (fdBoundary H) 0 5 (logDeriv (g ∘ ofComplex)) Sx
      (2 * (Real.pi : ℂ) * Complex.I * qExpansionOrderAtCusp 1 g -
        (k : ℂ) * ((Real.pi / 6 : ℝ) * Complex.I)))
    (hU : IsOpen U)
    (hUdom : UpperHalfPlane.coe '' ModularGroup.truncatedFundamentalDomain H ⊆ U)
    (hoff : ∀ z ∈ U, z ∉ T → AnalyticAt ℂ (g ∘ ofComplex) z ∧ (g ∘ ofComplex) z ≠ 0)
    (hmero : ∀ s ∈ T, s ∈ U → MeromorphicAt (g ∘ ofComplex) s)
    (hpos : ∀ s ∈ T, 0 < s.im) (hbase : fdBoundary H 0 ∉ (T : Set ℂ)) :
    ∑ z ∈ T.attach, Contour.windingNumber (fdBoundary H) 0 5 (z : ℂ) *
        ((orderOfVanishingAt g ⟨(z : ℂ), hpos _ z.2⟩ : ℤ) : ℂ) =
      qExpansionOrderAtCusp 1 g - (k : ℂ) / 12 := by
  refine mul_left_cancel₀ Complex.two_pi_I_ne_zero ?_
  rw [two_pi_I_mul_sum_windingNumber_mul_orderOfVanishingAt_eq g hH hpv
    hU hUdom hoff hmero hpos hbase]
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
  have := sum_windingNumber_mul_orderOfVanishingAt_eq ⇑f hH.le
    (hasCauchyPVWith_fdBoundary_logDeriv_comp_ofComplex f hS hnorm hinv hHgt hper hoffγ hga hgz)
    hU hUdom hoff hmero hpos hbase
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


/-- A corner the divisor set misses has order `0`: the corners lie in the closed fundamental
domain, so a nonzero order would put them into any complete set. -/
private lemma orderOfVanishingAt_corner_eq_zero {f : ℍ → ℂ} {S : Finset ℍ}
    (hcomp : ∀ p, p ∈ 𝒟 → orderOfVanishingAt f p ≠ 0 → p ∈ S) {c : ℍ}
    (hc : c = UpperHalfPlane.I ∨ c = ρ ∨ c = (1 : ℝ) +ᵥ ρ) (hcS : c ∉ S) :
    orderOfVanishingAt f c = 0 := by
  by_contra hne
  refine hcS (hcomp c ?_ hne)
  rcases hc with rfl | rfl | rfl
  exacts [ModularGroup.I_mem_fd, ModularGroup.ρ_mem_fd,
    vadd_mem_fd_of_re_eq (by norm_num) ModularGroup.ρ_mem_fd (by norm_num)]

/-- The `ℂ`-corner classification transfers along the coercion: a point of `ℍ` lands on
`{i, ρ, ρ + 1}` in `ℂ` exactly when it is one of the three corner points of `ℍ`. -/
private lemma coe_mem_corner_iff {p : ℍ} :
    (p : ℂ) ∈ ({Complex.I, (ρ : ℂ), (ρ : ℂ) + 1} : Finset ℂ) ↔
      p = UpperHalfPlane.I ∨ p = ρ ∨ p = (1 : ℝ) +ᵥ ρ := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h | h)
    · exact Or.inl (UpperHalfPlane.coe_injective (h.trans UpperHalfPlane.coe_I.symm))
    · exact Or.inr (Or.inl (UpperHalfPlane.coe_injective h))
    · exact Or.inr (Or.inr (UpperHalfPlane.coe_injective (h.trans coe_vadd_one_ρ.symm)))
  · rintro (rfl | rfl | rfl)
    · exact Or.inl UpperHalfPlane.coe_I
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr coe_vadd_one_ρ)

/-- The corner contribution to the winding-weighted divisor sum: `-(1/2)·ord_i - ⅓·ord_ρ`.
The two `ρ`-corners weigh `-(1/6)` each and carry the same order by periodicity; a corner the
set misses carries order `0` by completeness. -/
private lemma sum_filter_corner_windingNumber_mul_order {f : ℍ → ℂ} {H : ℝ} {S : Finset ℍ}
    (hH : 1 < H) (hper : Periodic (f ∘ ofComplex) 1)
    (hcomp : ∀ p, p ∈ 𝒟 → orderOfVanishingAt f p ≠ 0 → p ∈ S) :
    ∑ p ∈ (S.filter fun p : ℍ ↦ orderOfVanishingAt f p ≠ 0).filter
        (fun p : ℍ ↦ (p : ℂ) ∈ ({Complex.I, (ρ : ℂ), (ρ : ℂ) + 1} : Finset ℂ)),
        Contour.windingNumber (fdBoundary H) 0 5 (p : ℂ) *
          ((orderOfVanishingAt f p : ℤ) : ℂ) =
      -(1 / 2) * ((orderOfVanishingAt f UpperHalfPlane.I : ℤ) : ℂ) -
        1 / 3 * ((orderOfVanishingAt f ρ : ℤ) : ℂ) := by
  classical
  have hρH : Real.sqrt 3 / 2 < H := sqrt_three_div_two_lt_one.trans hH
  have hordρ₁ : orderOfVanishingAt f ((1 : ℝ) +ᵥ ρ) = orderOfVanishingAt f ρ :=
    orderOfVanishingAt_eq_of_coe_eq_add hper (by rw [coe_vadd_one_ρ, add_comm])
  have hsub : (S.filter fun p : ℍ ↦ orderOfVanishingAt f p ≠ 0).filter
      (fun p : ℍ ↦ (p : ℂ) ∈ ({Complex.I, (ρ : ℂ), (ρ : ℂ) + 1} : Finset ℂ)) ⊆
      ({UpperHalfPlane.I, ρ, (1 : ℝ) +ᵥ ρ} : Finset ℍ) := fun p hp => by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact coe_mem_corner_iff.mp (Finset.mem_filter.mp hp).2
  have hmiss : ∀ c ∈ ({UpperHalfPlane.I, ρ, (1 : ℝ) +ᵥ ρ} : Finset ℍ),
      c ∉ (S.filter fun p : ℍ ↦ orderOfVanishingAt f p ≠ 0).filter
        (fun p : ℍ ↦ (p : ℂ) ∈ ({Complex.I, (ρ : ℂ), (ρ : ℂ) + 1} : Finset ℂ)) →
      Contour.windingNumber (fdBoundary H) 0 5 (c : ℂ) *
        ((orderOfVanishingAt f c : ℤ) : ℂ) = 0 := by
    intro c hc hcn
    have hc' : c = UpperHalfPlane.I ∨ c = ρ ∨ c = (1 : ℝ) +ᵥ ρ := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hc
    rcases Decidable.em (orderOfVanishingAt f c = 0) with h0 | h0
    · rw [h0]
      simp
    · rw [orderOfVanishingAt_corner_eq_zero hcomp hc' fun hmem => hcn (Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨hmem, h0⟩, coe_mem_corner_iff.mpr hc'⟩)]
      simp
  rw [Finset.sum_subset hsub hmiss,
    Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_singleton,
    UpperHalfPlane.coe_I, coe_vadd_one_ρ,
    windingNumber_fdBoundary_arc hH (by norm_num) (by norm_num) (by norm_num),
    windingNumber_fdBoundary_rho hρH, windingNumber_fdBoundary_rho_add_one hρH, hordρ₁]
  ring

/-- **The non-corner boundary weight.** A point of the closed fundamental domain that is
neither a corner nor strictly interior lies on a vertical edge or on the open arc, where the
boundary contour winds `-1/2`. -/
private lemma windingNumber_coe_eq_neg_half {H : ℝ} {p : ℍ} (hH : 1 < H) (hp : p ∈ 𝒟)
    (hc : (p : ℂ) ∉ ({Complex.I, (ρ : ℂ), (ρ : ℂ) + 1} : Finset ℂ))
    (hint : ¬(1 < ‖(p : ℂ)‖ ∧ |(p : ℂ).re| < 1 / 2)) (him : (p : ℂ).im < H) :
    Contour.windingNumber (fdBoundary H) 0 5 (p : ℂ) = -(1 / 2 : ℂ) := by
  rcases (mem_boundary_iff hp).mp ⟨hc, hint⟩ with ⟨hre, hgt⟩ | ⟨hre, hgt⟩ |
    ⟨hne, hnorm, hpos⟩ | ⟨hne, hnorm, hneg⟩
  · exact windingNumber_fdBoundary_vertical (by rw [← one_div]; exact Or.inl hre) hgt p.2 him
  · exact windingNumber_fdBoundary_vertical (by rw [← one_div]; exact Or.inr hre) hgt p.2 him
  · refine windingNumber_fdBoundary_arc hH hnorm ?_ p.2
    rw [← one_div, abs_lt]
    exact ⟨by linarith, lt_of_le_of_ne (abs_le.mp hp.2).2 fun h =>
      hne ((congrArg _ (eq_vadd_one_ρ_of_re_eq_half hnorm h)).trans coe_vadd_one_ρ)⟩
  · refine windingNumber_fdBoundary_arc hH hnorm ?_ p.2
    rw [← one_div, abs_lt]
    exact ⟨lt_of_le_of_ne (abs_le.mp hp.2).1 fun h =>
      hne (congrArg _ (eq_ρ_of_re_eq_neg_half hnorm h.symm)), by linarith⟩

/-- Restricting a family sum to the nonzero-order points does not change it. -/
private lemma sum_filter_orderOfVanishingAt_ne_zero {f : ℍ → ℂ} {S : Finset ℍ}
    (P : ℍ → Prop) [DecidablePred P] :
    ∑ p ∈ (S.filter fun p : ℍ ↦ orderOfVanishingAt f p ≠ 0).filter P,
        ((orderOfVanishingAt f p : ℤ) : ℂ) =
      ∑ p ∈ S.filter P, ((orderOfVanishingAt f p : ℤ) : ℂ) := by
  rw [Finset.filter_comm]
  exact Finset.sum_filter_of_ne fun p _ hne => Int.cast_ne_zero.mp hne

/-- The boundary aggregate over the nonzero-order points, paired into left representatives:
completeness matches each right half-edge with its left partner, so the non-elliptic boundary
sum is twice the left-representative sum. -/
private lemma sum_filter_boundary_orderOfVanishingAt_eq [SlashInvariantFormClass F Γ k] (f : F)
    (hSmem : ModularGroup.S ∈ Γ) {S : Finset ℍ} (hper : Periodic (⇑f ∘ ofComplex) 1)
    (hSfd : ∀ p ∈ S, orderOfVanishingAt ⇑f p ≠ 0 → p ∈ 𝒟)
    (hcomp : ∀ p, p ∈ 𝒟 → orderOfVanishingAt ⇑f p ≠ 0 → p ∈ S) :
    ∑ p ∈ (S.filter fun p : ℍ ↦ orderOfVanishingAt ⇑f p ≠ 0).filter
        (fun p : ℍ ↦ (p : ℂ) ∉ ({Complex.I, (ρ : ℂ), (ρ : ℂ) + 1} : Finset ℂ) ∧
          ¬(1 < ‖(p : ℂ)‖ ∧ |(p : ℂ).re| < 1 / 2)),
        ((orderOfVanishingAt ⇑f p : ℤ) : ℂ) =
      2 * (∑ p ∈ S.filter (fun p : ℍ ↦ (p : ℂ).re = -(1 / 2) ∧ 1 < ‖(p : ℂ)‖),
          ((orderOfVanishingAt ⇑f p : ℤ) : ℂ) +
        ∑ p ∈ S.filter (fun p : ℍ ↦ (p : ℂ) ≠ (ρ : ℂ) ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0),
          ((orderOfVanishingAt ⇑f p : ℤ) : ℂ)) := by
  rw [sum_filter_orderOfVanishingAt_ne_zero]
  exact_mod_cast congrArg (Int.cast : ℤ → ℂ)
    (sum_orderOfVanishingAt_nonEllipticBoundary_eq_two_mul f hper hSmem hSfd hcomp)

/-- A strictly interior point is not a corner: the corners sit on the unit circle. -/
private lemma notMem_corner_of_interior {p : ℍ}
    (hp : 1 < ‖(p : ℂ)‖ ∧ |(p : ℂ).re| < 1 / 2) :
    (p : ℂ) ∉ ({Complex.I, (ρ : ℂ), (ρ : ℂ) + 1} : Finset ℂ) := by
  intro hmem
  have h1 : ‖(p : ℂ)‖ = 1 := norm_eq_one_of_mem_ellipticPoints hmem
  rw [h1] at hp
  exact lt_irrefl 1 hp.1

/-- The pointwise winding weight off the corners: `-1` in the interior, `-1/2` on the
boundary, packaged as the `if` the sum below splits along. -/
private lemma windingNumber_mul_order_ite {f : ℍ → ℂ} {H : ℝ} {S : Finset ℍ} (hH : 1 < H)
    (hSfd : ∀ p ∈ S, orderOfVanishingAt f p ≠ 0 → p ∈ 𝒟)
    (hHgt : ∀ p ∈ S, (p : ℂ).im < H) :
    ∀ p ∈ (S.filter fun p : ℍ ↦ orderOfVanishingAt f p ≠ 0).filter
      (fun p : ℍ ↦ (p : ℂ) ∉ ({Complex.I, (ρ : ℂ), (ρ : ℂ) + 1} : Finset ℂ)),
      Contour.windingNumber (fdBoundary H) 0 5 (p : ℂ) * ((orderOfVanishingAt f p : ℤ) : ℂ) =
        if 1 < ‖(p : ℂ)‖ ∧ |(p : ℂ).re| < 1 / 2
        then -((orderOfVanishingAt f p : ℤ) : ℂ)
        else -(1 / 2) * ((orderOfVanishingAt f p : ℤ) : ℂ) := by
  intro p hp
  obtain ⟨hp', hpc⟩ := Finset.mem_filter.mp hp
  obtain ⟨hpS, hpne⟩ := Finset.mem_filter.mp hp'
  split_ifs with h
  · rw [windingNumber_fdBoundary_eq_neg_one_of_interior hH h.1 h.2 p.2 (hHgt p hpS),
      neg_one_mul]
  · rw [windingNumber_coe_eq_neg_half hH (hSfd p hpS hpne) hpc h (hHgt p hpS)]

/-- Inside the non-corner family the interior filter absorbs the corner filter: interior
points are off the unit circle, where the corners sit. -/
private lemma filter_filter_interior_eq {f : ℍ → ℂ} {S : Finset ℍ} :
    ((S.filter fun p : ℍ ↦ orderOfVanishingAt f p ≠ 0).filter
      (fun p : ℍ ↦ (p : ℂ) ∉ ({Complex.I, (ρ : ℂ), (ρ : ℂ) + 1} : Finset ℂ))).filter
      (fun p : ℍ ↦ 1 < ‖(p : ℂ)‖ ∧ |(p : ℂ).re| < 1 / 2) =
      (S.filter fun p : ℍ ↦ orderOfVanishingAt f p ≠ 0).filter
        (fun p : ℍ ↦ 1 < ‖(p : ℂ)‖ ∧ |(p : ℂ).re| < 1 / 2) := by
  ext q
  simp only [Finset.mem_filter, and_assoc]
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2.2⟩,
    fun h => ⟨h.1, h.2.1, notMem_corner_of_interior h.2.2, h.2.2⟩⟩

/-- **The winding-weighted divisor sum over a complete set, evaluated.** The corners weigh
`-(1/2)` at `i` and `-(1/6)` at each `ρ`-corner (merging into `-⅓` at `ρ` by periodicity),
interior points weigh `-1`, and the non-elliptic boundary points weigh `-1/2` and pair into
left representatives, each pair contributing one full-weight representative. -/
private lemma sum_windingNumber_mul_orderOfVanishingAt_coe_eq [SlashInvariantFormClass F Γ k]
    (f : F) (hSmem : ModularGroup.S ∈ Γ) {H : ℝ} {S : Finset ℍ} (hH : 1 < H)
    (hper : Periodic (⇑f ∘ ofComplex) 1)
    (hSfd : ∀ p ∈ S, orderOfVanishingAt ⇑f p ≠ 0 → p ∈ 𝒟)
    (hcomp : ∀ p, p ∈ 𝒟 → orderOfVanishingAt ⇑f p ≠ 0 → p ∈ S)
    (hHgt : ∀ p ∈ S, (p : ℂ).im < H) :
    ∑ p ∈ S, Contour.windingNumber (fdBoundary H) 0 5 (p : ℂ) *
        ((orderOfVanishingAt ⇑f p : ℤ) : ℂ) =
      -(∑ p ∈ S.filter (fun p : ℍ ↦ 1 < ‖(p : ℂ)‖ ∧ |(p : ℂ).re| < 1 / 2),
            ((orderOfVanishingAt ⇑f p : ℤ) : ℂ)
          + ∑ p ∈ S.filter (fun p : ℍ ↦ (p : ℂ).re = -(1 / 2) ∧ 1 < ‖(p : ℂ)‖),
            ((orderOfVanishingAt ⇑f p : ℤ) : ℂ)
          + ∑ p ∈ S.filter (fun p : ℍ ↦ (p : ℂ) ≠ (ρ : ℂ) ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0),
            ((orderOfVanishingAt ⇑f p : ℤ) : ℂ)
          + 1 / 2 * ((orderOfVanishingAt ⇑f UpperHalfPlane.I : ℤ) : ℂ)
          + 1 / 3 * ((orderOfVanishingAt ⇑f ρ : ℤ) : ℂ)) := by
  classical
  -- Restrict to the nonzero-order points, then split the three corner points from the rest.
  rw [← Finset.sum_filter_of_ne (p := fun p : ℍ ↦ orderOfVanishingAt ⇑f p ≠ 0)
      fun p _ h => Int.cast_ne_zero.mp (right_ne_zero_of_mul h),
    ← Finset.sum_filter_add_sum_filter_not (S.filter fun p : ℍ ↦ orderOfVanishingAt ⇑f p ≠ 0)
      (fun p : ℍ ↦ (p : ℂ) ∈ ({Complex.I, (ρ : ℂ), (ρ : ℂ) + 1} : Finset ℂ))]
  -- The corner block evaluates to the two weighted elliptic orders.
  rw [sum_filter_corner_windingNumber_mul_order hH hper hcomp]
  -- Off the corners the winding weight is `-1` on the interior and `-1/2` on the boundary;
  -- the boundary half then pairs into full-weight left representatives.
  rw [Finset.sum_congr rfl (windingNumber_mul_order_ite hH hSfd hHgt), Finset.sum_ite,
    Finset.sum_neg_distrib, filter_filter_interior_eq,
    sum_filter_orderOfVanishingAt_ne_zero (fun p : ℍ ↦ 1 < ‖(p : ℂ)‖ ∧ |(p : ℂ).re| < 1 / 2),
    ← Finset.mul_sum, Finset.filter_filter,
    sum_filter_boundary_orderOfVanishingAt_eq (k := k) f hSmem hper hSfd hcomp]
  ring


/-- Along the contour, off the union of the two singular sets, a nonzero level-one form is
analytic and nonvanishing: analyticity is holomorphy transported through `ofComplex`, and a
vanishing contour point would be captured into the union by
`fdBoundary_mem_arcSingularSet_union_verticalSingularSet_of_comp_eq_zero`. -/
private lemma analyticAt_comp_ofComplex_and_ne_zero_of_notMem [ModularFormClass F 𝒮ℒ k] {f : F}
    (hf : (⇑f : ℍ → ℂ) ≠ 0) {H : ℝ} {S : Finset ℍ} (hH : 1 ≤ H)
    (hcomp : ∀ p, p ∈ 𝒟 → orderOfVanishingAt ⇑f p ≠ 0 → p ∈ S)
    (hHgt : ∀ p ∈ S, (p : ℂ).im < H) :
    ∀ t ∈ Icc (0 : ℝ) 5, fdBoundary H t ∉ arcSingularSet S ∪ verticalSingularSet S →
      AnalyticAt ℂ (⇑f ∘ ofComplex) (fdBoundary H t) ∧
        (⇑f ∘ ofComplex) (fdBoundary H t) ≠ 0 := by
  intro t ht hmem
  obtain ⟨q, -, hqe⟩ := fdBoundary_mem_coe_truncatedFundamentalDomain hH ht
  refine ⟨UpperHalfPlane.analyticAt_comp_ofComplex (ModularFormClass.holo f) ?_,
    fun h0 => hmem
      (fdBoundary_mem_arcSingularSet_union_verticalSingularSet_of_comp_eq_zero hf hcomp hH
        hHgt ht h0)⟩
  rw [← hqe]
  exact q.2

/-- The image of a divisor set of upper half-plane points lies above the real axis. -/
private lemma im_pos_of_mem_image {S : Finset ℍ} :
    ∀ z ∈ S.image ((↑·) : ℍ → ℂ), 0 < z.im := by
  simp only [Finset.mem_image]
  rintro z ⟨p, -, rfl⟩
  exact p.2

/-- The basepoint of the contour sits at height `H`, above every point of a height-bounded
divisor set. -/
private lemma fdBoundary_zero_notMem_image {H : ℝ} {S : Finset ℍ}
    (hHgt : ∀ p ∈ S, (p : ℂ).im < H) :
    fdBoundary H 0 ∉ ((S.image ((↑·) : ℍ → ℂ)) : Set ℂ) := by
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
  rintro ⟨p, hp, he⟩
  have him : (fdBoundary H 0).im = H := by rw [fdBoundary_apply_zero]; simp
  rw [← he] at him
  exact absurd him (ne_of_lt (hHgt p hp))

/-- Off a set capturing the confined zeros, the transported form is analytic and nonzero:
analyticity is holomorphy transported through `ofComplex`, and a zero of `g ∘ ofComplex`
inside `U` must already lie in the truncated fundamental domain, where completeness of `T`
puts it in `T`. -/
private lemma analyticAt_comp_ofComplex_and_ne_zero_of_notMem_of_zeros_confined {g : ℍ → ℂ}
    (hg : MDiff g) {U : Set ℂ} {T : Finset ℂ} {H : ℝ}
    (hUsub : U ⊆ {z : ℂ | 0 < z.im})
    (hUZ : {z ∈ U | (g ∘ ofComplex) z = 0} =
      {z ∈ UpperHalfPlane.coe '' ModularGroup.truncatedFundamentalDomain H |
        (g ∘ ofComplex) z = 0})
    (hT : ∀ z ∈ UpperHalfPlane.coe '' ModularGroup.truncatedFundamentalDomain H,
      (g ∘ ofComplex) z = 0 → z ∈ T) :
    ∀ z ∈ U, z ∉ T → AnalyticAt ℂ (g ∘ ofComplex) z ∧ (g ∘ ofComplex) z ≠ 0 := by
  intro z hzU hzT
  refine ⟨UpperHalfPlane.analyticAt_comp_ofComplex hg (hUsub hzU), fun h0 ↦ hzT ?_⟩
  have hz := hUZ.subset (⟨hzU, h0⟩ : z ∈ {z ∈ U | (g ∘ ofComplex) z = 0})
  exact hT z hz.1 hz.2


/-- **The valence formula, with the elliptic points.** The divisor set `S` is now a finite set
of upper half-plane points, *complete* for the closed fundamental domain: every point of `𝒟`
of nonzero order belongs to it. Nothing confines the divisor to the interior — it may meet the
corners, the vertical edges and the unit arc, because the excised assembly tolerates contour
zeros anywhere the completeness hypothesis can force them.

The count splits by winding weight. The corners weigh `-(1/2)` at `i` and `-(1/6)` at each
`ρ`-corner, and periodicity merges the two `⅙`s; interior points weigh `-1`; every other
boundary point weighs `-1/2` and pairs with its partner under `z ↦ z + 1` (verticals) or
`z ↦ -1/z` (arc), so each pair enters as one full-weight *left* representative:

`Σ_int ord_q + Σ_leftVert ord_q + Σ_{leftArc∖ρ} ord_q + ½·ord_i + ⅓·ord_ρ + ord_∞ = k/12`.

The statement shape follows `valence_formula_textbook_unconditional_FM` in
`ValenceFormulaBridged.lean` of AINTLIB (github.com/CBirkbeck/AINTLIB, revision
2baa76f742bdb4fb8ee323fabba41203bd390e08), with the filter vocabulary of `BoundaryPairing`.

Only the cusp-function non-vanishing `hgz` remains an analytic hypothesis — it holds only
above a height threshold, so this fixed-`H` statement cannot construct it. The zero-confining
neighbourhood and the cusp-function analyticity are built internally
(`UpperHalfPlane.exists_isOpen_zeros_inter` with
`analyticAt_comp_ofComplex_and_ne_zero_of_notMem_of_zeros_confined`, and
`analyticAt_cuspFunction_of_mem_closedBall`) — the confinement's capture hypothesis is handed
to it by completeness over the closed domain (`hcomp`), with `hSfd` confining `S` back into
`𝒟` — while the
along-contour non-vanishing that the excised assembly needs is *derived*: a contour zero is a
nonzero-order point of the truncated fundamental domain, so completeness captures it into
`arcSingularSet S ∪ verticalSingularSet S`
(`fdBoundary_mem_arcSingularSet_union_verticalSingularSet_of_comp_eq_zero`), which is exactly
the set the assembly excises. That capture argument is what forces `f` to be a genuine
level-one modular form here rather than an abstract slash-invariant one. -/
private theorem sum_orderOfVanishingAt_add_elliptic_add_qExpansionOrderAtCusp_eq_of_im_lt
    [ModularFormClass F 𝒮ℒ k] (f : F) (hf : (⇑f : ℍ → ℂ) ≠ 0) {H : ℝ} {S : Finset ℍ}
    (hH : 1 < H)
    (hSfd : ∀ p ∈ S, orderOfVanishingAt ⇑f p ≠ 0 → p ∈ 𝒟)
    (hcomp : ∀ p, p ∈ 𝒟 → orderOfVanishingAt ⇑f p ≠ 0 → p ∈ S)
    (hHgt : ∀ p ∈ S, (p : ℂ).im < H)
    (hgz : ∀ q ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H), q ≠ 0 →
      cuspFunction 1 ⇑f q ≠ 0) :
    ∑ p ∈ S.filter (fun p : ℍ ↦ 1 < ‖(p : ℂ)‖ ∧ |(p : ℂ).re| < 1 / 2),
          ((orderOfVanishingAt ⇑f p : ℤ) : ℂ)
        + ∑ p ∈ S.filter (fun p : ℍ ↦ (p : ℂ).re = -(1 / 2) ∧ 1 < ‖(p : ℂ)‖),
          ((orderOfVanishingAt ⇑f p : ℤ) : ℂ)
        + ∑ p ∈ S.filter (fun p : ℍ ↦ (p : ℂ) ≠ (ρ : ℂ) ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0),
          ((orderOfVanishingAt ⇑f p : ℤ) : ℂ)
        + 1 / 2 * ((orderOfVanishingAt ⇑f UpperHalfPlane.I : ℤ) : ℂ)
        + 1 / 3 * ((orderOfVanishingAt ⇑f ρ : ℤ) : ℂ)
        + qExpansionOrderAtCusp 1 ⇑f = (k : ℂ) / 12 := by
  have hper : Periodic (⇑f ∘ ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL
  have hg : MDiff (⇑f : ℍ → ℂ) := ModularFormClass.holo f
  obtain ⟨U, hU, hUdom, hUsub, hUZ⟩ := UpperHalfPlane.exists_isOpen_zeros_inter hg hf
    (K := UpperHalfPlane.coe '' ModularGroup.truncatedFundamentalDomain H)
    (image_subset_iff.mpr fun p _ ↦ p.im_pos)
  have hoff : ∀ z ∈ U, z ∉ S.image ((↑·) : ℍ → ℂ) →
      AnalyticAt ℂ (⇑f ∘ ofComplex) z ∧ (⇑f ∘ ofComplex) z ≠ 0 := by
    refine analyticAt_comp_ofComplex_and_ne_zero_of_notMem_of_zeros_confined hg hUsub hUZ ?_
    rintro z ⟨q, hq, rfl⟩ h0
    exact Finset.mem_image_of_mem _ (hcomp q hq.1 (orderOfVanishingAt_ne_zero_of_eq_zero hg hf
      (by simpa [Function.comp_apply, ofComplex_apply] using h0)))
  have hga : ∀ q ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H),
      AnalyticAt ℂ (cuspFunction 1 ⇑f) q :=
    analyticAt_cuspFunction_of_mem_closedBall f (zero_lt_one.trans hH)
  have hoffγU := analyticAt_comp_ofComplex_and_ne_zero_of_notMem (k := k) hf hH.le hcomp hHgt
  -- Only the slash-invariant class is transported to the `⊤`-shaped subgroup: a `map`-shaped
  -- `ModularFormClass` instance would shadow the `𝒮ℒ`-shaped searches above.
  have : SlashInvariantFormClass F ((⊤ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k :=
    MonoidHom.range_eq_map (Matrix.SpecialLinearGroup.mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) ▸
      inferInstance
  have key := sum_windingNumber_mul_orderOfVanishingAt_eq ⇑f hH.le
    (hasCauchyPVWith_fdBoundary_logDeriv_arcSingularSet_union_verticalSingularSet
      (Γ := (⊤ : Subgroup SL(2, ℤ))) (k := k) f (Subgroup.mem_top _) hH hHgt hper hoffγU hga hgz)
    hU hUdom hoff
    (fun s hs _ =>
      (UpperHalfPlane.analyticAt_comp_ofComplex hg (im_pos_of_mem_image s hs)).meromorphicAt)
    im_pos_of_mem_image (fdBoundary_zero_notMem_image hHgt)
  rw [sum_attach_mul_orderOfVanishingAt im_pos_of_mem_image
      (Contour.windingNumber (fdBoundary H) 0 5),
    Finset.sum_image fun p _ q _ h => UpperHalfPlane.coe_injective h] at key
  simp only [ofComplex_apply] at key
  rw [sum_windingNumber_mul_orderOfVanishingAt_coe_eq (Γ := (⊤ : Subgroup SL(2, ℤ))) (k := k) f
      (Subgroup.mem_top _) hH hper hSfd hcomp hHgt] at key
  linear_combination -key


/-- **The valence formula for a nonzero level-one modular form.** Beyond nonvanishing, the
divisor set is only asked to capture the closed fundamental domain's divisor in both
directions — every point of `𝒟` of nonzero order lies in `S` (`hcomp`), and every point of
`S` of nonzero order lies in `𝒟` (`hSfd`); the truncation height and every analytic input
are constructed in the fixed-height layer above.

The height is internal, following `valence_formula_general_S_FM` in
`ForMathlib/ValenceFormula.lean` of AINTLIB (github.com/CBirkbeck/AINTLIB, revision
2baa76f742bdb4fb8ee323fabba41203bd390e08): `exists_height_bound` dominates the divisor set,
and `exists_threshold_cuspFunction_ne_zero` supplies the threshold above which the `q`-disk
of radius `fdBoundaryQRadius H = exp (-2πH)` sits inside the cusp function's non-vanishing
neighbourhood — the maximum of the two serves, and above it the cusp-function non-vanishing
`hgz` holds. -/
theorem sum_orderOfVanishingAt_add_elliptic_add_qExpansionOrderAtCusp_eq
    [ModularFormClass F 𝒮ℒ k] (f : F) (hf : (⇑f : ℍ → ℂ) ≠ 0) {S : Finset ℍ}
    (hSfd : ∀ p ∈ S, orderOfVanishingAt ⇑f p ≠ 0 → p ∈ 𝒟)
    (hcomp : ∀ p, p ∈ 𝒟 → orderOfVanishingAt ⇑f p ≠ 0 → p ∈ S) :
    ∑ p ∈ S.filter (fun p : ℍ ↦ 1 < ‖(p : ℂ)‖ ∧ |(p : ℂ).re| < 1 / 2),
          ((orderOfVanishingAt ⇑f p : ℤ) : ℂ)
        + ∑ p ∈ S.filter (fun p : ℍ ↦ (p : ℂ).re = -(1 / 2) ∧ 1 < ‖(p : ℂ)‖),
          ((orderOfVanishingAt ⇑f p : ℤ) : ℂ)
        + ∑ p ∈ S.filter (fun p : ℍ ↦ (p : ℂ) ≠ (ρ : ℂ) ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0),
          ((orderOfVanishingAt ⇑f p : ℤ) : ℂ)
        + 1 / 2 * ((orderOfVanishingAt ⇑f UpperHalfPlane.I : ℤ) : ℂ)
        + 1 / 3 * ((orderOfVanishingAt ⇑f ρ : ℤ) : ℂ)
        + qExpansionOrderAtCusp 1 ⇑f = (k : ℂ) / 12 := by
  obtain ⟨H₀, hH₀⟩ := exists_threshold_cuspFunction_ne_zero hf
  obtain ⟨H₁, -, hH₁1, hH₁⟩ := exists_height_bound S
  exact sum_orderOfVanishingAt_add_elliptic_add_qExpansionOrderAtCusp_eq_of_im_lt f hf
    (hH₁1.trans_le (le_max_right _ _)) hSfd hcomp
    (fun p hp => (hH₁ p hp).trans_le (le_max_right _ _)) (hH₀ _ (le_max_left _ _))

/-- **The valence formula, with its interior divisor sum reindexed over orbits.** The divisor
set is captured in both directions as in the point-sum statement — every point of `𝒟` of
nonzero order lies in `S` (`hcomp`), every point of `S` of nonzero order lies in `𝒟`
(`hSfd`). The order is constant along the `SL₂(ℤ)`-action, so the interior divisor points may
be replaced by the orbits they represent; this is faithful because distinct points of the
open fundamental domain lie in distinct orbits. The boundary families stay as point sums: the
closed domain's boundary identifications are exactly what the left-representative filters
already quotient by.

⚠ The sum here runs over the orbits *met by the divisor set* `S`, **not** over the whole
non-elliptic orbit space, which is what the roadmap's Layer-1 target states. Reaching that
needs the further step that an orbit missed by `S` contributes `0`
(`orderOfVanishingOnOrbit_eq_zero_of_notMem`).

Level one is forced: `orderOfVanishingOnOrbit` is defined for `𝒮ℒ`-invariant forms, so this
theorem takes the level-one class rather than a general `Γ`. -/
theorem finsum_orderOfVanishingOnOrbit_mem_image_add_elliptic_add_qExpansionOrderAtCusp_eq
    [ModularFormClass F 𝒮ℒ k] (f : F) (hf : (⇑f : ℍ → ℂ) ≠ 0) {S : Finset ℍ}
    (hSfd : ∀ p ∈ S, orderOfVanishingAt ⇑f p ≠ 0 → p ∈ 𝒟)
    (hcomp : ∀ p, p ∈ 𝒟 → orderOfVanishingAt ⇑f p ≠ 0 → p ∈ S) :
    ((∑ᶠ q ∈ (fun p : ℍ ↦ (Quotient.mk'' p : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ)) ''
            ↑(S.filter (fun p : ℍ ↦ 1 < ‖(p : ℂ)‖ ∧ |(p : ℂ).re| < 1 / 2)),
          orderOfVanishingOnOrbit f q : ℤ) : ℂ)
        + ∑ p ∈ S.filter (fun p : ℍ ↦ (p : ℂ).re = -(1 / 2) ∧ 1 < ‖(p : ℂ)‖),
          ((orderOfVanishingAt ⇑f p : ℤ) : ℂ)
        + ∑ p ∈ S.filter (fun p : ℍ ↦ (p : ℂ) ≠ (ρ : ℂ) ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0),
          ((orderOfVanishingAt ⇑f p : ℤ) : ℂ)
        + 1 / 2 * ((orderOfVanishingAt ⇑f UpperHalfPlane.I : ℤ) : ℂ)
        + 1 / 3 * ((orderOfVanishingAt ⇑f ρ : ℤ) : ℂ)
        + qExpansionOrderAtCusp 1 ⇑f = (k : ℂ) / 12 := by
  have hfdo : ∀ p ∈ S.filter (fun p : ℍ ↦ 1 < ‖(p : ℂ)‖ ∧ |(p : ℂ).re| < 1 / 2), p ∈ 𝒟ᵒ := by
    intro p hp
    obtain ⟨-, hn, hre⟩ := Finset.mem_filter.mp hp
    exact ⟨Complex.one_lt_normSq_iff.mpr hn, hre⟩
  have horb : ∑ p ∈ S.filter (fun p : ℍ ↦ 1 < ‖(p : ℂ)‖ ∧ |(p : ℂ).re| < 1 / 2),
      orderOfVanishingAt (⇑f) p =
      ∑ᶠ q ∈ (fun p : ℍ ↦ (Quotient.mk'' p : MulAction.orbitRel.Quotient SL(2, ℤ) ℍ)) ''
          ↑(S.filter (fun p : ℍ ↦ 1 < ‖(p : ℂ)‖ ∧ |(p : ℂ).re| < 1 / 2)),
        orderOfVanishingOnOrbit (k := k) f q :=
    sum_orderOfVanishingAt_eq_finsum_orbit f (fun p : ℍ ↦ p) fun a ha b hb hab =>
      TauCeti.ModularGroup.orbit_mk_injOn_fdo (hfdo a (by simpa using ha))
        (hfdo b (by simpa using hb)) hab
  have key := sum_orderOfVanishingAt_add_elliptic_add_qExpansionOrderAtCusp_eq
    f hf hSfd hcomp
  rw [← horb]
  push_cast
  exact key

end ModularForm

end TauCeti

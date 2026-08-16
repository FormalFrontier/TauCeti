/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Assembly
public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.SingularSets

import TauCeti.Analysis.Calculus.PeriodicDeriv
import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.ExcisionSeparation

/-!
# The excised boundary contour integral of a level-one logarithmic derivative

`TauCeti.ModularForm.intervalIntegral_logDeriv_fdBoundary` assembles the boundary integral
for a form with no zeros on the contour. The valence formula needs the version that tolerates
them at the elliptic points `i` and `ρ`, which sit *on* the fundamental-domain boundary, so a
form vanishing there makes `logDeriv f` blow up on the contour itself. (Nonvanishing along the
ceiling is still required, through the `q`-disk hypothesis.) The device is `ε`-excision —
the integrand is replaced by `0` within `ε` of any excision centre — and this file assembles
the excised integral **at a fixed `ε`**, from integrability hypotheses it takes rather than
proves. Taking `ε → 0` and identifying the limit as a principal value is not done here.

The three pieces are already available and each already tolerates the excision: the verticals
cancel by periodicity (`intervalIntegral_excised_fdBoundarySegment4_eq_neg_segment1`), the
arc collapses to its weight term
(`two_mul_intervalIntegral_excised_deriv_smul_logDeriv_comp_ofComplex_fdBoundary_arc`), and
the ceiling is untouched by the excision altogether
(`intervalIntegral_excised_logDeriv_fdBoundarySegment5_eq_two_pi_I_mul_qExpansionOrderAtCusp`).

The assembly comes in two set shapes. `intervalIntegral_excised_logDeriv_fdBoundary` takes a
single unit-norm inversion-closed excision set, which serves a form whose contour zeros all
sit on the arc. The valence formula's unconditional excision set is the union
`arcSingularSet S ∪ verticalSingularSet S`, whose vertical part leaves the unit circle;
`intervalIntegral_excised_logDeriv_fdBoundary_arcSingularSet_union_verticalSingularSet`
assembles that shape. Its verticals still cancel — the union is closed under the reflection
`z ↦ -conj z` — and once `ε` is under the arc/vertical separation the union test agrees with
its arc part along the arc, so the arc still collapses through the arc-only machinery.

## Main declarations

* `TauCeti.ModularForm.intervalIntegral_excised_logDeriv_fdBoundary`: the assembled excised
  boundary integral, `2πi · ord_∞ - (k/2) · ∫₁³ (excised logDeriv γ)`.
* `intervalIntegral_excised_logDeriv_fdBoundary_arcSingularSet_union_verticalSingularSet`
  (same namespace): the assembly for the union-shaped excision set, for `ε` under the
  arc/vertical separation.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development (`ForMathlib/ValenceFormula/PVChain/Assembly.lean`) this file ports onto the
  current Mathlib pin.
-/

public section

open Complex Function MeasureTheory Set UpperHalfPlane

open scoped MatrixGroups Real

namespace TauCeti

namespace ModularForm

variable {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup SL(2, ℤ)} {k : ℤ}

/-- **The excised boundary assembly, given the excision set's reflection closure.** The shared
machinery behind `intervalIntegral_excised_logDeriv_fdBoundary` and
`intervalIntegral_excised_logDeriv_fdBoundary_arcSingularSet_union_verticalSingularSet`: once the
excision test set `Sx` is closed under `z ↦ -conj z` (`hrefl`), is excised-integrable on
`[2, 3]` (`hint23`), and its excised arc integral already collapses to the weight term (`harc`),
the four pieces assemble exactly as in the unexcised case — the verticals cancel, the arc
contributes `harc`'s weight term, and the ceiling reads the cusp order. The two callers differ
only in how they produce `hrefl`, `hint23` and `harc` from their own excision set. -/
private theorem intervalIntegral_excised_logDeriv_fdBoundary_of_neg_conj_mem
    (f : F) {H ε : ℝ} {Sx : Finset ℂ} (hrefl : ∀ s ∈ Sx, -(starRingEnd ℂ) s ∈ Sx)
    (hlt : ∀ s ∈ Sx, s.im + ε < H) (hper : Periodic (⇑f ∘ ofComplex) 1)
    (hga : ∀ q ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H),
      AnalyticAt ℂ (cuspFunction 1 ⇑f) q)
    (hgz : ∀ q ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H), q ≠ 0 →
      cuspFunction 1 ⇑f q ≠ 0)
    (hint01 : IntervalIntegrable (fun t ↦ if ∃ s ∈ Sx, ‖fdBoundary H t - s‖ ≤ ε then 0
      else deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t)) volume 0 1)
    (hint12 : IntervalIntegrable (fun t ↦ if ∃ s ∈ Sx, ‖fdBoundary H t - s‖ ≤ ε then 0
      else deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t)) volume 1 2)
    (hint23 : IntervalIntegrable (fun t ↦ if ∃ s ∈ Sx, ‖fdBoundary H t - s‖ ≤ ε then 0
      else deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t)) volume 2 3)
    (hint45 : IntervalIntegrable (fun t ↦ if ∃ s ∈ Sx, ‖fdBoundary H t - s‖ ≤ ε then 0
      else deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t)) volume 4 5)
    (harc : 2 * ∫ t in (1 : ℝ)..3, (if ∃ s ∈ Sx, ‖fdBoundary H t - s‖ ≤ ε then 0
        else deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t)) =
      -(k : ℂ) * ∫ t in (1 : ℝ)..3, (if ∃ s ∈ Sx, ‖fdBoundary H t - s‖ ≤ ε then 0
        else logDeriv (fdBoundary H) t)) :
    ∫ t in (0 : ℝ)..5, (if ∃ s ∈ Sx, ‖fdBoundary H t - s‖ ≤ ε then 0
        else deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t)) =
      2 * Real.pi * Complex.I * qExpansionOrderAtCusp 1 ⇑f -
        (k : ℂ) / 2 * ∫ t in (1 : ℝ)..3, (if ∃ s ∈ Sx, ‖fdBoundary H t - s‖ ≤ ε then 0
          else logDeriv (fdBoundary H) t) := by
  have hint34 : IntervalIntegrable (fun t ↦ if ∃ s ∈ Sx, ‖fdBoundary H t - s‖ ≤ ε then 0
      else deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t)) volume 3 4 := by
    simpa only [smul_ite, smul_zero] using
      intervalIntegrable_excised_deriv_smul_fdBoundarySegment4
        (TauCeti.Function.Periodic.logDeriv hper) hrefl
        (by simpa only [smul_ite, smul_zero] using hint01)
  have hint13 := hint12.trans hint23
  have hint35 := hint34.trans hint45
  have hvert : (∫ t in (3 : ℝ)..4, (if ∃ s ∈ Sx, ‖fdBoundary H t - s‖ ≤ ε then 0
        else deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t))) =
      -∫ t in (0 : ℝ)..1, (if ∃ s ∈ Sx, ‖fdBoundary H t - s‖ ≤ ε then 0
        else deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t)) := by
    simpa only [smul_ite, smul_zero] using
      intervalIntegral_excised_fdBoundarySegment4_eq_neg_segment1 H
        (TauCeti.Function.Periodic.logDeriv hper) hrefl
  rw [← intervalIntegral.integral_add_adjacent_intervals hint01 (hint13.trans hint35),
    ← intervalIntegral.integral_add_adjacent_intervals hint13 hint35,
    ← intervalIntegral.integral_add_adjacent_intervals hint34 hint45,
    hvert,
    intervalIntegral_excised_logDeriv_fdBoundarySegment5_eq_two_pi_I_mul_qExpansionOrderAtCusp
      hlt hper hga hgz]
  linear_combination harc / 2

/-- **The excised boundary contour integral of a level-one logarithmic derivative.** The
four pieces assemble exactly as they do without the excision: the verticals cancel, the arc
collapses to its weight term, and the ceiling reads the cusp order. What the excision buys is
zeros on the arc and at the elliptic boundary points, where the integrand is replaced by `0`
instead. It does not free the ceiling: `hgz` still asks `f` to be nonvanishing at every
nonzero point of the closed `q`-disk, the circle of which is the ceiling.

The statement is at a fixed `ε`, with integrability on `[0, 1]`, `[1, 2]` and `[4, 5]` assumed;
the remaining two pieces are derived by the reflections. Compare
`intervalIntegral_logDeriv_fdBoundary`, the unexcised assembly, whose arc term is the constant
`k·(π/6)·i`: here the arc term is `(k/2)` times the excised arc integral of the contour's own
logarithmic derivative, an `ε`-dependent quantity this theorem says nothing about the limit
of. -/
theorem intervalIntegral_excised_logDeriv_fdBoundary [SlashInvariantFormClass F Γ k] (f : F)
    (hS : ModularGroup.S ∈ Γ) {H ε : ℝ} {S : Finset ℂ}
    (hnorm : ∀ s ∈ S, ‖s‖ = 1) (hinv : ∀ s ∈ S, -1 / s ∈ S)
    (hlt : ∀ s ∈ S, s.im + ε < H)
    (hper : Periodic (⇑f ∘ ofComplex) 1)
    (hd : ∀ t ∈ Ioo (1 : ℝ) 2, ¬(∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε) →
      DifferentiableAt ℂ (⇑f ∘ ofComplex) (fdBoundary H t))
    (hne : ∀ t ∈ Ioo (1 : ℝ) 2, ¬(∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε) →
      (⇑f ∘ ofComplex) (fdBoundary H t) ≠ 0)
    (hga : ∀ q ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H),
      AnalyticAt ℂ (cuspFunction 1 ⇑f) q)
    (hgz : ∀ q ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H), q ≠ 0 →
      cuspFunction 1 ⇑f q ≠ 0)
    (hint01 : IntervalIntegrable (fun t ↦ if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
      else deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t)) volume 0 1)
    (hint12 : IntervalIntegrable (fun t ↦ if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
      else deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t)) volume 1 2)
    (hint45 : IntervalIntegrable (fun t ↦ if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
      else deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t)) volume 4 5) :
    ∫ t in (0 : ℝ)..5, (if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
        else deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t)) =
      2 * Real.pi * Complex.I * qExpansionOrderAtCusp 1 ⇑f -
        (k : ℂ) / 2 * ∫ t in (1 : ℝ)..3, (if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0
          else logDeriv (fdBoundary H) t) := by
  -- On the unit circle inversion is conjugation, so the arc hypothesis already gives the
  -- vertical one: `-1 / s = -s⁻¹ = -conj s`.
  have hrefl : ∀ s ∈ S, -(starRingEnd ℂ) s ∈ S := fun s hs => by
    have h : -1 / s = -(starRingEnd ℂ) s := by
      rw [neg_div, one_div, Complex.inv_eq_conj (hnorm s hs)]
    exact h ▸ hinv s hs
  exact intervalIntegral_excised_logDeriv_fdBoundary_of_neg_conj_mem f hrefl hlt hper hga hgz
    hint01 hint12
    (intervalIntegrable_excised_deriv_smul_logDeriv_comp_ofComplex_fdBoundarySegment3 f hS hnorm
      hinv hd hne hint12)
    hint45
    (two_mul_intervalIntegral_excised_deriv_smul_logDeriv_comp_ofComplex_fdBoundary_arc f hS hnorm
      hinv hd hne hint12)

/-- **Integrability on the second arc half, union-excised.** For `ε` under the arc/vertical
separation the union test agrees with its arc part along the arc
(`exists_norm_fdBoundary_sub_le_union_iff`), so the `[1, 2]`-side hypotheses convert to their
arc-only form, the arc-only reflected integrability applies, and its conclusion transfers back
to the union test. -/
private theorem intervalIntegrable_union_excised_fdBoundarySegment3
    [SlashInvariantFormClass F Γ k] (f : F) (hS : ModularGroup.S ∈ Γ) {H ε : ℝ} {S : Finset ℍ}
    (hfar : ∀ s ∈ verticalSingularSet S, s ∉ arcSingularSet S →
      ∀ t ∈ Icc (1 : ℝ) 3, ε < ‖fdBoundary H t - s‖)
    (hd : ∀ t ∈ Ioo (1 : ℝ) 2,
      ¬(∃ s ∈ arcSingularSet S ∪ verticalSingularSet S, ‖fdBoundary H t - s‖ ≤ ε) →
      DifferentiableAt ℂ (⇑f ∘ ofComplex) (fdBoundary H t))
    (hne : ∀ t ∈ Ioo (1 : ℝ) 2,
      ¬(∃ s ∈ arcSingularSet S ∪ verticalSingularSet S, ‖fdBoundary H t - s‖ ≤ ε) →
      (⇑f ∘ ofComplex) (fdBoundary H t) ≠ 0)
    (hint12 : IntervalIntegrable (fun t ↦
      if ∃ s ∈ arcSingularSet S ∪ verticalSingularSet S, ‖fdBoundary H t - s‖ ≤ ε then 0
      else deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t)) volume 1 2) :
    IntervalIntegrable (fun t ↦
      if ∃ s ∈ arcSingularSet S ∪ verticalSingularSet S, ‖fdBoundary H t - s‖ ≤ ε then 0
      else deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t)) volume 2 3 := by
  refine (intervalIntegrable_excised_deriv_smul_logDeriv_comp_ofComplex_fdBoundarySegment3 f hS
    (fun _ hs => norm_eq_one_of_mem_arcSingularSet hs)
    (fun _ hs => neg_one_div_mem_arcSingularSet hs)
    (fun t ht hn => hd t ht fun hu => hn ((exists_norm_fdBoundary_sub_le_union_iff hfar
      ⟨ht.1.le, by linarith [ht.2]⟩).mp hu))
    (fun t ht hn => hne t ht fun hu => hn ((exists_norm_fdBoundary_sub_le_union_iff hfar
      ⟨ht.1.le, by linarith [ht.2]⟩).mp hu))
    (hint12.congr_uIoo fun t ht => by
      rw [Set.uIoo_of_le (by norm_num : (1 : ℝ) ≤ 2)] at ht
      exact if_congr (exists_norm_fdBoundary_sub_le_union_iff hfar
        ⟨ht.1.le, by linarith [ht.2]⟩) rfl rfl)).congr_uIoo fun t ht => ?_
  rw [Set.uIoo_of_le (by norm_num : (2 : ℝ) ≤ 3)] at ht
  exact (if_congr (exists_norm_fdBoundary_sub_le_union_iff hfar
    ⟨by linarith [ht.1], ht.2.le⟩) rfl rfl).symm

/-- **The union-excised arc integral collapses to the weight term.** For `ε` under the
arc/vertical separation the union test agrees with its arc part along the arc
(`exists_norm_fdBoundary_sub_le_union_iff`), so the `[1, 2]`-side hypotheses convert to their
arc-only form, the arc-only collapse applies, and both of its integrals transfer back to the
union test. -/
private theorem two_mul_intervalIntegral_union_excised_arc
    [SlashInvariantFormClass F Γ k] (f : F) (hS : ModularGroup.S ∈ Γ) {H ε : ℝ} {S : Finset ℍ}
    (hfar : ∀ s ∈ verticalSingularSet S, s ∉ arcSingularSet S →
      ∀ t ∈ Icc (1 : ℝ) 3, ε < ‖fdBoundary H t - s‖)
    (hd : ∀ t ∈ Ioo (1 : ℝ) 2,
      ¬(∃ s ∈ arcSingularSet S ∪ verticalSingularSet S, ‖fdBoundary H t - s‖ ≤ ε) →
      DifferentiableAt ℂ (⇑f ∘ ofComplex) (fdBoundary H t))
    (hne : ∀ t ∈ Ioo (1 : ℝ) 2,
      ¬(∃ s ∈ arcSingularSet S ∪ verticalSingularSet S, ‖fdBoundary H t - s‖ ≤ ε) →
      (⇑f ∘ ofComplex) (fdBoundary H t) ≠ 0)
    (hint12 : IntervalIntegrable (fun t ↦
      if ∃ s ∈ arcSingularSet S ∪ verticalSingularSet S, ‖fdBoundary H t - s‖ ≤ ε then 0
      else deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t)) volume 1 2) :
    2 * ∫ t in (1 : ℝ)..3,
        (if ∃ s ∈ arcSingularSet S ∪ verticalSingularSet S, ‖fdBoundary H t - s‖ ≤ ε then 0
        else deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t)) =
      -(k : ℂ) * ∫ t in (1 : ℝ)..3,
        (if ∃ s ∈ arcSingularSet S ∪ verticalSingularSet S, ‖fdBoundary H t - s‖ ≤ ε then 0
        else logDeriv (fdBoundary H) t) := by
  have hcongr : ∀ g : ℝ → ℂ,
      (∫ t in (1 : ℝ)..3,
        (if ∃ s ∈ arcSingularSet S ∪ verticalSingularSet S, ‖fdBoundary H t - s‖ ≤ ε then 0
        else g t)) =
      ∫ t in (1 : ℝ)..3,
        (if ∃ s ∈ arcSingularSet S, ‖fdBoundary H t - s‖ ≤ ε then 0 else g t) :=
    fun g => intervalIntegral.integral_congr fun t ht =>
      if_congr (exists_norm_fdBoundary_sub_le_union_iff hfar
        (by rwa [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)] at ht)) rfl rfl
  rw [hcongr, hcongr]
  exact two_mul_intervalIntegral_excised_deriv_smul_logDeriv_comp_ofComplex_fdBoundary_arc f hS
    (fun _ hs => norm_eq_one_of_mem_arcSingularSet hs)
    (fun _ hs => neg_one_div_mem_arcSingularSet hs)
    (fun t ht hn => hd t ht fun hu => hn ((exists_norm_fdBoundary_sub_le_union_iff hfar
      ⟨ht.1.le, by linarith [ht.2]⟩).mp hu))
    (fun t ht hn => hne t ht fun hu => hn ((exists_norm_fdBoundary_sub_le_union_iff hfar
      ⟨ht.1.le, by linarith [ht.2]⟩).mp hu))
    (hint12.congr_uIoo fun t ht => by
      rw [Set.uIoo_of_le (by norm_num : (1 : ℝ) ≤ 2)] at ht
      exact if_congr (exists_norm_fdBoundary_sub_le_union_iff hfar
        ⟨ht.1.le, by linarith [ht.2]⟩) rfl rfl)

/-- **The excised boundary integral for the union-shaped excision set.** The excision set is
now `arcSingularSet S ∪ verticalSingularSet S` — both singular families of a finite set of
upper half-plane points — rather than a single unit-norm inversion-closed set, so a form may
vanish on the verticals of the contour as well as on the arc. The verticals still cancel: the
union is closed under the reflection `z ↦ -conj z` that exchanges them
(`neg_conj_mem_arcSingularSet_union_verticalSingularSet`). The arc still collapses to its
weight term: for `ε` under the arc/vertical separation `hfar` the union test agrees with its
arc part along the arc, and the arc-only pairing machinery applies. The ceiling is untouched
by the excision, exactly as in `intervalIntegral_excised_logDeriv_fdBoundary`.

`hfar` is the fixed-`ε` reading of the separation
`exists_pos_forall_le_norm_fdBoundary_sub_of_mem_verticalSingularSet`, satisfied for every
small `ε` by `eventually_forall_lt_norm_fdBoundary_sub_of_mem_verticalSingularSet`; `hlt` is
the same `ε`-smallness clearance below the ceiling the arc-only assembly takes. -/
theorem intervalIntegral_excised_logDeriv_fdBoundary_arcSingularSet_union_verticalSingularSet
    [SlashInvariantFormClass F Γ k] (f : F) (hS : ModularGroup.S ∈ Γ) {H ε : ℝ} {S : Finset ℍ}
    (hfar : ∀ s ∈ verticalSingularSet S, s ∉ arcSingularSet S →
      ∀ t ∈ Icc (1 : ℝ) 3, ε < ‖fdBoundary H t - s‖)
    (hlt : ∀ s ∈ arcSingularSet S ∪ verticalSingularSet S, s.im + ε < H)
    (hper : Periodic (⇑f ∘ ofComplex) 1)
    (hd : ∀ t ∈ Ioo (1 : ℝ) 2,
      ¬(∃ s ∈ arcSingularSet S ∪ verticalSingularSet S, ‖fdBoundary H t - s‖ ≤ ε) →
      DifferentiableAt ℂ (⇑f ∘ ofComplex) (fdBoundary H t))
    (hne : ∀ t ∈ Ioo (1 : ℝ) 2,
      ¬(∃ s ∈ arcSingularSet S ∪ verticalSingularSet S, ‖fdBoundary H t - s‖ ≤ ε) →
      (⇑f ∘ ofComplex) (fdBoundary H t) ≠ 0)
    (hga : ∀ q ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H),
      AnalyticAt ℂ (cuspFunction 1 ⇑f) q)
    (hgz : ∀ q ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H), q ≠ 0 →
      cuspFunction 1 ⇑f q ≠ 0)
    (hint01 : IntervalIntegrable (fun t ↦
      if ∃ s ∈ arcSingularSet S ∪ verticalSingularSet S, ‖fdBoundary H t - s‖ ≤ ε then 0
      else deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t)) volume 0 1)
    (hint12 : IntervalIntegrable (fun t ↦
      if ∃ s ∈ arcSingularSet S ∪ verticalSingularSet S, ‖fdBoundary H t - s‖ ≤ ε then 0
      else deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t)) volume 1 2)
    (hint45 : IntervalIntegrable (fun t ↦
      if ∃ s ∈ arcSingularSet S ∪ verticalSingularSet S, ‖fdBoundary H t - s‖ ≤ ε then 0
      else deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t)) volume 4 5) :
    ∫ t in (0 : ℝ)..5,
        (if ∃ s ∈ arcSingularSet S ∪ verticalSingularSet S, ‖fdBoundary H t - s‖ ≤ ε then 0
        else deriv (fdBoundary H) t • logDeriv (⇑f ∘ ofComplex) (fdBoundary H t)) =
      2 * Real.pi * Complex.I * qExpansionOrderAtCusp 1 ⇑f -
        (k : ℂ) / 2 * ∫ t in (1 : ℝ)..3,
          (if ∃ s ∈ arcSingularSet S ∪ verticalSingularSet S, ‖fdBoundary H t - s‖ ≤ ε then 0
          else logDeriv (fdBoundary H) t) := by
  exact intervalIntegral_excised_logDeriv_fdBoundary_of_neg_conj_mem f
    (fun _ hs => neg_conj_mem_arcSingularSet_union_verticalSingularSet hs) hlt hper hga hgz hint01
    hint12 (intervalIntegrable_union_excised_fdBoundarySegment3 f hS hfar hd hne hint12) hint45
    (two_mul_intervalIntegral_union_excised_arc f hS hfar hd hne hint12)

end ModularForm

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Meromorphic.Basic
public import TauCeti.Analysis.Contour.Cauchy.PrincipalValue.On
public import TauCeti.Analysis.Contour.PwC1ImmersionOn
public import TauCeti.Analysis.Contour.RegularityConditions
public import TauCeti.Analysis.Contour.Residue.Basic
public import TauCeti.Analysis.Contour.Winding.Number.Basic
import TauCeti.Analysis.Contour.ConditionDischarge
import TauCeti.Analysis.Contour.InvSubCPVExistence
import TauCeti.Analysis.Contour.MeromorphicLaurent
import TauCeti.Analysis.Contour.PolarPart.Decomposition
import TauCeti.Analysis.Contour.Residue.Assembly
import TauCeti.Analysis.Contour.Winding.Number.Reverse
import Mathlib.Analysis.Complex.CauchyIntegral
import TauCeti.Analysis.Contour.Crossing.Finiteness
import TauCeti.Analysis.Contour.FlatnessOne

/-!
# The Hungerbühler–Wasem generalized residue theorem

The summit of the contour-integration roadmap (HW Thm 3.3): for `f` holomorphic on `U ∖ S`
and meromorphic at each point of the finite `S ⊆ U`, and a **null-homologous, closed**
piecewise-`C¹` **immersion** `γ` in `U` rooted off the poles, under the regularity conditions
(A′) and (B), the set-level Cauchy principal value of `f` along `γ` exists and equals
`2πi · Σ_{s ∈ S} n_s(γ) · Res_s f` — with the generalized (non-integer) winding numbers as
weights, valid when singularities lie **on** the curve. The half-residue case
(`S = {s}`, `n_s(γ) = ½`) evaluates to `πi · Res_s f` — the on-cycle acceptance gate, and the
value the valence formula uses at `i` and `ρ`.

Both statements follow the roadmap signatures. The proof instantiates the canonical polar
decomposition, discharges the conditions into the per-pole hypotheses, and assembles the
residue sum; a reversed parametrization (`b ≤ a`) reduces to the oriented case through the
orientation lemmas, every ingredient being endpoint-swap invariant.

## Main results

* `Contour.hungerbuhlerWasem_residueTheorem` — HW Thm 3.3.
* `Contour.hasCauchyPV_half_residue` — the winding-`½` on-cycle case.
* `Contour.hungerbuhlerWasem_residueTheorem_of_simple_poles`,
  `Contour.hasCauchyPV_half_residue_of_simple_pole` — the simple-pole forms, with conditions
  (A′) and (B) discharged automatically; the statements the argument principle and the
  valence formula consume.

## Provenance

Migrated from `residueTheorem_crossing_paper_faithful_clean` of `MultiCrossingCPV.lean`
(re-exported as `hw_3_3_clean_full_mero` in `HW33Clean.lean`) in the AINTLIB
`LeanModularForms` development, restated for a raw curve over `[a, b]`; the basepoint
hypothesis `hγa` is that statement's `hx_notin_S`. See N. Hungerbühler, M. Wasem,
*Non-integer valued winding numbers and a generalized Residue Theorem*, arXiv:1808.00997,
Thm 3.3.
-/

public section

noncomputable section

namespace TauCeti.Contour

open Filter Set Topology

/-- The oriented (`a ≤ b`) case of the generalized residue theorem: instantiate the canonical
polar decomposition, discharge conditions (A′) and (B) into the per-pole hypotheses, and
assemble the residue sum. -/
private theorem hungerbuhlerWasem_residueTheorem_of_le {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (S : Finset ℂ) (γ : ℝ → ℂ) (a b : ℝ) (hγ_imm : IsPwC1ImmersionOn γ a b)
    (hSU : (S : Set ℂ) ⊆ U) (hclosed : γ a = γ b) (hγa : γ a ∉ (S : Set ℂ))
    (hγU : ∀ t ∈ Set.uIcc a b, γ t ∈ U) (hf : DifferentiableOn ℂ f (U \ (S : Set ℂ)))
    (hmero : ∀ s ∈ S, MeromorphicAt f s) (hnull : IsNullHomologous γ a b U)
    (hA : ConditionAprime γ a b f S) (hB : ConditionB γ a b f) (hab : a ≤ b) :
    HasCauchyPV γ a b f
      (2 * (Real.pi : ℂ) * Complex.I * (∑ s ∈ S, windingNumber γ a b s * residue f s)) := by
  classical
  have h_interior : ∀ s : S, ∀ t ∈ Icc a b, γ t = (s : ℂ) → t ∈ Ioo a b := fun s =>
    mem_Ioo_of_closed_of_ne hclosed fun h => hγa (h ▸ Finset.mem_coe.mpr s.2)
  have h_ord : ∀ s : S, (PolarPartDecomposition.ofMeromorphic hU hf hmero).order s
      = meromorphicPolarOrderAt f ↑s := fun s =>
    PolarPartDecomposition.ofMeromorphic_order s
  exact (PolarPartDecomposition.ofMeromorphic hU hf hmero).hasCauchyPV_residue_sum hU
    hγ_imm hab hclosed hγU hnull h_interior
    (fun s k hk1 _ => hA.flatOfOrder_of_crossing _ s s.2 hγ_imm hab (h_interior s)
      (h_ord s) k hk1)
    (fun s => hB.pow_unit_tangent_eq_of_coeff_ne_zero _ hU hSU s (hmero ↑s s.2) hγ_imm hab
      (h_interior s) (h_ord s))

/-- **The Hungerbühler–Wasem generalized residue theorem** (HW Thm 3.3): for `f` holomorphic
on `U ∖ S` and meromorphic at each point of the finite `S ⊆ U`, and a null-homologous closed
piecewise-`C¹` immersion `γ` in `U` rooted off the poles, under conditions (A′) and (B) the
set-level Cauchy principal value of `f` along `γ` is
`2πi · Σ_{s ∈ S} n_s(γ) · Res_s f`, with the generalized (non-integer) winding numbers as
weights — valid when singularities of `f` lie **on** the curve. -/
theorem hungerbuhlerWasem_residueTheorem {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (S : Finset ℂ) (γ : ℝ → ℂ) (a b : ℝ) (hγ_imm : IsPwC1ImmersionOn γ a b)
    (hSU : (S : Set ℂ) ⊆ U) (hclosed : γ a = γ b) (hγa : γ a ∉ (S : Set ℂ))
    (hγU : ∀ t ∈ Set.uIcc a b, γ t ∈ U) (hf : DifferentiableOn ℂ f (U \ (S : Set ℂ)))
    (hmero : ∀ s ∈ S, MeromorphicAt f s) (hnull : IsNullHomologous γ a b U)
    (hA : ConditionAprime γ a b f S) (hB : ConditionB γ a b f) :
    HasCauchyPV γ a b f
      (2 * (Real.pi : ℂ) * Complex.I * (∑ s ∈ S, windingNumber γ a b s * residue f s)) := by
  classical
  rcases le_total a b with hab | hba
  · exact hungerbuhlerWasem_residueTheorem_of_le hU S γ a b hγ_imm hSU hclosed hγa hγU hf
      hmero hnull hA hB hab
  · -- reduce the reversed parametrization to the oriented case on `(b, a)`
    have h_kernel_int : ∀ z ∉ U, IntervalIntegrable
        (fun t => (γ t - z)⁻¹ * deriv γ t) MeasureTheory.volume a b := fun z hz =>
      intervalIntegrable_inv_sub_mul_deriv hγ_imm.continuousOn
        (fun t ht h_eq => hz (h_eq ▸ hγU t ht))
        hγ_imm.isPiecewiseC1On.intervalIntegrable_deriv
    have h_core := hungerbuhlerWasem_residueTheorem_of_le hU S γ b a hγ_imm.symm hSU
      hclosed.symm (fun h => hγa (hclosed ▸ h))
      (fun t ht => hγU t (by rwa [Set.uIcc_comm])) hf hmero
      (hnull.symm_of_avoidance hγU hγ_imm.continuousOn h_kernel_int)
      (conditionAprime_comm.mp hA) (conditionB_comm.mp hB) hba
    have h_exists : ∀ s ∈ S, CauchyPVExistsAt γ b a (fun w => (w - s)⁻¹) s := fun s hs =>
      (hγ_imm.symm.cauchyPVExistsAt_inv_sub hba
        (mem_Ioo_of_closed_of_ne hclosed.symm
          (fun h => hγa (hclosed ▸ h ▸ Finset.mem_coe.mpr hs))))
    have h_val : (∑ s ∈ S, windingNumber γ b a s * residue f s)
        = -∑ s ∈ S, windingNumber γ a b s * residue f s := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [windingNumber_symm (h_exists s hs)]
      ring
    have h := h_core.symm
    rw [h_val] at h
    simpa using h

/-- **Half-residue: the winding-`½` on-cycle case of HW Thm 3.3** — the `S = {s}`
specialisation: when the generalized winding number of the closed, null-homologous immersion
about the on-cycle singularity `s` is `½`, the principal value is `πi · Res_s f`. -/
theorem hasCauchyPV_half_residue {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (γ : ℝ → ℂ)
    (a b : ℝ) (s : ℂ) (hγ_imm : IsPwC1ImmersionOn γ a b) (hsU : s ∈ U)
    (hclosed : γ a = γ b) (hγa : γ a ≠ s)
    (hγU : ∀ t ∈ Set.uIcc a b, γ t ∈ U) (hf : DifferentiableOn ℂ f (U \ {s}))
    (hmero : MeromorphicAt f s) (hnull : IsNullHomologous γ a b U)
    (hA : ConditionAprime γ a b f {s}) (hB : ConditionB γ a b f)
    (hwind : windingNumber γ a b s = 1 / 2) :
    HasCauchyPV γ a b f ((Real.pi : ℂ) * Complex.I * residue f s) := by
  have h := hungerbuhlerWasem_residueTheorem hU {s} γ a b hγ_imm
    (by simpa using hsU) hclosed (by simpa using hγa) hγU (by simpa using hf)
    (fun s' hs' => (Finset.mem_singleton.mp hs') ▸ hmero) hnull hA hB
  rw [Finset.sum_singleton, hwind] at h
  rw [show (Real.pi : ℂ) * Complex.I * residue f s
    = 2 * (Real.pi : ℂ) * Complex.I * (1 / 2 * residue f s) by ring]
  exact h

/-! ### The simple-pole form

When every prescribed singularity is at worst a simple pole, conditions (A′) and (B) hold
automatically — first-order flatness is every immersion's geometry, and the sector condition
only constrains poles of order `> 1`. This is HW's own base regime (Thm 3.3's unconditional
case, "`C` only contains singularities of `f` which are poles of order `1`"), and the form
the argument principle and the valence formula consume: a logarithmic derivative has only
simple poles. -/

/-- Everywhere on `U`, the order of `f` is at least `-1`: at the prescribed singularities by
hypothesis, elsewhere by analyticity on the open complement. -/
private theorem neg_one_le_meromorphicOrderAt {f : ℂ → ℂ} {U : Set ℂ} {S : Finset ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f (U \ (S : Set ℂ)))
    (h_simple : ∀ s ∈ S, ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f s) :
    ∀ w ∈ U, ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f w := by
  intro w hw
  by_cases hwS : w ∈ S
  · exact h_simple w hwS
  · have h_an : AnalyticAt ℂ f w :=
      hf.analyticOnNhd (hU.sdiff S.finite_toSet.isClosed) w ⟨hw, hwS⟩
    exact le_trans (by exact_mod_cast (by norm_num : (-1 : ℤ) ≤ 0))
      h_an.meromorphicOrderAt_nonneg

/-- **Condition (A′) is automatic at simple poles.** The only pole order the interior clause can
meet is `1`, discharged by the first-order flatness of the immersion, and the basepoint
`γ (min a b)` is off the singularities.

The curve need not be closed: `ConditionAprime` constrains the basepoint `γ (min a b)`, so
`hymin` is the whole premise the proof consumes. A closed contour supplies it from
`γ a = γ b` together with `γ a ∉ S`, which is what
`hungerbuhlerWasem_residueTheorem_of_simple_poles` does at its call site.

This is an instantiation lemma for `TauCeti.Contour.ConditionAprime`: it exhibits a hypothesis
set a caller can actually supply — a piecewise-`C¹` immersion whose basepoint lies off `S`, with
`f` having at worst simple poles — under which the condition holds. Where an interior crossing
occurs the flatness clause is met with content rather than by vacuity: the pole order there is
forced to `1` and `IsPwC1ImmersionOn.flatOfOrder_one` supplies the first-order flatness. On a
curve with no interior crossing the clause holds because there is nothing to discharge. -/
theorem conditionAprime_of_simple_poles {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ}
    {U : Set ℂ} {S : Finset ℂ} (hU : IsOpen U) (hγ_imm : IsPwC1ImmersionOn γ a b)
    (hymin : γ (min a b) ∉ (S : Set ℂ)) (hγU : ∀ t ∈ Set.uIcc a b, γ t ∈ U)
    (hf : DifferentiableOn ℂ f (U \ (S : Set ℂ)))
    (h_simple : ∀ s ∈ S, ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f s) :
    ConditionAprime γ a b f S := by
  have h_ge := neg_one_le_meromorphicOrderAt hU hf h_simple
  refine ⟨fun s _ => hγ_imm.finite_crossings, fun t₀ ht₀ _ n hn h_ord => ?_, fun hmem => ?_⟩
  · have h_le := h_ge (γ t₀) (hγU t₀ (by rw [← Set.Icc_min_max]; exact Set.Ioo_subset_Icc_self ht₀))
    rw [h_ord] at h_le
    have h_n : n = 1 := by
      have : (-1 : ℤ) ≤ -(n : ℤ) := by exact_mod_cast h_le
      omega
    subst h_n
    exact hγ_imm.flatOfOrder_one ht₀
  · exact absurd hmem hymin

/-- **Condition (B) is automatic at simple poles.** Its clauses only fire at poles of order
`> 1`, and there are none.

The companion instantiation lemma to `conditionAprime_of_simple_poles`: together the two
discharge both regularity hypotheses of HW Thm 3.3 from the same simple-pole hypothesis, which
is what makes `hungerbuhlerWasem_residueTheorem_of_simple_poles` unconditional. -/
theorem conditionB_of_simple_poles {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ}
    {U : Set ℂ} {S : Finset ℂ} (hU : IsOpen U) (hγU : ∀ t ∈ Set.uIcc a b, γ t ∈ U)
    (hf : DifferentiableOn ℂ f (U \ (S : Set ℂ)))
    (h_simple : ∀ s ∈ S, ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f s) :
    ConditionB γ a b f := by
  have h_ge := neg_one_le_meromorphicOrderAt hU hf h_simple
  refine ⟨fun t₀ ht₀ h_lt => absurd h_lt (not_lt.mpr
      (h_ge (γ t₀) (hγU t₀ (by rw [← Set.Icc_min_max]; exact Set.Ioo_subset_Icc_self ht₀)))),
    fun h_lt => absurd h_lt (not_lt.mpr (h_ge (γ (min a b))
      (hγU (min a b) (by rw [← Set.Icc_min_max]; exact Set.left_mem_Icc.mpr min_le_max))))⟩

/-- **The generalized residue theorem for simple poles** — HW Thm 3.3's unconditional regime:
when every prescribed singularity is at worst a simple pole
(`meromorphicOrderAt f s ≥ -1`), conditions (A′) and (B) hold automatically, and the
principal value is the winding-weighted residue sum with no regularity hypotheses beyond the
immersion. The form the argument principle and the valence formula consume. -/
theorem hungerbuhlerWasem_residueTheorem_of_simple_poles {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (S : Finset ℂ) (γ : ℝ → ℂ) (a b : ℝ) (hγ_imm : IsPwC1ImmersionOn γ a b)
    (hSU : (S : Set ℂ) ⊆ U) (hclosed : γ a = γ b) (hγa : γ a ∉ (S : Set ℂ))
    (hγU : ∀ t ∈ Set.uIcc a b, γ t ∈ U) (hf : DifferentiableOn ℂ f (U \ (S : Set ℂ)))
    (hmero : ∀ s ∈ S, MeromorphicAt f s) (hnull : IsNullHomologous γ a b U)
    (h_simple : ∀ s ∈ S, ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f s) :
    HasCauchyPV γ a b f
      (2 * (Real.pi : ℂ) * Complex.I * (∑ s ∈ S, windingNumber γ a b s * residue f s)) :=
  hungerbuhlerWasem_residueTheorem hU S γ a b hγ_imm hSU hclosed hγa hγU hf hmero hnull
    (conditionAprime_of_simple_poles hU hγ_imm
      (by rcases le_total a b with h | h
          · rwa [min_eq_left h]
          · rwa [min_eq_right h, ← hclosed]) hγU hf h_simple)
    (conditionB_of_simple_poles hU hγU hf h_simple)

/-- **The half-residue theorem at a simple pole**: the winding-`½` case with the conditions
discharged automatically — an on-cycle simple pole crossed by the immersion contributes
`πi · Res_s f`. The acceptance form for the valence formula's `i` and `ρ`. -/
theorem hasCauchyPV_half_residue_of_simple_pole {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (γ : ℝ → ℂ) (a b : ℝ) (s : ℂ) (hγ_imm : IsPwC1ImmersionOn γ a b) (hsU : s ∈ U)
    (hclosed : γ a = γ b) (hγa : γ a ≠ s)
    (hγU : ∀ t ∈ Set.uIcc a b, γ t ∈ U) (hf : DifferentiableOn ℂ f (U \ {s}))
    (hmero : MeromorphicAt f s) (hnull : IsNullHomologous γ a b U)
    (h_simple : ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f s)
    (hwind : windingNumber γ a b s = 1 / 2) :
    HasCauchyPV γ a b f ((Real.pi : ℂ) * Complex.I * residue f s) :=
  hasCauchyPV_half_residue hU γ a b s hγ_imm hsU hclosed hγa hγU hf hmero hnull
    (conditionAprime_of_simple_poles hU hγ_imm
      (by rcases le_total a b with h | h
          · simpa [min_eq_left h] using hγa
          · simpa [min_eq_right h, ← hclosed] using hγa)
      hγU (by simpa using hf)
      (fun s' hs' => (Finset.mem_singleton.mp hs') ▸ h_simple))
    (conditionB_of_simple_poles hU hγU (S := {s}) (by simpa using hf)
      (fun s' hs' => (Finset.mem_singleton.mp hs') ▸ h_simple))
    hwind

end TauCeti.Contour

end

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Contour.Cycle.Basic
public import TauCeti.Analysis.Contour.Winding.UnboundedComponent
import TauCeti.Analysis.Contour.Winding.Integer

/-!
# Winding numbers of contour cycles off their trace

The generalized winding number of a contour cycle is defined at every point by additive extension
from its closed piecewise-`C¹` generators. Away from the cycle's trace, every generator is in the
classical regime: its principal value is an ordinary integral and its winding number is an integer.
This file transfers that classical package to finite formal `ℤ`-combinations of curves.

The support formula is the bridge between the free-abelian-group definition and the single-curve
theory. It gives the ordinary contour-integral formula and integer-valuedness off the trace. It also
shows that the cycle winding number is locally constant on the trace complement, vanishes far from
the cycle, and hence vanishes on every unbounded connected component of the complement.

## Main results

* `TauCeti.Contour.Cycle.windingNumber_eq_integral_of_not_mem_trace` identifies the winding number
  off the trace with the normalized ordinary cycle integral of the Cauchy kernel.
* `TauCeti.Contour.Cycle.exists_int_windingNumber_of_not_mem_trace` proves integer-valuedness off
  the trace.
* `TauCeti.Contour.Cycle.isLocallyConstant_windingNumber` proves local constancy on the trace
  complement.
* `TauCeti.Contour.Cycle.windingNumber_eq_zero_of_unbounded_component` proves vanishing on every
  unbounded component of the complement.

## References

* N. Hungerbühler and M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997 (2018), Section 2.
* L. Ahlfors, *Complex Analysis*, Chapter 4.
-/

public section

noncomputable section

open Bornology Complex MeasureTheory Set

open scoped Topology

namespace TauCeti.Contour.Cycle

/-- The winding number of a cycle is the coefficient-weighted sum of the winding numbers of the
curves in its canonical support. -/
theorem windingNumber_eq_sum_support (C : Cycle) (z : ℂ) :
    windingNumber z C =
      ∑ γ ∈ FreeAbelianGroup.support C,
        (FreeAbelianGroup.coeff γ C : ℂ) * TauCeti.Contour.windingNumber γ γ.a γ.b z := by
  conv_lhs => rw [FreeAbelianGroup.eq_sum_support_coeff_smul_of C]
  simp only [map_sum, map_zsmul, windingNumber_of, ← Int.cast_smul_eq_zsmul ℂ, smul_eq_mul]

/-- **Ordinary-integral formula off the trace.** At a point `z` outside a contour cycle's trace,
the generalized winding number is the normalized ordinary cycle integral of the Cauchy kernel
`w ↦ (w - z)⁻¹`. No principal value remains: every generator in the canonical support avoids
`z`. -/
theorem windingNumber_eq_integral_of_not_mem_trace (C : Cycle) {z : ℂ} (hz : z ∉ trace C) :
    windingNumber z C =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * integral (fun w ↦ (w - z)⁻¹) C := by
  conv_lhs => rw [FreeAbelianGroup.eq_sum_support_coeff_smul_of C]
  conv_rhs => rw [FreeAbelianGroup.eq_sum_support_coeff_smul_of C]
  simp only [map_sum, map_zsmul, windingNumber_of, integral_of,
    ← Int.cast_smul_eq_zsmul ℂ, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun γ hγ ↦ ?_
  have hoff := avoids_of_mem_support hz hγ
  have hint := intervalIntegrable_inv_sub_mul_deriv γ.continuousOn hoff γ.intervalIntegrable_deriv
  have hwind := TauCeti.Contour.windingNumber_eq_integral_of_avoidance
    γ.continuousOn hoff hint
  rw [hwind]
  have hinter :
      (∫ t in γ.a..γ.b, deriv γ t * (γ t - z)⁻¹) =
        ∫ t in γ.a..γ.b, (γ t - z)⁻¹ * deriv γ t := by
    apply intervalIntegral.integral_congr
    intro t _
    exact mul_comm _ _
  rw [hinter]
  ring

/-- **Integer-valuedness off the trace.** The winding number of a contour cycle about a point
outside its trace is an integer. Each supported generator has an integer winding number there, and
the cycle value is their coefficient-weighted sum. -/
theorem exists_int_windingNumber_of_not_mem_trace (C : Cycle) {z : ℂ} (hz : z ∉ trace C) :
    ∃ n : ℤ, windingNumber z C = n := by
  classical
  have hgen : ∀ γ ∈ FreeAbelianGroup.support C,
      ∃ n : ℤ, TauCeti.Contour.windingNumber γ γ.a γ.b z = n := by
    intro γ hγ
    exact γ.isPiecewiseC1On.exists_int_windingNumber γ.source_eq_target
      (avoids_of_mem_support hz hγ)
  let n : PiecewiseC1ClosedCurve → ℤ := fun γ ↦
    if hγ : γ ∈ FreeAbelianGroup.support C then Classical.choose (hgen γ hγ) else 0
  have hn : ∀ γ ∈ FreeAbelianGroup.support C,
      TauCeti.Contour.windingNumber γ γ.a γ.b z = n γ := by
    intro γ hγ
    simpa only [n, dite_eq_left hγ] using Classical.choose_spec (hgen γ hγ)
  refine ⟨∑ γ ∈ FreeAbelianGroup.support C, FreeAbelianGroup.coeff γ C * n γ, ?_⟩
  rw [windingNumber_eq_sum_support]
  push_cast
  refine Finset.sum_congr rfl fun γ hγ ↦ ?_
  rw [hn γ hγ]

/-- **Local constancy off the trace.** The winding number of a contour cycle, viewed as a function
on the complement of its trace, is locally constant. This is the finite-sum extension of local
constancy for the closed generator curves. -/
theorem isLocallyConstant_windingNumber (C : Cycle) :
    IsLocallyConstant (fun z : {z : ℂ // z ∉ trace C} ↦ windingNumber z C) := by
  classical
  have hterm : ∀ γ ∈ FreeAbelianGroup.support C,
      IsLocallyConstant (fun z : {z : ℂ // z ∉ trace C} ↦
        (FreeAbelianGroup.coeff γ C : ℂ) *
          TauCeti.Contour.windingNumber γ γ.a γ.b z) := by
    intro γ hγ
    obtain ⟨P, hP, hdiff⟩ := γ.isPiecewiseC1On.exists_countable_differentiableAt
    let inclusion : {z : ℂ // z ∉ trace C} →
        {z : ℂ // ∀ t ∈ uIcc γ.a γ.b, γ t ≠ z} :=
      fun z ↦ ⟨z, avoids_of_mem_support z.property hγ⟩
    have hinclusion : Continuous inclusion := by fun_prop
    have hlocal := TauCeti.Contour.isLocallyConstant_windingNumber_of_closed γ.source_eq_target
      hP γ.continuousOn hdiff γ.intervalIntegrable_deriv
    exact (IsLocallyConstant.const (FreeAbelianGroup.coeff γ C : ℂ)).mul
      (hlocal.comp_continuous hinclusion)
  have hsum_aux : ∀ (s : Finset PiecewiseC1ClosedCurve),
      s ⊆ FreeAbelianGroup.support C →
        IsLocallyConstant (fun z : {z : ℂ // z ∉ trace C} ↦
          ∑ γ ∈ s, (FreeAbelianGroup.coeff γ C : ℂ) *
            TauCeti.Contour.windingNumber γ γ.a γ.b z) := by
    intro s hs
    induction s using Finset.induction_on with
    | empty => exact IsLocallyConstant.of_constant _ fun _ _ ↦ rfl
    | @insert γ s hγs ih =>
        have hγC : γ ∈ FreeAbelianGroup.support C := hs (Finset.mem_insert_self γ s)
        have hsC : s ⊆ FreeAbelianGroup.support C := fun _ h ↦ hs (Finset.mem_insert_of_mem h)
        simpa only [Finset.sum_insert hγs] using
          (hterm γ hγC).comp₂ (ih hsC) (fun x y : ℂ ↦ x + y)
  have hsum := hsum_aux (FreeAbelianGroup.support C) Subset.rfl
  have heq : (fun z : {z : ℂ // z ∉ trace C} ↦ windingNumber z C) =
      fun z : {z : ℂ // z ∉ trace C} ↦ ∑ γ ∈ FreeAbelianGroup.support C,
        (FreeAbelianGroup.coeff γ C : ℂ) *
          TauCeti.Contour.windingNumber γ γ.a γ.b z := by
    funext z
    exact windingNumber_eq_sum_support C z
  rw [heq]
  exact hsum

/-- The winding number of a contour cycle is constant on each connected component of the
complement of its trace. -/
theorem windingNumber_eq_of_mem_connectedComponentIn {C : Cycle} {z₀ z₁ : ℂ}
    (hz₁ : z₁ ∈ connectedComponentIn (trace C)ᶜ z₀) :
    windingNumber z₁ C = windingNumber z₀ C := by
  have hz₀ : z₀ ∈ (trace C)ᶜ := by
    by_contra hz₀
    rw [connectedComponentIn_eq_empty hz₀] at hz₁
    exact hz₁
  rw [connectedComponentIn_eq_image hz₀] at hz₁
  obtain ⟨z₁, hz₁, rfl⟩ := hz₁
  exact (isLocallyConstant_windingNumber C).apply_eq_of_isPreconnected
    isPreconnected_connectedComponent hz₁ mem_connectedComponent

/-- The winding number of a contour cycle eventually vanishes along the cocompact filter. The
same eventual set also lies outside the cycle's trace. -/
theorem windingNumber_eventually_zero_cocompact (C : Cycle) :
    ∀ᶠ z in Filter.cocompact ℂ, z ∉ trace C ∧ windingNumber z C = 0 := by
  classical
  have hgen : ∀ γ ∈ FreeAbelianGroup.support C,
      ∀ᶠ z in Filter.cocompact ℂ,
        (∀ t ∈ uIcc γ.a γ.b, γ t ≠ z) ∧
          TauCeti.Contour.windingNumber γ γ.a γ.b z = 0 := by
    intro γ hγ
    obtain ⟨P, hP, hdiff⟩ := γ.isPiecewiseC1On.exists_countable_differentiableAt
    exact TauCeti.Contour.windingNumber_eventually_zero_cocompact γ.source_eq_target hP
      γ.continuousOn hdiff γ.intervalIntegrable_deriv
  filter_upwards [(Filter.eventually_all_finset (FreeAbelianGroup.support C)).mpr hgen]
    with z hz
  constructor
  · rw [mem_trace_iff]
    rintro ⟨γ, hγ, t, ht, htz⟩
    exact (hz γ hγ).1 t ht htz
  · rw [windingNumber_eq_sum_support]
    exact Finset.sum_eq_zero fun γ hγ ↦ by rw [(hz γ hγ).2, mul_zero]

/-- **Vanishing on an unbounded component.** If the connected component of a point in the
complement of a contour cycle's trace is unbounded, then the cycle has winding number zero about
that point. -/
theorem windingNumber_eq_zero_of_unbounded_component {C : Cycle} {z : ℂ}
    (hcomp : ¬IsBounded (connectedComponentIn (trace C)ᶜ z)) : windingNumber z C = 0 := by
  obtain ⟨K, hK_compact, hK_good⟩ :=
    Filter.mem_cocompact.mp (windingNumber_eventually_zero_cocompact C)
  have hnot_subset : ¬connectedComponentIn (trace C)ᶜ z ⊆ K :=
    fun hsubset ↦ hcomp (hK_compact.isBounded.subset hsubset)
  obtain ⟨z', hz'_comp, hz'_notK⟩ := Set.not_subset.mp hnot_subset
  have hz'_zero : windingNumber z' C = 0 := (hK_good hz'_notK).2
  exact (windingNumber_eq_of_mem_connectedComponentIn hz'_comp).symm.trans hz'_zero

end TauCeti.Contour.Cycle

end

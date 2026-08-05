/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.Modular
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import TauCeti.NumberTheory.ModularForms.Order.OfVanishing

/-!
# Finite zeros of a level-one modular form in the fundamental domain

A nonzero level-one modular form does not vanish above some height, since its cusp
function is nonvanishing on a punctured `q`-ball; its remaining nonzero-order points in
the standard fundamental domain lie in a truncated fundamental domain, which is compact,
so by the accumulation-point argument and the identity theorem they are finite — the
finite-support input to the valence formula.

## Main declarations

* `TauCeti.ModularForm.exists_height_nonvanishing`: a nonzero form does not vanish at
  points of imaginary part above some height.
* `TauCeti.ModularForm.finite_zeros_in_fd`: finiteness of the nonzero-order points in `𝒟`.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development this file ports onto the current Mathlib pin.
-/

public noncomputable section

open Complex Filter Metric Set UpperHalfPlane TauCeti.UpperHalfPlane

open scoped ModularForm MatrixGroups Modular Topology

namespace TauCeti

namespace ModularForm

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {F : Type*} [FunLike F ℍ ℂ] {f : F} {h : ℝ}

private lemma cuspFunction_not_eventually_zero [ModularFormClass F Γ k] (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) (hf : (⇑f : ℍ → ℂ) ≠ 0) :
    ¬∀ᶠ q in 𝓝 (0 : ℂ), cuspFunction h f q = 0 := by
  intro h_ev
  have h_diff : DifferentiableOn ℂ (cuspFunction h f) (ball 0 1) :=
    have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
    differentiableOn_cuspFunction_ball hh (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ)
      (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f)
  have h_eqOn : EqOn (cuspFunction h f) 0 (ball 0 1) :=
    (h_diff.analyticOnNhd isOpen_ball).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball 0 1).isPreconnected (mem_ball_self one_pos) h_ev
  refine hf (funext fun τ ↦ ?_)
  rw [Pi.zero_apply, ← SlashInvariantFormClass.eq_cuspFunction f τ hΓ hh.ne']
  exact h_eqOn (by
    rw [mem_ball, dist_zero_right]
    exact_mod_cast Function.Periodic.norm_qParam_lt_one hh τ.im_pos)

private lemma cuspFunction_eventually_ne_zero [ModularFormClass F Γ k] (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) (hf : (⇑f : ℍ → ℂ) ≠ 0) :
    ∀ᶠ q in 𝓝[≠] (0 : ℂ), cuspFunction h f q ≠ 0 :=
  (ModularFormClass.analyticAt_cuspFunction_zero f hh
    hΓ).eventually_eq_zero_or_eventually_ne_zero.resolve_left
    (cuspFunction_not_eventually_zero hh hΓ hf)

/-- A nonzero modular form with a positive strict period does not vanish at points of
sufficiently large imaginary part. -/
lemma exists_height_nonvanishing [ModularFormClass F Γ k] (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) (hf : (⇑f : ℍ → ℂ) ≠ 0) :
    ∃ H : ℝ, ∀ p : ℍ, H ≤ (p : ℂ).im → f p ≠ 0 := by
  have h_ev : ∀ᶠ p : ℍ in atImInfty, cuspFunction h f (Function.Periodic.qParam h ↑p) ≠ 0 :=
    ((Function.Periodic.qParam_tendsto hh).comp tendsto_coe_atImInfty).eventually
      (cuspFunction_eventually_ne_zero hh hΓ hf)
  obtain ⟨H, hH⟩ := (atImInfty_mem _).mp h_ev
  refine ⟨H, fun p hp hfp ↦ hH p (by rwa [UpperHalfPlane.coe_im] at hp) ?_⟩
  rw [← SlashInvariantFormClass.eq_cuspFunction f p hΓ hh.ne'] at hfp
  exact hfp

/-- The set of points of the fundamental domain at which the vanishing order of a nonzero
level-one modular form is nonzero is finite. -/
lemma finite_zeros_in_fd [ModularFormClass F 𝒮ℒ k] (hf : (⇑f : ℍ → ℂ) ≠ 0) :
    Set.Finite {p : ℍ | p ∈ 𝒟 ∧ orderOfVanishingAt f p ≠ 0} := by
  obtain ⟨H₀, hH₀_no⟩ := exists_height_nonvanishing one_pos (by simp) hf
  have hK : IsCompact (UpperHalfPlane.coe '' ModularGroup.truncatedFundamentalDomain H₀) :=
    (ModularGroup.isCompact_truncatedFundamentalDomain H₀).image continuous_coe
  have hK_im : ∀ z ∈ UpperHalfPlane.coe '' ModularGroup.truncatedFundamentalDomain H₀,
      0 < z.im := by
    rintro _ ⟨q, -, rfl⟩
    exact q.im_pos
  have h_mero : MeromorphicOn (⇑f ∘ ofComplex)
      (UpperHalfPlane.coe '' ModularGroup.truncatedFundamentalDomain H₀) := fun z hz ↦
    (analyticAt_comp_ofComplex (ModularFormClass.holo f) (hK_im z hz)).meromorphicAt
  have h_fin := MeromorphicOn.divisor_support_finite_of_subset h_mero hK subset_rfl
  refine (h_fin.preimage UpperHalfPlane.coe_injective.injOn).subset ?_
  rintro p ⟨hp_fd, hp_ord⟩
  have h_zero : f p = 0 := by
    by_contra hne'
    exact hp_ord ((orderOfVanishingAt_eq_zero_iff (ModularFormClass.holo f) hf).mpr hne')
  have hpK : (p : ℂ) ∈ UpperHalfPlane.coe '' ModularGroup.truncatedFundamentalDomain H₀ :=
    ⟨p, ⟨hp_fd, by by_contra! h_gt; exact hH₀_no p h_gt.le h_zero⟩, rfl⟩
  rw [Set.mem_preimage, Function.mem_support, ne_eq,
    MeromorphicOn.divisor_apply h_mero hpK]
  intro h0
  exact hp_ord (by rwa [orderOfVanishingAt_def])

end ModularForm

end TauCeti

end

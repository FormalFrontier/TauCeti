/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Modular
public import TauCeti.NumberTheory.ModularForms.Order.AtCusp
public import TauCeti.NumberTheory.ModularForms.Order.OfVanishing


/-!
# Finite zeros of a level-one modular form in the fundamental domain `𝒟`

A nonzero level-one modular form does not vanish above some height, since its cusp
function is nonvanishing on a punctured `q`-ball; its remaining nonzero-order points in
the standard fundamental domain lie in a truncated fundamental domain, which is compact,
so by the accumulation-point argument and the identity theorem they are finite — the
finite-support input to the valence formula.

The statement carries no nonvanishing hypothesis: the zero form has order `0` at every
point (`TauCeti.orderOfVanishingAt_zero`), so the set is empty and finiteness is trivial.
That is what lets the orbit-level finite-support statements downstream drop theirs too.

⚠ `𝒟` here is the fundamental domain of `𝒮ℒ`, and this file is level-one throughout. The
general-level analogue is **not** obtained by widening the group while keeping this region:
for `Γ` of relative index `n > 1` an `𝒮ℒ`-orbit splits into up to `n` `Γ`-orbits, and `𝒟`
need not meet all of them, so bounding the zeros inside `𝒟` does not bound the order divisor
on `Γ \ ℍ`. (It can meet more than one: `𝒟` is closed, and its boundary carries `𝒮ℒ`-equivalent
representatives — the two vertical edges under `T`, the two arc halves under `S` — which may
fall in distinct `Γ`-orbits.) The general statement belongs at the orbit level, downstream of
`TauCeti.ModularForm.orderOfVanishingOnOrbit`.

## Main declarations

* `TauCeti.ModularForm.exists_height_nonvanishing`: a nonzero form does not vanish at
  points of imaginary part above some height.
* `TauCeti.ModularForm.finite_zeros_in_fd`: finiteness of the nonzero-order points of a
  level-one form lying in `𝒟`.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB), Chris Birkbeck,
  Apache 2.0, commit `2baa76f742bdb4fb8ee323fabba41203bd390e08` — `finite_zeros_in_fd` is
  ported from `finite_zeros_in_fdFM`
  (`projects/LeanModularForms/LeanModularForms/ForMathlib/Orbits.lean`), through the same
  compact-truncation architecture as `modularForm_finitely_many_zeros_in_fdBox`
  (`ForMathlib/ModularInvariance.lean`). Dropping the source's nonvanishing hypothesis is
  new here, and rests on TauCeti's `untop₀` order-zero convention.
-/

public noncomputable section

open Complex Filter Metric Set UpperHalfPlane TauCeti.UpperHalfPlane

open scoped ModularForm MatrixGroups Modular Topology

namespace TauCeti

namespace ModularForm

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {F : Type*} [FunLike F ℍ ℂ] {f : F} {h : ℝ}

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

/-- The points of the level-one fundamental domain `𝒟` at which a level-one modular form has
nonzero vanishing order are finite in number.

No nonvanishing hypothesis: the zero form has order `0` at every point, so the set is empty
and finiteness is trivial. -/
lemma finite_zeros_in_fd [ModularFormClass F 𝒮ℒ k] :
    Set.Finite {p : ℍ | p ∈ 𝒟 ∧ orderOfVanishingAt f p ≠ 0} := by
  rcases eq_or_ne (⇑f : ℍ → ℂ) 0 with hf | hf
  · simp [hf]
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

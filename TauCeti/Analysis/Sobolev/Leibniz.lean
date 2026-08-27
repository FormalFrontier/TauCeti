/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv

/-!
# The product rule for weak derivatives

A weak derivative is additive and commutes with scalars
(`TauCeti.HasWeakLineDerivOn.add`, `TauCeti.HasWeakLineDerivOn.const_smul`), but Lane A of the PDE
roadmap needs one more algebraic rule before it can localize: multiplication by a *variable*
smooth factor.  This file proves it.  For a smooth `ψ : E → ℝ` and a weakly differentiable `u`,

`∂_v (ψ u) = ψ ∂_v u + (∂_v ψ) u`

on `Ω`, in the weak sense of `TauCeti.HasWeakLineDerivOn`.

The proof is the one-line distributional computation.  Testing `ψ u` against `∂_v φ` is the same
as testing `u` against `ψ ∂_v φ = ∂_v (ψ φ) − (∂_v ψ) φ`, and `ψ φ` is again a test function on
`Ω`, because multiplying by a smooth function neither enlarges a support nor destroys smoothness.
So the defining identity for `u` applies to it, and the leftover term `(∂_v ψ) φ` is the second
summand of the Leibniz formula.  No smoothness of `u` is used, and no boundary hypothesis on `Ω`:
`ψ φ` is compactly supported *inside* `Ω`, so no boundary term appears.

Smoothness of `ψ` is more than the identity needs — `C¹` would do — but it is what makes `ψ φ` a
member of Mathlib's `TestFunction` type, whose smoothness order is `∞`, and it is what every
intended application supplies (cutoffs are built from `ContDiffBump`).

## Why this is the localization tool

`ψ` will be a cutoff.  Multiplying by one is how a global statement about `W^{k,p}(Ω)` is reduced
to a local one: it is the first step of the Meyers–Serrin `H = W` density theorem and of the
extension operator (Lane A.2 and A.6 of `TauCetiRoadmap/PDE/README.md`), and it is what turns an
interior estimate into an estimate on a compactly contained subdomain (Lane E.20).  The second
summand `(∂_v ψ) u` is exactly the error such an argument has to absorb, so having it with an
explicit, non-asymptotic formula is the point.

## Main declarations

* `TauCeti.HasWeakLineDerivOn.contDiff_smul`: the Leibniz rule in a direction `v`.
* `TauCeti.HasWeakFDerivOn.contDiff_smul`: its Fréchet form, with the rank-one correction
  `(fderiv ℝ ψ x).smulRight (u x)`.
* `TauCeti.HasWeakFDerivOn.contDiff_smul_gradient`: the form consumed by `TauCeti.W1p`, where a
  weak derivative of a scalar function is recorded by its Riesz representative and the rule reads
  `∇(ψ u) = ψ ∇u + u ∇ψ`.

## References

L. C. Evans, *Partial Differential Equations*, §5.2.3, Theorem 1(iv).
-/

public section

namespace TauCeti

open MeasureTheory TopologicalSpace
open scoped ContDiff Distributions

section General

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace E] [OpensMeasurableSpace E]
  [LocallyCompactSpace E] {Ω : Opens E} {v : E} {μ : Measure E} {u u' : E → F} {ψ : E → ℝ}

omit [MeasurableSpace E] [OpensMeasurableSpace E] [LocallyCompactSpace E] in
/-- A directional derivative of a smooth function is smooth. -/
private theorem contDiff_fderiv_apply (hψ : ContDiff ℝ ∞ ψ) (v : E) :
    ContDiff ℝ ∞ fun x => fderiv ℝ ψ x v :=
  (hψ.fderiv_right (by simp)).clm_apply contDiff_const

/-- **The Leibniz rule for weak directional derivatives.** If `u'` is a weak derivative of `u` in
the direction `v` on `Ω` and `ψ` is smooth, then `ψ u` is weakly differentiable in the direction
`v` on `Ω`, with derivative `ψ u' + (∂_v ψ) u`.

Nothing is assumed about `Ω` beyond openness: the test function `ψ φ` used in the proof is still
compactly supported inside `Ω`, so the boundary term of the classical integration by parts is
absent here just as it is in the definition. -/
theorem HasWeakLineDerivOn.contDiff_smul (h : HasWeakLineDerivOn μ Ω u u' v)
    (hψ : ContDiff ℝ ∞ ψ) :
    HasWeakLineDerivOn μ Ω (fun x => ψ x • u x)
      (fun x => ψ x • u' x + fderiv ℝ ψ x v • u x) v := by
  have hΩ : IsLocallyClosed (Ω : Set E) := Ω.isOpen.isLocallyClosed
  have hdψ : ContDiff ℝ ∞ fun x => fderiv ℝ ψ x v := contDiff_fderiv_apply hψ v
  have hu : LocallyIntegrableOn (fun x => ψ x • u x) Ω μ :=
    h.locallyIntegrableOn.continuousOn_smul hΩ hψ.continuous.continuousOn
  have hu' : LocallyIntegrableOn (fun x => ψ x • u' x + fderiv ℝ ψ x v • u x) Ω μ :=
    (h.locallyIntegrableOn_deriv.continuousOn_smul hΩ hψ.continuous.continuousOn).add
      (h.locallyIntegrableOn.continuousOn_smul hΩ hdψ.continuous.continuousOn)
  rw [hasWeakLineDerivOn_iff_testFunction]
  refine ⟨h.completeSpace, hu, hu', fun φ => ?_⟩
  -- `ψ φ` and `(∂_v ψ) φ` are test functions on `Ω`: smoothness is preserved by products and
  -- the support only shrinks.
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : 𝓓(Ω, ℝ), (Φ : E → ℝ) = ψ * (φ : E → ℝ) :=
    ⟨⟨ψ * (φ : E → ℝ), hψ.mul φ.contDiff, φ.hasCompactSupport.mul_left,
      tsupport_mul_subset_right.trans φ.tsupport_subset⟩, rfl⟩
  obtain ⟨Ψ, hΨ⟩ :
      ∃ Ψ : 𝓓(Ω, ℝ), (Ψ : E → ℝ) = (fun x => fderiv ℝ ψ x v) * (φ : E → ℝ) :=
    ⟨⟨(fun x => fderiv ℝ ψ x v) * (φ : E → ℝ), hdψ.mul φ.contDiff,
      φ.hasCompactSupport.mul_left,
      tsupport_mul_subset_right.trans φ.tsupport_subset⟩, rfl⟩
  have hint1 : Integrable (fun x => lineDeriv ℝ (Φ : E → ℝ) x v • u x) μ :=
    integrable_lineDeriv_smul_of_locallyIntegrableOn h.locallyIntegrableOn Φ v
  have hint2 : Integrable (fun x => (Ψ : E → ℝ) x • u x) μ :=
    integrable_smul_of_locallyIntegrableOn h.locallyIntegrableOn Ψ
  have hint3 : Integrable (fun x => (Φ : E → ℝ) x • u' x) μ :=
    integrable_smul_of_locallyIntegrableOn h.locallyIntegrableOn_deriv Φ
  -- The classical product rule for the smooth factors.
  have hlineΦ : ∀ x, lineDeriv ℝ (Φ : E → ℝ) x v
      = ψ x * lineDeriv ℝ (φ : E → ℝ) x v + (Ψ : E → ℝ) x := by
    intro x
    have hdψx : DifferentiableAt ℝ ψ x := (hψ.differentiable (by simp)) x
    have hdφx : DifferentiableAt ℝ (φ : E → ℝ) x := (φ.contDiff.differentiable (by simp)) x
    have hmul : DifferentiableAt ℝ (ψ * (φ : E → ℝ)) x := hdψx.mul hdφx
    rw [hΦ, hΨ, hmul.lineDeriv_eq_fderiv, hdφx.lineDeriv_eq_fderiv, fderiv_mul hdψx hdφx]
    simp only [add_apply, FunLike.coe_smul, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    ring
  have hsplit : ∫ x, (φ : E → ℝ) x • (ψ x • u' x + fderiv ℝ ψ x v • u x) ∂μ
      = ∫ x, (Φ : E → ℝ) x • u' x ∂μ + ∫ x, (Ψ : E → ℝ) x • u x ∂μ := by
    rw [← integral_add hint3 hint2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hΦ, hΨ, Pi.mul_apply, smul_add, smul_smul, mul_comm]
  calc ∫ x, lineDeriv ℝ (φ : E → ℝ) x v • (ψ x • u x) ∂μ
      = ∫ x, (lineDeriv ℝ (Φ : E → ℝ) x v • u x - (Ψ : E → ℝ) x • u x) ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [hlineΦ x, add_smul, add_sub_cancel_right, smul_smul, mul_comm]
    _ = ∫ x, lineDeriv ℝ (Φ : E → ℝ) x v • u x ∂μ - ∫ x, (Ψ : E → ℝ) x • u x ∂μ :=
        integral_sub hint1 hint2
    _ = -∫ x, (Φ : E → ℝ) x • u' x ∂μ - ∫ x, (Ψ : E → ℝ) x • u x ∂μ := by
        rw [h.integral_lineDeriv_smul_eq_neg_integral_smul Φ]
    _ = -∫ x, (φ : E → ℝ) x • (ψ x • u' x + fderiv ℝ ψ x v • u x) ∂μ := by
        rw [hsplit]; abel

/-- **The Leibniz rule for weak Fréchet derivatives**: `D(ψ u) = ψ Du + u ⊗ Dψ`, the correction
being the rank-one map `v ↦ (Dψ v) u`. -/
theorem HasWeakFDerivOn.contDiff_smul {U : E → E →L[ℝ] F} (h : HasWeakFDerivOn μ Ω u U)
    (hψ : ContDiff ℝ ∞ ψ) :
    HasWeakFDerivOn μ Ω (fun x => ψ x • u x)
      (fun x => ψ x • U x + (fderiv ℝ ψ x).smulRight (u x)) := by
  rw [hasWeakFDerivOn_iff]
  intro v
  have hv := (h.hasWeakLineDerivOn v).contDiff_smul hψ
  convert hv using 2 with x
  simp

end General

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [FiniteDimensional ℝ E] {Ω : Opens E} {μ : Measure E}
  {a ψ : E → ℝ} {g : E → E}

open scoped Gradient

/-- **The Leibniz rule in gradient form**: `∇(ψ a) = ψ ∇a + a ∇ψ`.

This is the shape `TauCeti.W1p` stores a weak derivative in — a scalar function together with the
Riesz representative of its weak Fréchet derivative — so it is the form a multiplication operator
on the Sobolev space consumes. -/
theorem HasWeakFDerivOn.contDiff_smul_gradient
    (h : HasWeakFDerivOn μ Ω a fun x => innerSL ℝ (g x)) (hψ : ContDiff ℝ ∞ ψ) :
    HasWeakFDerivOn μ Ω (fun x => ψ x • a x)
      (fun x => innerSL ℝ (ψ x • g x + a x • ∇ ψ x)) := by
  have hv := h.contDiff_smul hψ
  convert hv using 2 with x
  ext w
  simp [inner_gradient_left (𝕜 := ℝ) (f := ψ) (x := x), mul_comm]

end InnerProduct

end TauCeti

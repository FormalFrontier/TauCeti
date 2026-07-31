/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity

/-!
# The area of the image of a holomorphic map

Where its derivative does not vanish a holomorphic map is conformal: at such a point `z` it acts on
the plane as a rotation followed by a dilation of ratio `‖deriv f z‖`. At every point, critical or
not, it multiplies infinitesimal area by `‖deriv f z‖ ^ 2`. Integrating that pointwise distortion
over a set on which `f` is injective gives the **area formula**,
`volume (f '' s) = ∫⁻ z in s, ‖deriv f z‖ₑ ^ 2`,
and its immediate corollary that a holomorphic injection whose image has finite area has a finite
Dirichlet integral `∫⁻ z in s, ‖deriv f z‖ₑ ^ 2`.

That finiteness is the analytic input of the *length–area method*, the classical route to layer
**L5** of the conformal-mapping roadmap (`ConformalMapping/README.md`), Carathéodory's boundary
correspondence: for a conformal map of the disc onto a bounded domain, the finite Dirichlet
integral is spent along the circular arcs `{z ∈ ball 0 1 | ‖z - ζ‖ = ρ}` approaching a boundary
point `ζ`, so by Cauchy–Schwarz the images of those arcs must be short for some arbitrarily small
`ρ`, which is what forces the boundary cluster set at `ζ` to degenerate to a point. The topological
half of that argument is already on `main`: `TauCeti.exists_continuousOn_closure_eqOn` turns a
subsingleton cluster set into a continuous extension. The analytic half, of which the area formula
is the first component, is not; the degeneracy itself is not proved here.

The proof is Mathlib's change-of-variables formula
`MeasureTheory.lintegral_abs_det_fderiv_eq_addHaar_image₀` for an injective differentiable map,
applied to `f` viewed as a map of the real plane. The only complex-analytic input is the value of
the Jacobian determinant: the `ℝ`-linear map underlying multiplication by `c : ℂ` has determinant
`Complex.normSq c = ‖c‖ ^ 2`, which is the private `det_restrictScalars_smulRight_one` below and
comes from `Algebra.norm_complex_eq` through `LinearMap.det_restrictScalars`. Injectivity is what
makes the formula an equality rather than the inequality
`TauCeti.volume_image_le_lintegral_enorm_deriv_sq`, which holds for any holomorphic map because a
non-injective map covers parts of its image more than once.

In accordance with the generality bar of `ConformalMapping/README.md`, which fixes scalar `ℂ` for
every theorem added in layers L0–L6, the results below are stated for maps of `ℂ`. The hypotheses
are the roadmap's: an open domain `U`, `DifferentiableOn ℂ f U`, and `Set.InjOn`. Statements are
made for an arbitrary `s ⊆ U` rather than for `U` itself, because the length–area argument
integrates over the sub-annuli `U ∩ {z | ρ₁ < ‖z - ζ‖ < ρ₂}`, not over `U`; take `s = U` with
`hUo.measurableSet` and `subset_rfl` for the plain domain form. The area formula and the
finiteness it gives ask only for `MeasureTheory.NullMeasurableSet s volume`, as Mathlib's
change of variables does; the Bochner-integral forms ask for `MeasurableSet s`, which is what
turns the continuity of `deriv f` into strong measurability on `s`.

## Main results

* `TauCeti.volume_image_eq_lintegral_enorm_deriv_sq` — the area formula: the area of the image of
  a set on which a holomorphic map is injective is the integral of `‖deriv f‖ ^ 2` over it.
* `TauCeti.volume_image_le_lintegral_enorm_deriv_sq` — the inequality form, with no injectivity.
* `TauCeti.lintegral_enorm_deriv_sq_ne_top` and `TauCeti.integrableOn_norm_deriv_sq` — a
  holomorphic injection whose image has finite area has a finite Dirichlet integral;
  `TauCeti.lintegral_enorm_deriv_sq_ne_top_of_isBounded` and
  `TauCeti.integrableOn_norm_deriv_sq_of_isBounded` are the forms taking a bounded image.
* `TauCeti.integral_norm_deriv_sq_eq_toReal_volume_image` — the Bochner-integral form of the area
  formula.
* `TauCeti.volume_image_eq_zero_iff` — a holomorphic injection whose derivative is almost
  everywhere nonzero carries null sets to null sets and back.
* `TauCeti.lintegral_enorm_deriv_sq_eq_pi_of_image_eq_ball` — the Dirichlet integral of a Riemann
  map is exactly `π`.

## Coordination with upstream Mathlib

Mathlib has the change-of-variables formula but no area formula for holomorphic maps: a grep of
the pinned Mathlib for `lintegral_abs_det_fderiv` finds only the polar-coordinate and
upper-half-plane applications, neither of which computes the area of a conformal image. Layer L5 is
absent from [mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), the
in-progress human-curated Riemann-mapping-theorem effort, which stops at the mapping theorem
itself, so this file is new Lean formalization rather than a temporary shim.

## References

* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, §2.2 (the length–area method).
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. IX.
* P. L. Duren, *Univalent Functions*, Ch. 2 (the area theorem).
-/

public section

namespace TauCeti

open Bornology Complex MeasureTheory Metric Set

variable {U s : Set ℂ} {f : ℂ → ℂ}

/-- **The Jacobian of a complex dilation-rotation.** Multiplication by `c : ℂ`, read as an
`ℝ`-linear map of the plane, has determinant `‖c‖ ^ 2`: it is the rotation by `arg c` scaled by
`‖c‖`, and a dilation of ratio `‖c‖` multiplies area by `‖c‖ ^ 2`.

The map is written as `ContinuousLinearMap.smulRight 1 c` because that is the shape in which
`HasDerivAt.hasFDerivAt` presents the Fréchet derivative of a function of one complex variable. -/
private theorem det_restrictScalars_smulRight_one (c : ℂ) :
    ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ).det = ‖c‖ ^ 2 := by
  have h : ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c
      = ContinuousLinearMap.toSpanSingleton ℂ c := by
    ext; simp [ContinuousLinearMap.toSpanSingleton]
  simp [h, ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_eq,
    Complex.normSq_eq_norm_sq]

/-- At each point of a subset `s` of an open set on which `f` is holomorphic, the `ℝ`-linear
derivative of `f` relative to `s` is multiplication by `deriv f z`. This is the family of
derivatives the change-of-variables formula is applied to. -/
private theorem hasFDerivWithinAt_smulRight_deriv (hUo : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hsU : s ⊆ U) {z : ℂ} (hz : z ∈ s) :
    HasFDerivWithinAt f
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv f z)).restrictScalars ℝ) s z :=
  (((hf z (hsU hz)).differentiableAt (hUo.mem_nhds (hsU hz))).hasDerivAt.hasFDerivAt.restrictScalars
    ℝ).hasFDerivWithinAt

/-- The pointwise area distortion, in the form the change-of-variables formula produces it. -/
private theorem ofReal_abs_det_eq (c : ℂ) :
    ENNReal.ofReal
        |((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ).det| = ‖c‖ₑ ^ 2 := by
  rw [det_restrictScalars_smulRight_one, abs_of_nonneg (by positivity), ← ofReal_norm,
    ENNReal.ofReal_pow (norm_nonneg _)]

/-- **The area formula.** If `f` is holomorphic on an open set `U` and injective on a null
measurable `s ⊆ U`, then the area of `f '' s` is the integral over `s` of the area distortion
`‖deriv f z‖ ^ 2`.

Injectivity is essential: without it the map covers part of its image more than once and only the
inequality `TauCeti.volume_image_le_lintegral_enorm_deriv_sq` survives. -/
theorem volume_image_eq_lintegral_enorm_deriv_sq (hUo : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hs : NullMeasurableSet s volume) (hsU : s ⊆ U) (hinj : InjOn f s) :
    volume (f '' s) = ∫⁻ z in s, ‖deriv f z‖ₑ ^ 2 := by
  rw [← MeasureTheory.lintegral_abs_det_fderiv_eq_addHaar_image₀ volume hs
    (fun z hz => hasFDerivWithinAt_smulRight_deriv hUo hf hsU hz) hinj]
  exact lintegral_congr fun z => ofReal_abs_det_eq (deriv f z)

/-- **The area inequality for a holomorphic map.** Dropping injectivity from the area formula
leaves an inequality, since a map that covers a part of its image several times spends more of the
integral `∫⁻ z in s, ‖deriv f z‖ₑ ^ 2` than the area of the image accounts for. -/
theorem volume_image_le_lintegral_enorm_deriv_sq (hUo : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hs : MeasurableSet s) (hsU : s ⊆ U) :
    volume (f '' s) ≤ ∫⁻ z in s, ‖deriv f z‖ₑ ^ 2 := by
  refine le_trans (MeasureTheory.addHaar_image_le_lintegral_abs_det_fderiv volume hs
    (fun z hz => hasFDerivWithinAt_smulRight_deriv hUo hf hsU hz)) ?_
  exact le_of_eq (lintegral_congr fun z => ofReal_abs_det_eq (deriv f z))

/-- The area distortion of a holomorphic map is continuous, because the derivative of a holomorphic
function is again holomorphic. -/
private theorem continuousOn_norm_deriv_sq (hUo : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hsU : s ⊆ U) : ContinuousOn (fun z => ‖deriv f z‖ ^ 2) s :=
  ((((hf.analyticOnNhd hUo).deriv).continuousOn).mono hsU).norm.pow 2

/-- **A holomorphic injection whose image has finite area has a finite Dirichlet integral.** This is
the finiteness that the length–area method spends: the whole of `∫⁻ z in s, ‖deriv f z‖ₑ ^ 2` is
available to bound the lengths of the images of the circular arcs approaching a boundary point, so
all but finitely much of it must be spread thinly. -/
theorem lintegral_enorm_deriv_sq_ne_top (hUo : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hs : NullMeasurableSet s volume) (hsU : s ⊆ U) (hinj : InjOn f s)
    (hfin : volume (f '' s) ≠ ⊤) :
    ∫⁻ z in s, ‖deriv f z‖ₑ ^ 2 ≠ ⊤ := by
  rwa [← volume_image_eq_lintegral_enorm_deriv_sq hUo hf hs hsU hinj]

/-- The bounded-image form of `TauCeti.lintegral_enorm_deriv_sq_ne_top`: a holomorphic injection
with bounded image has a finite Dirichlet integral. -/
theorem lintegral_enorm_deriv_sq_ne_top_of_isBounded (hUo : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hs : NullMeasurableSet s volume) (hsU : s ⊆ U)
    (hinj : InjOn f s) (hb : IsBounded (f '' s)) :
    ∫⁻ z in s, ‖deriv f z‖ₑ ^ 2 ≠ ⊤ :=
  lintegral_enorm_deriv_sq_ne_top hUo hf hs hsU hinj hb.measure_lt_top.ne

/-- The Bochner-integrability form of `TauCeti.lintegral_enorm_deriv_sq_ne_top`: the area distortion
of a holomorphic injection whose image has finite area is integrable. Measurability is free because
the derivative of a holomorphic function is again holomorphic, hence continuous. -/
theorem integrableOn_norm_deriv_sq (hUo : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hs : MeasurableSet s) (hsU : s ⊆ U) (hinj : InjOn f s) (hfin : volume (f '' s) ≠ ⊤) :
    IntegrableOn (fun z => ‖deriv f z‖ ^ 2) s := by
  refine ⟨(continuousOn_norm_deriv_sq hUo hf hsU).aestronglyMeasurable hs, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun z => ?_))
    (lt_top_iff_ne_top.mpr
      (lintegral_enorm_deriv_sq_ne_top hUo hf hs.nullMeasurableSet hsU hinj hfin))
  rw [Real.enorm_eq_ofReal (by positivity), ← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]

/-- The bounded-image form of `TauCeti.integrableOn_norm_deriv_sq`: the area distortion of a
holomorphic injection with bounded image is integrable. -/
theorem integrableOn_norm_deriv_sq_of_isBounded (hUo : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hs : MeasurableSet s) (hsU : s ⊆ U) (hinj : InjOn f s) (hb : IsBounded (f '' s)) :
    IntegrableOn (fun z => ‖deriv f z‖ ^ 2) s :=
  integrableOn_norm_deriv_sq hUo hf hs hsU hinj hb.measure_lt_top.ne

/-- **The area formula, Bochner form.** The area of the image of a holomorphic injection is the
ordinary integral of the area distortion.

No finiteness is needed: if the area distortion is not integrable then both sides are `0`, the
Bochner integral by convention and the right-hand side because `(⊤ : ℝ≥0∞).toReal = 0`. -/
theorem integral_norm_deriv_sq_eq_toReal_volume_image (hUo : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hs : MeasurableSet s) (hsU : s ⊆ U) (hinj : InjOn f s) :
    ∫ z in s, ‖deriv f z‖ ^ 2 = (volume (f '' s)).toReal := by
  rw [volume_image_eq_lintegral_enorm_deriv_sq hUo hf hs.nullMeasurableSet hsU hinj,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun z => by positivity)
      ((continuousOn_norm_deriv_sq hUo hf hsU).aestronglyMeasurable hs)]
  congr 1
  refine lintegral_congr fun z => ?_
  rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]

/-- **A holomorphic injection carries null sets to null sets and back.** Where the derivative is
almost everywhere nonzero, the image of a measurable set is null exactly when the set is.

The nonvanishing is not an extra assumption in the intended case `s = U`: a holomorphic map
injective on the open set `U` has nonvanishing derivative throughout `U`, by
`TauCeti.not_injOn_of_deriv_eq_zero`, so `MeasureTheory.ae_restrict_of_forall_mem` supplies `hd`. It
is kept as a hypothesis so that the statement also covers a proper subset `s`, which need not be a
neighbourhood of its points.

Only the forward implication needs the derivative: a differentiable map carries null sets to null
sets whatever its derivative does, whereas a set of positive measure has a null image only if the
area distortion `‖deriv f‖ ^ 2` vanishes on much of it. -/
theorem volume_image_eq_zero_iff (hUo : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hs : MeasurableSet s) (hsU : s ⊆ U) (hinj : InjOn f s)
    (hd : ∀ᵐ z ∂volume.restrict s, deriv f z ≠ 0) :
    volume (f '' s) = 0 ↔ volume s = 0 := by
  have hm : AEMeasurable (fun z => ‖deriv f z‖ₑ ^ 2) (volume.restrict s) :=
    ((((hf.analyticOnNhd hUo).deriv).continuousOn).mono hsU).aemeasurable hs |>.enorm.pow_const 2
  rw [volume_image_eq_lintegral_enorm_deriv_sq hUo hf hs.nullMeasurableSet hsU hinj,
    lintegral_eq_zero_iff' hm]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hfalse : ∀ᵐ z ∂volume.restrict s, False := by
      filter_upwards [h, hd] with z hz hz0
      exact hz0 (enorm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hz))
    simpa [ae_iff, Measure.restrict_apply_univ] using hfalse
  · rw [MeasureTheory.Measure.restrict_eq_zero.mpr h, ae_zero]
    exact Filter.eventually_bot

/-- **The Dirichlet integral of a Riemann map is `π`.** A holomorphic injection of an open set onto
the unit disc spends exactly the area of the disc.

The hypotheses are those of the conclusion of the Riemann mapping theorem
`TauCeti.riemannMapping`, so the statement is not vacuous: every nonempty simply connected proper
open subset of `ℂ` carries such an `f`. -/
theorem lintegral_enorm_deriv_sq_eq_pi_of_image_eq_ball (hUo : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hinj : InjOn f U) (himg : f '' U = ball 0 1) :
    ∫⁻ z in U, ‖deriv f z‖ₑ ^ 2 = ENNReal.ofReal Real.pi := by
  rw [← volume_image_eq_lintegral_enorm_deriv_sq hUo hf hUo.measurableSet.nullMeasurableSet
    subset_rfl hinj, himg, Complex.volume_ball]
  simp [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]

end TauCeti

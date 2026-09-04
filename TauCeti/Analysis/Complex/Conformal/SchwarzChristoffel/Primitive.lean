/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Conformal
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Integrand
public import TauCeti.Analysis.Complex.UpperHalfPlane.Primitive

/-!
# The Schwarz--Christoffel primitive

The Schwarz--Christoffel map is obtained by integrating the product of complex powers attached to
its real prevertices.  This file constructs the globally defined primitive on the upper half-plane,
normalized to vanish at an arbitrary base point there.

For prevertices `a`, turning exponents `e`, and a base point `z₀`,
`schwarzChristoffelPrimitive a e z₀ z` is the integral of
`schwarzChristoffelIntegrand a e` along the horizontal-then-vertical polygonal path from `z₀` to
`z`.  Holomorphy of the integrand and convexity of the upper half-plane make these wedge integrals
additive.  The primitive has the prescribed derivative everywhere in the upper half-plane and is
conformal there because that derivative never vanishes.  Its normalization characterizes it
uniquely among all primitives of the same integrand.

These properties provide the analytic map used in the Schwarz--Christoffel formula.  Identifying
its boundary values, its straight image edges, and its image as the intended polygon requires
separate boundary analysis.

## Main definitions

* `TauCeti.schwarzChristoffelPrimitive` -- the primitive normalized to vanish at a chosen point of
  the upper half-plane.

## Main results

* `TauCeti.hasDerivAt_schwarzChristoffelPrimitive` -- its derivative is the
  Schwarz--Christoffel integrand.
* `TauCeti.schwarzChristoffelPrimitive_change_base` -- changing the normalization point subtracts
  the value at the new base point.
* `TauCeti.conformalAt_schwarzChristoffelPrimitive` -- it is conformal throughout the upper
  half-plane.
* `TauCeti.eqOn_schwarzChristoffelPrimitive` -- the derivative and normalization uniquely
  characterize it on the upper half-plane.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

noncomputable section

namespace TauCeti

open Complex UpperHalfPlane

variable {ι : Type*} [Fintype ι]

/-- The **normalized Schwarz--Christoffel primitive** associated to real prevertices `a` and
turning exponents `e`.  It is the integral of `schwarzChristoffelIntegrand a e` from the chosen
upper-half-plane base point `z₀` to `z`, along a horizontal segment followed by a vertical one.

The definition is total on `ℂ`, but its analytic interpretation is asserted on
`upperHalfPlaneSet`. -/
noncomputable def schwarzChristoffelPrimitive (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (z : ℂ) : ℂ :=
  wedgeIntegral (z₀ : ℂ) z (schwarzChristoffelIntegrand a e)

/-- The normalized Schwarz--Christoffel primitive vanishes at its base point. -/
@[simp]
theorem schwarzChristoffelPrimitive_apply_base (a e : ι → ℝ) (z₀ : UpperHalfPlane) :
    schwarzChristoffelPrimitive a e z₀ z₀ = 0 := by
  simp [schwarzChristoffelPrimitive, wedgeIntegral]

/-- The derivative of the normalized Schwarz--Christoffel primitive is its integrand throughout
the upper half-plane. -/
theorem hasDerivAt_schwarzChristoffelPrimitive (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    {z : ℂ} (hz : z ∈ upperHalfPlaneSet) :
    HasDerivAt (schwarzChristoffelPrimitive a e z₀)
      (schwarzChristoffelIntegrand a e z) z := by
  exact (differentiableOn_schwarzChristoffelIntegrand a e).hasDerivAt_wedgeIntegral_upperHalfPlane
    z₀ hz

/-- Changing the base point of a normalized Schwarz--Christoffel primitive subtracts its value at
the new base point. -/
theorem schwarzChristoffelPrimitive_change_base (a e : ι → ℝ) (b c : UpperHalfPlane)
    {z : ℂ} (hz : z ∈ upperHalfPlaneSet) :
    schwarzChristoffelPrimitive a e b z =
      schwarzChristoffelPrimitive a e c z - schwarzChristoffelPrimitive a e c b := by
  symm
  exact (differentiableOn_schwarzChristoffelIntegrand a e).isConservativeOn
    |>.wedgeIntegral_sub_wedgeIntegral_eq_of_mem_upperHalfPlane
      (differentiableOn_schwarzChristoffelIntegrand a e).continuousOn c.coe_im_pos b.coe_im_pos hz

/-- The derivative of the normalized Schwarz--Christoffel primitive on the upper half-plane. -/
theorem deriv_schwarzChristoffelPrimitive (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    {z : ℂ} (hz : z ∈ upperHalfPlaneSet) :
    deriv (schwarzChristoffelPrimitive a e z₀) z = schwarzChristoffelIntegrand a e z :=
  (hasDerivAt_schwarzChristoffelPrimitive a e z₀ hz).deriv

/-- The normalized Schwarz--Christoffel primitive is holomorphic on the upper half-plane. -/
theorem differentiableOn_schwarzChristoffelPrimitive (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) :
    DifferentiableOn ℂ (schwarzChristoffelPrimitive a e z₀) upperHalfPlaneSet :=
  fun _ hz ↦
    (hasDerivAt_schwarzChristoffelPrimitive a e z₀ hz).differentiableAt.differentiableWithinAt

/-- The normalized Schwarz--Christoffel primitive is conformal at every point of the upper
half-plane. -/
theorem conformalAt_schwarzChristoffelPrimitive (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    {z : ℂ} (hz : z ∈ upperHalfPlaneSet) :
    ConformalAt (schwarzChristoffelPrimitive a e z₀) z := by
  exact (hasDerivAt_schwarzChristoffelPrimitive a e z₀ hz).differentiableAt.conformalAt
    (deriv_schwarzChristoffelPrimitive a e z₀ hz ▸
      schwarzChristoffelIntegrand_ne_zero a e hz)

/-- A primitive of the Schwarz--Christoffel integrand that vanishes at the chosen base point agrees
with `schwarzChristoffelPrimitive` throughout the upper half-plane. -/
theorem eqOn_schwarzChristoffelPrimitive (a e : ι → ℝ) (z₀ : UpperHalfPlane) {g : ℂ → ℂ}
    (hg : ∀ z ∈ upperHalfPlaneSet, HasDerivAt g (schwarzChristoffelIntegrand a e z) z)
    (hg₀ : g z₀ = 0) :
    upperHalfPlaneSet.EqOn g (schwarzChristoffelPrimitive a e z₀) := by
  apply isOpen_upperHalfPlaneSet.eqOn_of_deriv_eq (convex_halfSpace_im_gt 0).isPreconnected
    (fun z hz ↦ (hg z hz).differentiableAt.differentiableWithinAt)
    (differentiableOn_schwarzChristoffelPrimitive a e z₀)
    (fun z hz ↦ (hg z hz).deriv.trans (deriv_schwarzChristoffelPrimitive a e z₀ hz).symm)
    z₀.coe_im_pos
  simpa using hg₀

end TauCeti

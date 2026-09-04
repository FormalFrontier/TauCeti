/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import TauCeti.Analysis.Complex.UpperHalfPlane.Cpow

/-!
# The Schwarz--Christoffel integrand

The derivative in the Schwarz--Christoffel formula is, up to a nonzero constant, a finite
product

`∏ i, (z - a i) ^ e i`,

where the prevertices `a i` lie on the real axis and `e i` is the normalized turning exponent
at the corresponding polygon vertex.  For an interior angle `α i`, measured in radians, the
usual choice is `e i = α i / π - 1`.

This file defines that product using the principal complex power and establishes its analytic
properties on the upper half-plane.  Each difference `z - a i` lies in
`Complex.slitPlane` there, so the chosen branch is holomorphic.  The integrand is nowhere zero,
its norm is the product of the expected real powers, and its logarithmic derivative is the sum
of the simple fractions `e i / (z - a i)`.

These facts are the analytic input for constructing the Schwarz--Christoffel map as a primitive
of the integrand.  Nonvanishing will make that primitive locally conformal, while the real-power
norm formula provides estimates away from the prevertices.  Since complex powers are totalized
at zero, values of this definition at prevertices do not describe its boundary singularities;
those must instead be stated using punctured limits.

## Main definitions

* `TauCeti.schwarzChristoffelIntegrand` -- the finite product of the principal power factors.

## Main results

* `TauCeti.differentiableOn_schwarzChristoffelIntegrand` -- the integrand is holomorphic on the
  upper half-plane.
* `TauCeti.schwarzChristoffelIntegrand_ne_zero` -- it has no zero there.
* `TauCeti.norm_schwarzChristoffelIntegrand` -- its norm is the product of real powers of the
  distances to the prevertices.
* `TauCeti.logDeriv_schwarzChristoffelIntegrand` -- its logarithmic derivative is the expected
  sum of simple fractions.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

namespace TauCeti

open Complex Finset UpperHalfPlane

variable {ι : Type*} [Fintype ι]

/-- The **Schwarz--Christoffel integrand** associated to real prevertices `a i` and real
exponents `e i`.

For a polygon with interior angle `α i` at the vertex corresponding to `a i`, the classical
choice is `e i = α i / π - 1`.  The definition itself does not impose the polygonal angle
conditions: its analytic properties hold for every finite family of real exponents.  At a
prevertex, Mathlib's totalized zero-base power determines the value, which should not be
interpreted as analytic boundary data. -/
noncomputable def schwarzChristoffelIntegrand (a e : ι → ℝ) (z : ℂ) : ℂ :=
  ∏ i, (z - (a i : ℂ)) ^ (e i : ℂ)

/-- The Schwarz--Christoffel integrand is the product of its principal-power factors. -/
theorem schwarzChristoffelIntegrand_def (a e : ι → ℝ) (z : ℂ) :
    schwarzChristoffelIntegrand a e z = ∏ i, (z - (a i : ℂ)) ^ (e i : ℂ) :=
  (rfl)

/-- With every turning exponent zero, the Schwarz--Christoffel integrand is constant one. -/
@[simp]
theorem schwarzChristoffelIntegrand_zero (a : ι → ℝ) :
    schwarzChristoffelIntegrand a 0 = 1 := by
  ext z
  simp [schwarzChristoffelIntegrand]

/-- The Schwarz--Christoffel integrand is holomorphic on the open upper half-plane. -/
theorem differentiableOn_schwarzChristoffelIntegrand (a e : ι → ℝ) :
    DifferentiableOn ℂ (schwarzChristoffelIntegrand a e) upperHalfPlaneSet := by
  intro z hz
  exact DifferentiableWithinAt.fun_finsetProd fun i _ =>
    (differentiableAt_sub_cpow_of_im_pos hz (a i) (e i)).differentiableWithinAt

/-- The Schwarz--Christoffel integrand is nowhere zero in the upper half-plane.  Consequently,
any primitive of it is locally conformal there. -/
theorem schwarzChristoffelIntegrand_ne_zero (a e : ι → ℝ) {z : ℂ} (hz : z ∈ upperHalfPlaneSet) :
    schwarzChristoffelIntegrand a e z ≠ 0 := by
  rw [schwarzChristoffelIntegrand_def]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => sub_cpow_ne_zero_of_im_pos hz (a i) (e i)

/-- Adding two exponent families multiplies their Schwarz--Christoffel integrands at any point
off the prevertices.  The hypothesis is essential because the principal complex power is
additive in its exponent only away from a zero base. -/
theorem schwarzChristoffelIntegrand_add (a e d : ι → ℝ) {z : ℂ} (hz : ∀ i, z ≠ (a i : ℂ)) :
    schwarzChristoffelIntegrand a (e + d) z =
      schwarzChristoffelIntegrand a e z * schwarzChristoffelIntegrand a d z := by
  simp_rw [schwarzChristoffelIntegrand_def, Pi.add_apply, ofReal_add]
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ =>
    Complex.cpow_add _ _ (sub_ne_zero_of_ne (hz i))

/-- The norm of a Schwarz--Christoffel integrand is the product of the corresponding real powers
of the distances to its prevertices.  Both sides are totalized in the same way at a prevertex,
so no hypothesis on `z` is needed; the common value there is not analytic boundary data, which
has to be described by a punctured limit instead. -/
theorem norm_schwarzChristoffelIntegrand (a e : ι → ℝ) (z : ℂ) :
    ‖schwarzChristoffelIntegrand a e z‖ = ∏ i, dist z (a i : ℂ) ^ e i := by
  rw [schwarzChristoffelIntegrand_def, norm_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [Complex.norm_cpow_real, dist_eq]

/-- The logarithmic derivative of the Schwarz--Christoffel integrand is the sum of its simple
fractions.  Its possible poles are the real prevertices and hence lie on the boundary of the
domain of holomorphy. -/
theorem logDeriv_schwarzChristoffelIntegrand (a e : ι → ℝ) {z : ℂ}
    (hz : z ∈ upperHalfPlaneSet) :
    logDeriv (schwarzChristoffelIntegrand a e) z =
      ∑ i, (e i : ℂ) / (z - (a i : ℂ)) := by
  -- `logDeriv_fun_prod` rewrites a syntactic product of functions, so present the integrand
  -- as one before rewriting with it.
  have hfun : schwarzChristoffelIntegrand a e =
      fun w : ℂ => ∏ i, (w - (a i : ℂ)) ^ (e i : ℂ) :=
    funext (schwarzChristoffelIntegrand_def a e)
  rw [hfun, logDeriv_fun_prod]
  · exact Finset.sum_congr rfl fun i _ => logDeriv_sub_cpow_of_im_pos hz (a i) (e i)
  · exact fun i _ => sub_cpow_ne_zero_of_im_pos hz (a i) (e i)
  · exact fun i _ => differentiableAt_sub_cpow_of_im_pos hz (a i) (e i)

/-- The derivative of the Schwarz--Christoffel integrand, written as the integrand times its
logarithmic derivative. -/
theorem hasDerivAt_schwarzChristoffelIntegrand (a e : ι → ℝ) {z : ℂ}
    (hz : z ∈ upperHalfPlaneSet) :
    HasDerivAt (schwarzChristoffelIntegrand a e)
      (schwarzChristoffelIntegrand a e z *
        ∑ i, (e i : ℂ) / (z - (a i : ℂ))) z := by
  have hdiff : DifferentiableAt ℂ (schwarzChristoffelIntegrand a e) z :=
    (differentiableOn_schwarzChristoffelIntegrand a e z hz).differentiableAt
      (isOpen_upperHalfPlaneSet.mem_nhds hz)
  apply hdiff.hasDerivAt.congr_deriv
  have hlog := logDeriv_schwarzChristoffelIntegrand a e hz
  rw [logDeriv_apply] at hlog
  exact ((div_eq_iff (schwarzChristoffelIntegrand_ne_zero a e hz)).mp hlog).trans
    (mul_comm _ _)

/-- The derivative of the Schwarz--Christoffel integrand in the upper half-plane. -/
theorem deriv_schwarzChristoffelIntegrand (a e : ι → ℝ) {z : ℂ}
    (hz : z ∈ upperHalfPlaneSet) :
    deriv (schwarzChristoffelIntegrand a e) z =
      schwarzChristoffelIntegrand a e z *
        ∑ i, (e i : ℂ) / (z - (a i : ℂ)) :=
  (hasDerivAt_schwarzChristoffelIntegrand a e hz).deriv

end TauCeti

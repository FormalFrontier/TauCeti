/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

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
its norm is the product of the expected real powers, and its logarithmic derivative is the
sum of the simple fractions `e i / (z - a i)`.

These facts are the analytic input for constructing the Schwarz--Christoffel map as a primitive
of the integrand.  Nonvanishing will make that primitive locally conformal, while the real-power
norm formula controls its behaviour at the prevertices.

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
conditions: its analytic properties hold for every finite family of real exponents. -/
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

/-- Translating an upper-half-plane point by a real prevertex leaves it in the slit plane. -/
lemma sub_ofReal_mem_slitPlane_of_im_pos {z : ℂ} (hz : 0 < z.im) (x : ℝ) :
    z - (x : ℂ) ∈ slitPlane := by
  simp [slitPlane, hz.ne']

/-- A principal-power factor in the Schwarz--Christoffel integrand is differentiable at every
point of the upper half-plane. -/
lemma differentiableAt_cpow_sub_of_im_pos {z : ℂ} (hz : 0 < z.im) (x r : ℝ) :
    DifferentiableAt ℂ (fun w : ℂ => (w - (x : ℂ)) ^ (r : ℂ)) z :=
  (differentiableAt_id.sub_const (x : ℂ)).cpow_const
    (sub_ofReal_mem_slitPlane_of_im_pos hz x)

/-- The Schwarz--Christoffel integrand is holomorphic on the open upper half-plane. -/
theorem differentiableOn_schwarzChristoffelIntegrand (a e : ι → ℝ) :
    DifferentiableOn ℂ (schwarzChristoffelIntegrand a e) upperHalfPlaneSet := by
  intro z hz
  rw [show schwarzChristoffelIntegrand a e =
    (fun w => ∏ i, (w - (a i : ℂ)) ^ (e i : ℂ)) from
      funext (schwarzChristoffelIntegrand_def a e)]
  exact DifferentiableWithinAt.fun_finsetProd fun i _ =>
    (differentiableAt_cpow_sub_of_im_pos hz (a i) (e i)).differentiableWithinAt

/-- No principal-power factor in the Schwarz--Christoffel integrand vanishes in the upper
half-plane. -/
lemma cpow_sub_ne_zero_of_im_pos {z : ℂ} (hz : 0 < z.im) (x r : ℝ) :
    (z - (x : ℂ)) ^ (r : ℂ) ≠ 0 := by
  rw [Complex.cpow_ne_zero_iff]
  left
  intro h
  have := congr_arg Complex.im h
  simp only [sub_im, ofReal_im, sub_zero, zero_im] at this
  exact hz.ne' this

/-- The Schwarz--Christoffel integrand is nowhere zero in the upper half-plane.  Consequently,
any primitive of it is locally conformal there. -/
theorem schwarzChristoffelIntegrand_ne_zero (a e : ι → ℝ) {z : ℂ} (hz : z ∈ upperHalfPlaneSet) :
    schwarzChristoffelIntegrand a e z ≠ 0 := by
  rw [schwarzChristoffelIntegrand_def]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => cpow_sub_ne_zero_of_im_pos hz (a i) (e i)

/-- Adding two exponent families multiplies their Schwarz--Christoffel integrands in the upper
half-plane.  The domain hypothesis is essential because the principal complex power is additive
in its exponent only away from a zero base. -/
theorem schwarzChristoffelIntegrand_add (a e d : ι → ℝ) {z : ℂ}
    (hz : z ∈ upperHalfPlaneSet) :
    schwarzChristoffelIntegrand a (e + d) z =
      schwarzChristoffelIntegrand a e z * schwarzChristoffelIntegrand a d z := by
  simp_rw [schwarzChristoffelIntegrand_def, Pi.add_apply, ofReal_add,
    Complex.cpow_add _ _ (slitPlane_ne_zero (sub_ofReal_mem_slitPlane_of_im_pos hz _)),
    Finset.prod_mul_distrib]

/-- The norm of a Schwarz--Christoffel integrand is the product of the corresponding real powers
of the distances to its prevertices.  This identity is valid everywhere, including at a
prevertex; no upper-half-plane hypothesis is needed. -/
theorem norm_schwarzChristoffelIntegrand (a e : ι → ℝ) (z : ℂ) :
    ‖schwarzChristoffelIntegrand a e z‖ = ∏ i, dist z (a i : ℂ) ^ e i := by
  rw [schwarzChristoffelIntegrand_def, norm_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [Complex.norm_cpow_real, dist_eq]

/-- The logarithmic derivative of one principal-power factor in the upper half-plane is the
corresponding simple fraction. -/
lemma logDeriv_cpow_sub_of_im_pos {z : ℂ} (hz : 0 < z.im) (x r : ℝ) :
    logDeriv (fun w : ℂ => (w - (x : ℂ)) ^ (r : ℂ)) z = (r : ℂ) / (z - (x : ℂ)) := by
  have hslit := sub_ofReal_mem_slitPlane_of_im_pos hz x
  have hbase : z - (x : ℂ) ≠ 0 := slitPlane_ne_zero hslit
  have hpow : (z - (x : ℂ)) ^ (r : ℂ) ≠ 0 :=
    cpow_sub_ne_zero_of_im_pos hz x r
  rw [logDeriv_apply,
    ((hasDerivAt_id' z).sub_const (x : ℂ)).cpow_const hslit |>.deriv,
    mul_one, Complex.cpow_sub _ _ hbase, Complex.cpow_one]
  field_simp

/-- The logarithmic derivative of the Schwarz--Christoffel integrand is the sum of its simple
fractions.  Its possible poles are the real prevertices and hence lie on the boundary of the
domain of holomorphy. -/
theorem logDeriv_schwarzChristoffelIntegrand (a e : ι → ℝ) {z : ℂ}
    (hz : z ∈ upperHalfPlaneSet) :
    logDeriv (schwarzChristoffelIntegrand a e) z =
      ∑ i, (e i : ℂ) / (z - (a i : ℂ)) := by
  rw [show schwarzChristoffelIntegrand a e =
    (fun w => ∏ i, (w - (a i : ℂ)) ^ (e i : ℂ)) from
      funext (schwarzChristoffelIntegrand_def a e)]
  rw [logDeriv_fun_prod]
  · exact Finset.sum_congr rfl fun i _ => logDeriv_cpow_sub_of_im_pos hz (a i) (e i)
  · exact fun i _ => cpow_sub_ne_zero_of_im_pos hz (a i) (e i)
  · exact fun i _ => differentiableAt_cpow_sub_of_im_pos hz (a i) (e i)

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

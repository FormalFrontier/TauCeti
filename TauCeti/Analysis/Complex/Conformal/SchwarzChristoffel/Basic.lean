/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The Schwarz–Christoffel integrand and its straight-line boundary behaviour

The Schwarz–Christoffel formula produces a conformal map of the upper half-plane onto a polygon
by integrating

`S ζ = ∏ k, (ζ - a k) ^ β k`,

the product being over the prevertices `a k` on the real axis, with `β k = α k - 1` where `α k * π`
is the interior angle of the polygon at the image of `a k`. This file introduces that integrand
`TauCeti.schwarzChristoffelIntegrand` and proves the two facts that make the formula work: it is
holomorphic and zero-free off the real axis, and along each interval of the real axis that avoids
every prevertex it has *constant argument*. The latter is what forces a primitive of `S` to send
that interval into a straight line — the sides of the polygon.

The complex power is Mathlib's principal branch `Complex.cpow`. Off the real axis every factor
`ζ - a k` has nonzero imaginary part, hence lies in `Complex.slitPlane`, so the principal branch is
holomorphic there; this is why the integrand is holomorphic on both open half-planes at once. On
the real axis the principal branch is still available pointwise, and `Complex.ofReal_cpow_of_nonpos`
evaluates it: a factor to the left of `t` contributes a positive real number, while a factor to the
right of `t` contributes a positive real number times `exp (π * I * β k)`. Collecting the second
kind gives the polar decomposition

`S t = schwarzChristoffelModulus s a β t * schwarzChristoffelSideDirection s a β t`,

whose second factor is a unit complex number depending only on which prevertices lie to the right
of `t`. That set is constant on any interval free of prevertices, so the direction is constant
there, and the fundamental theorem of calculus turns this into the statement that a primitive `F`
of `S` along such an interval satisfies `F q - F p = r * (side direction)` with `r > 0` for
`p < q`: the image of a side is a straight segment traversed in one direction, and `F` is injective
on it.

## Main definitions

* `TauCeti.schwarzChristoffelIntegrand`: the Schwarz–Christoffel integrand `∏ k, (ζ - a k) ^ β k`,
  for a `Finset` of prevertices `a k` on the real axis with exponents `β k`.
* `TauCeti.schwarzChristoffelModulus`: its modulus `∏ k, |t - a k| ^ β k` along the real axis.
* `TauCeti.schwarzChristoffelSideDirection`: the unit complex number
  `exp (π * I * ∑ k with t < a k, β k)` giving its argument along the real axis.

## Main results

* `TauCeti.differentiableOn_schwarzChristoffelIntegrand` and
  `TauCeti.analyticOnNhd_schwarzChristoffelIntegrand`: the integrand is holomorphic off the real
  axis, in particular on the upper half-plane.
* `TauCeti.schwarzChristoffelIntegrand_ne_zero`: it is zero-free away from the prevertices.
* `TauCeti.schwarzChristoffelIntegrand_ofReal`: the polar decomposition along the real axis.
* `TauCeti.schwarzChristoffelSideDirection_eq_of_mem_Ioo`: the direction is constant on an interval
  containing no prevertex.
* `TauCeti.sub_eq_integral_mul_schwarzChristoffelSideDirection`: a primitive of the integrand along
  such an interval has increments that are real multiples of the side direction, the multiple being
  positive to the right (`TauCeti.integral_schwarzChristoffelModulus_pos`).
* `TauCeti.image_subset_line_of_hasDerivAt_schwarzChristoffelIntegrand` and
  `TauCeti.injOn_of_hasDerivAt_schwarzChristoffelIntegrand`: consequently such a primitive maps the
  interval injectively into a straight line.

## Roadmap

This is groundwork for layer **L6 — Schwarz–Christoffel** of the conformal-mapping roadmap
(`TauCetiRoadmap/ConformalMapping/README.md`): "explicit conformal maps onto polygons". Only the
analytic half of that layer is developed here — the integrand, its holomorphy, and the
straight-line boundary behaviour — none of which needs the boundary theory of layers L4–L5. That
the resulting map is *onto* a polygon needs the L5 boundary correspondence and is left to a later
file. Layer L6 is absent from the upstream Mathlib Riemann-mapping effort
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), so this is new
formalization rather than a temporary shim.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6.2.
* P. Henrici, *Applied and Computational Complex Analysis*, Vol. 1, Ch. 5.12.
* T. A. Driscoll and L. N. Trefethen, *Schwarz–Christoffel Mapping*, Ch. 2.
-/

public section

namespace TauCeti

open Complex MeasureTheory Set
open scoped Real

variable {ι : Type*} {s : Finset ι} {a β : ι → ℝ}

/-- The **Schwarz–Christoffel integrand** `ζ ↦ ∏ k ∈ s, (ζ - a k) ^ β k`, with prevertices `a k`
on the real axis and real exponents `β k`, using the principal branch of the complex power. In the
classical formula `β k = α k - 1`, where `α k * π` is the interior angle of the target polygon at
the image of the prevertex `a k`. -/
noncomputable def schwarzChristoffelIntegrand (s : Finset ι) (a β : ι → ℝ) (ζ : ℂ) : ℂ :=
  ∏ k ∈ s, (ζ - (a k : ℂ)) ^ ((β k : ℝ) : ℂ)

/-- The modulus of the Schwarz–Christoffel integrand along the real axis. -/
noncomputable def schwarzChristoffelModulus (s : Finset ι) (a β : ι → ℝ) (t : ℝ) : ℝ :=
  ∏ k ∈ s, |t - a k| ^ β k

/-- The direction of the Schwarz–Christoffel integrand along the real axis: the unit complex
number carrying its argument. Only the prevertices lying strictly to the right of `t` contribute,
so this is constant on every interval containing no prevertex — the direction of one side of the
target polygon. -/
noncomputable def schwarzChristoffelSideDirection (s : Finset ι) (a β : ι → ℝ) (t : ℝ) : ℂ :=
  Complex.exp ((π : ℂ) * I * ((∑ k ∈ s.filter fun k => t < a k, β k : ℝ) : ℂ))

theorem schwarzChristoffelIntegrand_eq (s : Finset ι) (a β : ι → ℝ) (ζ : ℂ) :
    schwarzChristoffelIntegrand s a β ζ = ∏ k ∈ s, (ζ - (a k : ℂ)) ^ ((β k : ℝ) : ℂ) := by
  rw [schwarzChristoffelIntegrand]

theorem schwarzChristoffelModulus_eq (s : Finset ι) (a β : ι → ℝ) (t : ℝ) :
    schwarzChristoffelModulus s a β t = ∏ k ∈ s, |t - a k| ^ β k := by
  rw [schwarzChristoffelModulus]

theorem schwarzChristoffelSideDirection_eq (s : Finset ι) (a β : ι → ℝ) (t : ℝ) :
    schwarzChristoffelSideDirection s a β t =
      Complex.exp ((π : ℂ) * I * ((∑ k ∈ s.filter fun k => t < a k, β k : ℝ) : ℂ)) := by
  rw [schwarzChristoffelSideDirection]

section Holomorphy

/-- The Schwarz–Christoffel integrand vanishes nowhere off the prevertices: each factor is a
principal power of a nonzero base. -/
theorem schwarzChristoffelIntegrand_ne_zero {ζ : ℂ} (h : ∀ k ∈ s, (a k : ℂ) ≠ ζ) :
    schwarzChristoffelIntegrand s a β ζ ≠ 0 := by
  rw [schwarzChristoffelIntegrand_eq]
  exact Finset.prod_ne_zero_iff.mpr fun k hk =>
    Complex.cpow_ne_zero_iff.mpr (Or.inl (sub_ne_zero.mpr (h k hk).symm))

/-- Off the real axis the Schwarz–Christoffel integrand is nonzero: no prevertex is there. -/
theorem schwarzChristoffelIntegrand_ne_zero_of_im_ne_zero {ζ : ℂ} (hζ : ζ.im ≠ 0) :
    schwarzChristoffelIntegrand s a β ζ ≠ 0 :=
  schwarzChristoffelIntegrand_ne_zero fun k _ h => hζ (by rw [← h]; simp)

/-- Off the real axis each factor `ζ - a k` of the Schwarz–Christoffel integrand lies in the slit
plane, where the principal power is holomorphic. -/
theorem differentiableAt_schwarzChristoffelIntegrand {ζ : ℂ} (hζ : ζ.im ≠ 0) :
    DifferentiableAt ℂ (schwarzChristoffelIntegrand s a β) ζ := by
  have hfun : schwarzChristoffelIntegrand s a β
      = fun z : ℂ => ∏ k ∈ s, (z - (a k : ℂ)) ^ ((β k : ℝ) : ℂ) :=
    funext (schwarzChristoffelIntegrand_eq s a β)
  rw [hfun]
  refine DifferentiableAt.fun_finsetProd
    (f := fun k (z : ℂ) => (z - (a k : ℂ)) ^ ((β k : ℝ) : ℂ)) fun k _ => ?_
  have hmem : ζ - (a k : ℂ) ∈ slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inr (by simpa using hζ))
  exact (((hasDerivAt_id ζ).sub_const (a k : ℂ)).cpow_const hmem).differentiableAt

/-- The Schwarz–Christoffel integrand is holomorphic off the real axis, hence on the upper
half-plane and on the lower half-plane. -/
theorem differentiableOn_schwarzChristoffelIntegrand :
    DifferentiableOn ℂ (schwarzChristoffelIntegrand s a β) {z : ℂ | z.im ≠ 0} :=
  fun _ hz => (differentiableAt_schwarzChristoffelIntegrand hz).differentiableWithinAt

/-- The Schwarz–Christoffel integrand is analytic off the real axis. -/
theorem analyticOnNhd_schwarzChristoffelIntegrand :
    AnalyticOnNhd ℂ (schwarzChristoffelIntegrand s a β) {z : ℂ | z.im ≠ 0} :=
  differentiableOn_schwarzChristoffelIntegrand.analyticOnNhd
    (isOpen_ne.preimage Complex.continuous_im)

end Holomorphy

section RealAxis

/-- A single Schwarz–Christoffel factor evaluated at a real point `t` distinct from its prevertex
`x`: it is a positive real number, times `exp (π * I * c)` when the prevertex lies to the right
of `t`. -/
private lemma cpow_ofReal_sub_ofReal {t x : ℝ} (c : ℝ) (h : x ≠ t) :
    ((t : ℂ) - (x : ℂ)) ^ ((c : ℝ) : ℂ)
      = ((|t - x| ^ c : ℝ) : ℂ) * Complex.exp ((π : ℂ) * I * (if t < x then (c : ℂ) else 0)) := by
  rw [← Complex.ofReal_sub]
  rcases lt_or_gt_of_ne h with hlt | hgt
  · -- The prevertex is to the left: the base is a positive real.
    have h0 : (0 : ℝ) < t - x := sub_pos.mpr hlt
    rw [if_neg (not_lt.mpr hlt.le), abs_of_pos h0, Complex.ofReal_cpow h0.le]
    simp
  · -- The prevertex is to the right: the base is a negative real, and the principal branch picks
    -- up the factor `exp (π * I * c)`.
    have h0 : t - x < 0 := sub_neg.mpr hgt
    rw [if_pos hgt, Complex.ofReal_cpow_of_nonpos h0.le, abs_of_neg h0, ← Complex.ofReal_neg,
      Complex.ofReal_cpow (by linarith : (0 : ℝ) ≤ -(t - x))]

/-- **Polar decomposition of the Schwarz–Christoffel integrand along the real axis.** At a real
point `t` distinct from every prevertex the integrand is its (positive) modulus times a unit
complex number determined by the prevertices to the right of `t`. -/
theorem schwarzChristoffelIntegrand_ofReal {t : ℝ} (h : ∀ k ∈ s, a k ≠ t) :
    schwarzChristoffelIntegrand s a β (t : ℂ)
      = (schwarzChristoffelModulus s a β t : ℂ) * schwarzChristoffelSideDirection s a β t := by
  rw [schwarzChristoffelIntegrand_eq, schwarzChristoffelModulus_eq,
    schwarzChristoffelSideDirection_eq, Complex.ofReal_prod,
    Finset.prod_congr rfl fun k hk => cpow_ofReal_sub_ofReal (β k) (h k hk),
    Finset.prod_mul_distrib, ← Complex.exp_sum]
  congr 1
  have hsum : ((∑ k ∈ s.filter fun k => t < a k, β k : ℝ) : ℂ)
      = ∑ k ∈ s, (if t < a k then (β k : ℂ) else 0) := by
    rw [Finset.sum_filter, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun k _ => by split_ifs <;> simp
  rw [hsum, Finset.mul_sum]

/-- The side direction is a unit complex number. -/
@[simp]
theorem norm_schwarzChristoffelSideDirection (t : ℝ) :
    ‖schwarzChristoffelSideDirection s a β t‖ = 1 := by
  rw [schwarzChristoffelSideDirection_eq, Complex.norm_exp]
  simp

/-- The modulus of the Schwarz–Christoffel integrand is positive away from the prevertices. -/
theorem schwarzChristoffelModulus_pos {t : ℝ} (h : ∀ k ∈ s, a k ≠ t) :
    0 < schwarzChristoffelModulus s a β t := by
  rw [schwarzChristoffelModulus_eq]
  exact Finset.prod_pos fun k hk =>
    Real.rpow_pos_of_pos (abs_pos.mpr (sub_ne_zero.mpr (h k hk).symm)) _

/-- The name `schwarzChristoffelModulus` is justified: it is the modulus of the integrand. -/
theorem norm_schwarzChristoffelIntegrand_ofReal {t : ℝ} (h : ∀ k ∈ s, a k ≠ t) :
    ‖schwarzChristoffelIntegrand s a β (t : ℂ)‖ = schwarzChristoffelModulus s a β t := by
  rw [schwarzChristoffelIntegrand_ofReal h, norm_mul, norm_schwarzChristoffelSideDirection,
    mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (schwarzChristoffelModulus_pos h)]

end RealAxis

section Side

variable {u v : ℝ}

/-- On an interval containing no prevertex, no point of the interval is a prevertex. -/
private lemma ne_of_mem_Ioo (hnv : ∀ k ∈ s, a k ∉ Ioo u v) {t : ℝ} (ht : t ∈ Ioo u v) :
    ∀ k ∈ s, a k ≠ t := fun k hk h => hnv k hk (h ▸ ht)

/-- The prevertices lying to the right of a point do not change as the point moves inside an
interval containing no prevertex. -/
private lemma filter_lt_eq_of_mem_Ioo (hnv : ∀ k ∈ s, a k ∉ Ioo u v) {t t' : ℝ}
    (ht : t ∈ Ioo u v) (ht' : t' ∈ Ioo u v) :
    (s.filter fun k => t < a k) = s.filter fun k => t' < a k := by
  have key : ∀ p q : ℝ, p ∈ Ioo u v → q ∈ Ioo u v → ∀ k ∈ s, p < a k → q < a k := by
    intro p q hp hq k hk hpk
    by_contra hcon
    exact hnv k hk ⟨hp.1.trans hpk, (not_lt.mp hcon).trans_lt hq.2⟩
  ext k
  simp only [Finset.mem_filter, and_congr_right_iff]
  exact fun hk => ⟨fun h => key t t' ht ht' k hk h, fun h => key t' t ht' ht k hk h⟩

/-- **The side direction is constant along a prevertex-free interval.** This is the reason the
Schwarz–Christoffel formula produces straight sides. -/
theorem schwarzChristoffelSideDirection_eq_of_mem_Ioo (hnv : ∀ k ∈ s, a k ∉ Ioo u v) {t t' : ℝ}
    (ht : t ∈ Ioo u v) (ht' : t' ∈ Ioo u v) :
    schwarzChristoffelSideDirection s a β t = schwarzChristoffelSideDirection s a β t' := by
  rw [schwarzChristoffelSideDirection_eq, schwarzChristoffelSideDirection_eq,
    filter_lt_eq_of_mem_Ioo hnv ht ht']

/-- The modulus is continuous on a prevertex-free interval. -/
theorem continuousOn_schwarzChristoffelModulus (hnv : ∀ k ∈ s, a k ∉ Ioo u v) :
    ContinuousOn (schwarzChristoffelModulus s a β) (Ioo u v) := by
  have hfun : schwarzChristoffelModulus s a β = fun t : ℝ => ∏ k ∈ s, |t - a k| ^ β k :=
    funext (schwarzChristoffelModulus_eq s a β)
  rw [hfun]
  refine continuousOn_finsetProd s fun k hk t ht => ?_
  have hne : |t - a k| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr (ne_of_mem_Ioo hnv ht k hk).symm)
  have hinner : ContinuousAt (fun t : ℝ => |t - a k|) t :=
    (continuous_abs.comp (continuous_id.sub continuous_const)).continuousAt
  exact (hinner.rpow_const (Or.inl hne)).continuousWithinAt

/-- The integrand is continuous along a prevertex-free interval of the real axis: it is the
continuous modulus times a constant direction. -/
theorem continuousOn_schwarzChristoffelIntegrand_ofReal (hnv : ∀ k ∈ s, a k ∉ Ioo u v) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo u v) :
    ContinuousOn (fun t : ℝ => schwarzChristoffelIntegrand s a β (t : ℂ)) (Ioo u v) := by
  refine ContinuousOn.congr (f := fun t : ℝ =>
    (schwarzChristoffelModulus s a β t : ℂ) * schwarzChristoffelSideDirection s a β t₀)
    ((Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_schwarzChristoffelModulus hnv)).mul continuousOn_const) fun t ht => ?_
  rw [schwarzChristoffelIntegrand_ofReal (ne_of_mem_Ioo hnv ht),
    schwarzChristoffelSideDirection_eq_of_mem_Ioo hnv ht ht₀]

/-- **The increment of a Schwarz–Christoffel primitive along a side.** If `F` has the
Schwarz–Christoffel integrand as its derivative along an interval containing no prevertex, then
each of its increments is a *real* multiple of the (constant) side direction. Together with
`TauCeti.integral_schwarzChristoffelModulus_pos` this says the side is traversed monotonically
along a fixed line. -/
theorem sub_eq_integral_mul_schwarzChristoffelSideDirection {F : ℝ → ℂ}
    (hnv : ∀ k ∈ s, a k ∉ Ioo u v)
    (hF : ∀ t ∈ Ioo u v, HasDerivAt F (schwarzChristoffelIntegrand s a β (t : ℂ)) t)
    {p q : ℝ} (hp : p ∈ Ioo u v) (hq : q ∈ Ioo u v) :
    F q - F p = ((∫ t in p..q, schwarzChristoffelModulus s a β t : ℝ) : ℂ) *
      schwarzChristoffelSideDirection s a β p := by
  have hsub : uIcc p q ⊆ Ioo u v := (ordConnected_Ioo).uIcc_subset hp hq
  have hcont : ContinuousOn (fun t : ℝ => schwarzChristoffelIntegrand s a β (t : ℂ)) (uIcc p q) :=
    (continuousOn_schwarzChristoffelIntegrand_ofReal hnv hp).mono hsub
  have hFTC : (∫ t in p..q, schwarzChristoffelIntegrand s a β (t : ℂ)) = F q - F p :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hF t (hsub ht))
      (hcont.intervalIntegrable)
  rw [← hFTC, ← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_mul_const]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [schwarzChristoffelIntegrand_ofReal (ne_of_mem_Ioo hnv (hsub ht)),
    schwarzChristoffelSideDirection_eq_of_mem_Ioo hnv (hsub ht) hp]

/-- The integral of the modulus over a subinterval of a prevertex-free interval is positive: the
side is traversed at nonzero speed. -/
theorem integral_schwarzChristoffelModulus_pos (hnv : ∀ k ∈ s, a k ∉ Ioo u v)
    {p q : ℝ} (hp : p ∈ Ioo u v) (hq : q ∈ Ioo u v) (hpq : p < q) :
    0 < ∫ t in p..q, schwarzChristoffelModulus s a β t := by
  have hsub : uIcc p q ⊆ Ioo u v := (ordConnected_Ioo).uIcc_subset hp hq
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    (((continuousOn_schwarzChristoffelModulus hnv).mono hsub).intervalIntegrable)
    (fun t ht => schwarzChristoffelModulus_pos (ne_of_mem_Ioo hnv (hsub (by
      rw [Set.uIcc_of_le hpq.le]; exact Ioo_subset_Icc_self ht)))) hpq

/-- **A Schwarz–Christoffel primitive maps a prevertex-free interval into a straight line**, the
line through `F t₀` with direction the constant side direction. This is the analytic source of the
straight sides of the target polygon. -/
theorem image_subset_line_of_hasDerivAt_schwarzChristoffelIntegrand {F : ℝ → ℂ}
    (hnv : ∀ k ∈ s, a k ∉ Ioo u v)
    (hF : ∀ t ∈ Ioo u v, HasDerivAt F (schwarzChristoffelIntegrand s a β (t : ℂ)) t)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo u v) :
    F '' Ioo u v ⊆
      {w | ∃ r : ℝ, w = F t₀ + (r : ℂ) * schwarzChristoffelSideDirection s a β t₀} := by
  rintro _ ⟨t, ht, rfl⟩
  refine ⟨∫ x in t₀..t, schwarzChristoffelModulus s a β x, ?_⟩
  rw [← sub_eq_integral_mul_schwarzChristoffelSideDirection hnv hF ht₀ ht]
  ring

/-- **A Schwarz–Christoffel primitive is injective on a prevertex-free interval.** The increments
are positive multiples of a single unit vector, so distinct parameters have distinct images. -/
theorem injOn_of_hasDerivAt_schwarzChristoffelIntegrand {F : ℝ → ℂ}
    (hnv : ∀ k ∈ s, a k ∉ Ioo u v)
    (hF : ∀ t ∈ Ioo u v, HasDerivAt F (schwarzChristoffelIntegrand s a β (t : ℂ)) t) :
    InjOn F (Ioo u v) := by
  have key : ∀ p ∈ Ioo u v, ∀ q ∈ Ioo u v, p < q → F q ≠ F p := by
    intro p hp q hq hpq hcon
    have hzero : ((∫ t in p..q, schwarzChristoffelModulus s a β t : ℝ) : ℂ) *
        schwarzChristoffelSideDirection s a β p = 0 := by
      rw [← sub_eq_integral_mul_schwarzChristoffelSideDirection hnv hF hp hq, hcon, sub_self]
    rcases mul_eq_zero.mp hzero with h | h
    · exact absurd (Complex.ofReal_eq_zero.mp h)
        (integral_schwarzChristoffelModulus_pos hnv hp hq hpq).ne'
    · exact absurd (norm_schwarzChristoffelSideDirection (s := s) (a := a) (β := β) p)
        (by rw [h]; simp)
  intro p hp q hq hpq
  rcases lt_trichotomy p q with h | h | h
  · exact absurd hpq.symm (key p hp q hq h)
  · exact h
  · exact absurd hpq (key q hq p hp h)

end Side

end TauCeti

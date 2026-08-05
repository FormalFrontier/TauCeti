/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Argument.Cycle
public import Mathlib.Analysis.Calculus.LogDeriv
import TauCeti.Analysis.Contour.LogDerivFTC

/-!
# The argument principle in winding-number form

The argument principle is normally *stated* as an equality of contour integrals — the integral of
`f'/f` along a cycle equals `2πi` times the winding-weighted count of zeros minus poles — and that
is the form the sibling contour-integration development supplies
(`TauCeti.Contour.argumentPrinciple_nullHomologous`). The name, though, comes from a *geometric*
reading of the same identity: `∮_γ f'/f` measures the total change of `arg (f z)` as `z` traverses
`γ`, so what the identity computes is **how often the image curve `f ∘ γ` winds around the
origin**. This file supplies that reading, and it is what turns the argument principle into a
statement about the geometry of the image rather than about an integral.

The bridge is `TauCeti.windingNumber_comp_eq_integral_logDeriv`: along a piecewise-`C¹` curve `γ`
on which `f` is analytic and zero-free, the composite `f ∘ γ` is itself a curve missing the origin,
and its index integral `(2πi)⁻¹ ∮_{f ∘ γ} dw / w` is, after the substitution `w = f z`, exactly
`(2πi)⁻¹ ∮_γ f'/f`. Formally the substitution is the chain rule `(f ∘ γ)' = γ' · f'(γ)`, valid off
the finitely many breakpoints of `γ` and so almost everywhere — which is all an integral sees. No
regularity of `f ∘ γ` beyond continuity and this almost-everywhere derivative is needed, so nothing
has to be said about `f ∘ γ` being piecewise `C¹` (it is, but the winding number does not ask).

Feeding the bridge into the homological argument principle gives the geometric statements. For `f`
meromorphic on an open `U` with its zeros and poles confined to a finite `S`, and `γ` closed and
null-homologous in `U`,

`n_0(f ∘ γ) = ∑_{z ∈ S} n_z(γ) · ord_z f`,

the winding number of the image about the origin being the winding-weighted number of zeros minus
poles. The holomorphic case is recorded separately, with the orders read off by
`analyticOrderNatAt` instead of supplied by the caller.

Nothing here re-proves the argument principle. Layer **L0** of the conformal-mapping roadmap is
directed to *consume* the residue and argument-principle material of the sibling
contour-integration roadmap, and that is what happens: the analytic content is
`TauCeti.Contour.argumentPrinciple_nullHomologous` and the corner-tolerant logarithmic-derivative
regularity of `TauCeti.Analysis.Contour.LogDerivFTC`, and what is added on top is the
conformal-geometric reading. `TauCeti/Analysis/Complex/Conformal/Rouche.lean` consumes it in turn
to state Rouché's theorem as an equality of image winding numbers — the "dog on a leash" form.

The generalized winding number of `TauCeti.Contour.windingNumber` is a *complex* number, defined by
a principal value, so no integrality is asserted anywhere below; the identity is an identity of
complex numbers, exactly as the underlying argument principle is.

## Main results

* `TauCeti.windingNumber_comp_eq_integral_logDeriv` — the bridge: the winding number of the image
  curve `f ∘ γ` about the origin is `(2πi)⁻¹ ∮_γ f'/f`.
* `TauCeti.argumentPrinciple_windingNumber` — **the argument principle, geometric form**: for `f`
  meromorphic with orders `ord` on a finite `S` and `γ` null-homologous, the image curve winds
  `∑_{z ∈ S} n_z(γ) · ord z` times about the origin.
* `TauCeti.argumentPrinciple_windingNumber_of_analyticOnNhd` — the holomorphic case, with the orders
  read off by `analyticOrderNatAt`.

## Coordination with upstream Mathlib

Per the *Coordination with upstream Mathlib* section of `ConformalMapping/README.md`, layer L0
overlaps [mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), the
in-progress human-curated Riemann-mapping-theorem effort, which proves an argument principle
internally as a private lemma
(`circleIntegral_logDeriv_eq_finsum_analyticOrderNatAdd`). **This file is therefore a temporary
shim**: once the corresponding Mathlib lemmas land, these statements should be backed by them — or
deleted and their consumers refactored — rather than maintained as an independent re-proof. What
Tau Ceti adds at L0 is named, discoverable API, not first proof.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 4 §5.
* S. Lang, *Complex Analysis* (GTM 103), Ch. VI §1.
-/

public section

open Complex MeasureTheory

open scoped Interval

namespace TauCeti

variable {f : ℂ → ℂ} {U : Set ℂ} {S : Finset ℂ} {γ : ℝ → ℂ} {a b : ℝ}

/-- **The winding number of the image curve is the logarithmic-derivative integral.** If `f` is
analytic and zero-free along a piecewise-`C¹` curve `γ`, the composite `f ∘ γ` avoids the origin
and

`n_0(f ∘ γ) = (2πi)⁻¹ ∫_a^b γ' t · (f'/f) (γ t)`.

This is the substitution `w = f z` in the index integral `(2πi)⁻¹ ∮_{f ∘ γ} dw / w`, carried out by
the chain rule. The chain rule is available only off the breakpoints of `γ`, a finite set, so the
two integrands agree merely almost everywhere — enough for both the integrals and the
interval-integrability to transfer.

The analyticity hypothesis is local: `AnalyticAt ℂ f (γ t)` asks only for *some* neighbourhood of
each point of the curve on which `f` is analytic, never for one ambient open set carrying the whole
curve, and imposes no condition beyond those neighbourhoods. So the lemma applies verbatim to a
function with zeros and poles inside the region the curve encloses; that is what the argument
principle then counts. -/
theorem windingNumber_comp_eq_integral_logDeriv (hγ : Contour.IsPiecewiseC1On γ a b)
    (hfa : ∀ t ∈ [[a, b]], AnalyticAt ℂ f (γ t)) (hfne : ∀ t ∈ [[a, b]], f (γ t) ≠ 0) :
    Contour.windingNumber (f ∘ γ) a b 0
      = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * ∫ t in a..b, deriv γ t • logDeriv f (γ t) := by
  obtain ⟨p, hp⟩ := hγ.exists_finset_differentiableAt
  have hcont : ContinuousOn (f ∘ γ) [[a, b]] := fun t ht =>
    (hfa t ht).continuousAt.comp_continuousWithinAt (hγ.continuousOn t ht)
  -- Off the finitely many breakpoints of `γ` — and off the right endpoint, which `Ι a b` contains
  -- but `Set.Ioo (min a b) (max a b)` does not — the chain rule identifies the two integrands.
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ι a b →
      deriv γ t • logDeriv f (γ t) = ((f ∘ γ) t - 0)⁻¹ * deriv (f ∘ γ) t := by
    have hnull : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ insert (max a b) (↑p : Set ℝ) :=
      measure_eq_zero_iff_ae_notMem.mp ((p.finite_toSet.insert (max a b)).measure_zero volume)
    filter_upwards [hnull] with t hts ht
    have ht' : t ∈ Set.Ioc (min a b) (max a b) := ht
    have htIoo : t ∈ Set.Ioo (min a b) (max a b) \ (↑p : Set ℝ) :=
      ⟨⟨ht'.1, lt_of_le_of_ne ht'.2 fun h => hts (by simp [h])⟩,
        fun h => hts (Set.mem_insert_of_mem _ h)⟩
    have htu : t ∈ [[a, b]] := by
      rw [← Set.Icc_min_max]
      exact Set.Ioo_subset_Icc_self htIoo.1
    have hcomp : logDeriv (f ∘ γ) t = logDeriv f (γ t) * deriv γ t :=
      logDeriv_comp (hfa t htu).differentiableAt (hp t htIoo)
    rw [sub_zero, ← div_eq_inv_mul, ← logDeriv_apply, hcomp, smul_eq_mul, mul_comm]
  have hint : IntervalIntegrable (fun t => deriv γ t • logDeriv f (γ t)) volume a b :=
    Contour.intervalIntegrable_deriv_smul_logDeriv hγ hfa hfne
  rw [Contour.windingNumber_eq_integral_of_avoidance hcont
      (fun t ht => hfne t ht) (hint.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr hae))]
  exact congrArg _ (intervalIntegral.integral_congr_ae hae).symm

/-- **The argument principle, geometric form.** Let `U` be open, `S` a finite set collecting every
zero and pole of `f` in `U`: `f` is analytic and non-vanishing at each point of `U ∖ S`, and
meromorphic of order `ord s` at each `s ∈ S` lying in `U`. Let `γ` be a closed piecewise-`C¹` curve
in `U`, **null-homologous** in `U`, that **avoids** `S`. Then the image curve `f ∘ γ` misses the
origin and winds around it exactly

`n_0(f ∘ γ) = ∑_{z ∈ S} n_z(γ) · ord z`

times: the number of zeros minus poles enclosed by `γ`, each counted with its multiplicity and with
the winding number of `γ` about it.

This is the reading that names the theorem — the total change of `arg (f z)` along `γ`, divided by
`2π` — and it is `TauCeti.Contour.argumentPrinciple_nullHomologous` read through
`TauCeti.windingNumber_comp_eq_integral_logDeriv`. As there, points of `S` outside `U` are
harmless: null-homology makes their winding number, hence their contribution, vanish. -/
theorem argumentPrinciple_windingNumber {ord : ℂ → ℤ} (hU : IsOpen U)
    (hoff : ∀ z ∈ U, z ∉ S → AnalyticAt ℂ f z ∧ f z ≠ 0)
    (hmero : ∀ s ∈ S, s ∈ U → MeromorphicAt f s)
    (hord : ∀ s ∈ S, s ∈ U → meromorphicOrderAt f s = (ord s : WithTop ℤ))
    (hγ : Contour.IsPiecewiseC1On γ a b) (hγU : ∀ t ∈ [[a, b]], γ t ∈ U) (hclosed : γ a = γ b)
    (hγoff : ∀ t ∈ [[a, b]], γ t ∉ (↑S : Set ℂ)) (hnull : Contour.IsNullHomologous γ a b U) :
    Contour.windingNumber (f ∘ γ) a b 0
      = ∑ z ∈ S, Contour.windingNumber γ a b z * (ord z : ℂ) := by
  rw [windingNumber_comp_eq_integral_logDeriv hγ
      (fun t ht => (hoff _ (hγU t ht) (hγoff t ht)).1)
      (fun t ht => (hoff _ (hγU t ht) (hγoff t ht)).2),
    Contour.argumentPrinciple_nullHomologous hU hoff hmero hord hγ hγU hclosed hγoff hnull,
    inv_mul_cancel_left₀ two_pi_I_ne_zero]

/-- **The argument principle, geometric form, for a holomorphic function.** Let `f` be analytic on
an open `U` with all its zeros in a finite set `S`, and let `γ` be a closed piecewise-`C¹` curve in
`U`, null-homologous in `U`, along which `f` does not vanish. Then

`n_0(f ∘ γ) = ∑_{z ∈ S} n_z(γ) · analyticOrderNatAt f z`:

the image curve winds around the origin as often as `γ` encloses zeros of `f`, counted with
multiplicity.

Only the *zeros* need be avoided, not all of `S`: `S` may list points where `f` does not vanish,
and `γ` is free to run through them, their order — and so their term in the sum — being `0`. This
is the pole-free specialisation of `TauCeti.argumentPrinciple_windingNumber`, with the orders read
off by `analyticOrderNatAt` instead of supplied by the caller. -/
theorem argumentPrinciple_windingNumber_of_analyticOnNhd (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U)
    (hzeros : ∀ z ∈ U, f z = 0 → z ∈ S)
    (hγ : Contour.IsPiecewiseC1On γ a b) (hγU : ∀ t ∈ [[a, b]], γ t ∈ U) (hclosed : γ a = γ b)
    (hγoff : ∀ t ∈ [[a, b]], f (γ t) ≠ 0) (hnull : Contour.IsNullHomologous γ a b U) :
    Contour.windingNumber (f ∘ γ) a b 0
      = ∑ z ∈ S, Contour.windingNumber γ a b z * (analyticOrderNatAt f z : ℂ) := by
  rw [windingNumber_comp_eq_integral_logDeriv hγ (fun t ht => hf _ (hγU t ht)) hγoff,
    Contour.argumentPrinciple_nullHomologous_of_analyticOnNhd hU hf hzeros hγ hγU hclosed hγoff
      hnull,
    inv_mul_cancel_left₀ two_pi_I_ne_zero]

end TauCeti

end

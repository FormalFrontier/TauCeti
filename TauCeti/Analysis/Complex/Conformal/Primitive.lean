/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import TauCeti.Analysis.Complex.Conformal.RiemannMapping.Existence

/-!
# Primitives on a simply connected domain, and Cauchy's theorem there

A holomorphic function on a simply connected open subset of `ℂ` has a primitive. Mathlib proves
this on a disc (`DifferentiableOn.isExactOn_ball`) and on the whole plane
(`Differentiable.isExactOn_univ`), and records the simply connected case as an open `TODO` in
`Mathlib/Analysis/Complex/HasPrimitives.lean`. This file discharges that case by transporting the
disc statement along a Riemann map, and then reads off the forms of Cauchy's theorem that primitive
existence gives for free: the integral of a holomorphic function along a *loop* in a simply
connected domain vanishes, and so does its integral along any circle whose *circle* — not its
closed disc — lies in the domain.

## Main results

* `TauCeti.DifferentiableOn.isExactOn_of_isSimplyConnected` — a holomorphic function on a simply
  connected open set has a primitive there, in Mathlib's `Complex.IsExactOn` vocabulary.
* `TauCeti.exists_differentiableOn_deriv_eqOn_of_isSimplyConnected` — the same primitive, packaged
  as a holomorphic `F` with `deriv F = f` on the domain.
* `TauCeti.isExactOn_iff_differentiableOn_of_isSimplyConnected` — on a simply connected open set,
  having a primitive and being holomorphic are the same condition.
* `TauCeti.cauchyTheorem_of_isSimplyConnected` — **Cauchy's theorem for a simply connected
  domain**: `∫ t in a..b, γ' t • f (γ t) = 0` for a differentiable loop `γ` in the domain.
* `TauCeti.circleIntegral_eq_zero_of_isSimplyConnected` — `∮ z in C(c, R), f z = 0` as soon as the
  circle `Metric.sphere c |R|` is contained in the domain.

## Proof

Write `Ω` for the domain. If `Ω = Set.univ` the statement is Mathlib's
`Differentiable.isExactOn_univ`. Otherwise `Ω` is a nonempty, simply connected, *proper* open
subset of `ℂ`, so the Riemann mapping theorem
(`TauCeti.exists_bijOn_ball_differentiableOn_invFunOn`) supplies a biholomorphism `φ : Ω → 𝔻` with
holomorphic inverse `ψ = Function.invFunOn φ Ω`. The pullback `w ↦ ψ' w • f (ψ w)` is holomorphic
on the disc, hence has a primitive `H` there by `DifferentiableOn.isExactOn_ball`, and `H ∘ φ` is a
primitive of `f` on `Ω`: the chain rule contributes the factor `φ' z * ψ' (φ z)`, which is `1`
because `ψ ∘ φ` is the identity near `z`.

This is the standard "uniformisation" proof, and it is why the result belongs to the conformal
layer rather than to the contour-integration layer below it: the only nonformal input is the
Riemann mapping theorem itself.

## Relation to the null-homotopic Cauchy theorem

`TauCeti.Contour.cauchyTheorem_of_pathHomotopy_refl` proves Cauchy's theorem for a loop in an
*arbitrary* open set that comes equipped with a `C²` path homotopy to a constant. Neither statement
subsumes the other: that one does not ask the ambient set to be simply connected, while
`cauchyTheorem_of_isSimplyConnected` asks for no homotopy witness and no regularity beyond
differentiability of the loop, which is what makes it usable for a loop handed over with no
homotopy in sight.

## Coordination with upstream Mathlib

The Riemann mapping theorem consumed here is Tau Ceti's L3 statement, an explicitly temporary shim
for the human-curated proof in progress at
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505); see
`TauCeti/Analysis/Complex/Conformal/RiemannMapping/Existence.lean`. When that lands, this file
should be refactored onto the Mathlib theorem — and its main result offered upstream, where it
answers the `TODO` in `Mathlib/Analysis/Complex/HasPrimitives.lean`.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 4 §4 and Ch. 6 §1.
* W. Rudin, *Real and Complex Analysis*, Thm. 13.11.
-/

public section

namespace TauCeti

open Complex MeasureTheory Metric Set
open scoped Interval Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable {f : ℂ → E} {Ω : Set ℂ}

/-- **A holomorphic function on a simply connected domain has a primitive.**

This is the simply connected case of Mathlib's `Complex.IsExactOn` theory, recorded there as a
`TODO`: `DifferentiableOn.isExactOn_ball` covers a disc and `Differentiable.isExactOn_univ` covers
the plane. The proof transports the disc case along a Riemann map, so the plane has to be split off
first — it is the one simply connected open set the Riemann mapping theorem excludes. -/
theorem DifferentiableOn.isExactOn_of_isSimplyConnected (hf : DifferentiableOn ℂ f Ω)
    (hΩo : IsOpen Ω) (hΩc : IsSimplyConnected Ω) :
    IsExactOn f Ω := by
  rcases eq_or_ne Ω univ with rfl | hΩ
  · exact Differentiable.isExactOn_univ (differentiableOn_univ.mp hf)
  obtain ⟨φ, hbij, hφd, hψd, hleft, -⟩ :=
    exists_bijOn_ball_differentiableOn_invFunOn hΩo hΩc hΩ
  set ψ := Function.invFunOn φ Ω
  -- The pullback `ψ' • (f ∘ ψ)` of `f` to the disc is holomorphic, so it has a primitive `H`.
  have hmapsTo : MapsTo ψ (ball (0 : ℂ) 1) Ω := hbij.surjOn.mapsTo_invFunOn
  have hcomp : DifferentiableOn ℂ (fun w => f (ψ w)) (ball (0 : ℂ) 1) := hf.comp hψd hmapsTo
  have hpull : DifferentiableOn ℂ (fun w => deriv ψ w • f (ψ w)) (ball (0 : ℂ) 1) :=
    (hψd.deriv isOpen_ball).smul hcomp
  obtain ⟨H, hH⟩ := hpull.isExactOn_ball
  refine ⟨H ∘ φ, fun z hz => ?_⟩
  have hzφ : φ z ∈ ball (0 : ℂ) 1 := hbij.mapsTo hz
  have hφz : HasDerivAt φ (deriv φ z) z :=
    ((hφd z hz).differentiableAt (hΩo.mem_nhds hz)).hasDerivAt
  have hψw : HasDerivAt ψ (deriv ψ (φ z)) (φ z) :=
    ((hψd _ hzφ).differentiableAt (isOpen_ball.mem_nhds hzφ)).hasDerivAt
  -- The two derivatives are reciprocal, because `ψ ∘ φ` is the identity near `z`.
  have hchain : deriv φ z * deriv ψ (φ z) = 1 := by
    have hid : (ψ ∘ φ) =ᶠ[𝓝 z] id := by
      filter_upwards [hΩo.mem_nhds hz] with w hw using hleft hw
    have hcompz := hψw.scomp z hφz
    rw [hid.hasDerivAt_iff] at hcompz
    simpa using hcompz.unique (hasDerivAt_id z)
  have hHφz : HasDerivAt H (deriv ψ (φ z) • f (ψ (φ z))) (φ z) := hH _ hzφ
  have hHz := hHφz.scomp z hφz
  rwa [hleft hz, smul_smul, hchain, one_smul] at hHz

/-- A holomorphic function on a simply connected open set is the derivative of a holomorphic
function there. This is `TauCeti.DifferentiableOn.isExactOn_of_isSimplyConnected` in the
`deriv`-and-`Set.EqOn` idiom, for consumers that prefer to rewrite with `deriv F`. -/
theorem exists_differentiableOn_deriv_eqOn_of_isSimplyConnected (hf : DifferentiableOn ℂ f Ω)
    (hΩo : IsOpen Ω) (hΩc : IsSimplyConnected Ω) :
    ∃ F : ℂ → E, DifferentiableOn ℂ F Ω ∧ EqOn (deriv F) f Ω := by
  obtain ⟨F, hF⟩ := TauCeti.DifferentiableOn.isExactOn_of_isSimplyConnected hf hΩo hΩc
  exact ⟨F, fun z hz => (hF z hz).differentiableAt.differentiableWithinAt,
    fun z hz => (hF z hz).deriv⟩

/-- On a simply connected open set, having a primitive is *equivalent* to being holomorphic.

The forward implication is Mathlib's `Complex.IsExactOn.differentiableOn`, which holds on any open
set; simple connectivity is exactly what makes the converse true. -/
theorem isExactOn_iff_differentiableOn_of_isSimplyConnected (hΩo : IsOpen Ω)
    (hΩc : IsSimplyConnected Ω) :
    IsExactOn f Ω ↔ DifferentiableOn ℂ f Ω :=
  ⟨fun h => h.differentiableOn hΩo,
    fun h => TauCeti.DifferentiableOn.isExactOn_of_isSimplyConnected h hΩo hΩc⟩

/-- **Cauchy's theorem for a simply connected domain.** The integral of a holomorphic function
along a loop contained in a simply connected open set vanishes.

The loop is described by its own derivative `γ'`, as in Mathlib's
`intervalIntegral.integral_eq_sub_of_hasDerivAt`; no regularity beyond differentiability of `γ`
and integrability of the integrand is required, and in particular no homotopy witness. Compare
`TauCeti.Contour.cauchyTheorem_of_pathHomotopy_refl`, which drops simple connectivity of the
ambient set but asks for a `C²` null-homotopy of the loop instead. -/
theorem cauchyTheorem_of_isSimplyConnected (hf : DifferentiableOn ℂ f Ω) (hΩo : IsOpen Ω)
    (hΩc : IsSimplyConnected Ω) {γ γ' : ℝ → ℂ} {a b : ℝ} (hγΩ : ∀ t ∈ uIcc a b, γ t ∈ Ω)
    (hγ : ∀ t ∈ uIcc a b, HasDerivAt γ (γ' t) t)
    (hint : IntervalIntegrable (fun t => γ' t • f (γ t)) volume a b) (hloop : γ a = γ b) :
    ∫ t in a..b, γ' t • f (γ t) = 0 := by
  obtain ⟨F, hF⟩ := TauCeti.DifferentiableOn.isExactOn_of_isSimplyConnected hf hΩo hΩc
  have hderiv : ∀ t ∈ uIcc a b, HasDerivAt (F ∘ γ) (γ' t • f (γ t)) t := fun t ht =>
    (hF _ (hγΩ t ht)).scomp t (hγ t ht)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint, Function.comp_apply,
    Function.comp_apply, hloop, sub_self]

/-- **Cauchy's theorem on a circle inside a simply connected domain.** If the circle
`Metric.sphere c |R|` lies in a simply connected open set on which `f` is holomorphic, then
`∮ z in C(c, R), f z = 0`.

Only the circle, not the closed disc it bounds, is asked to lie in the domain: that is what simple
connectivity buys over Mathlib's
`Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable`, which needs
`Metric.closedBall c R` inside the domain. -/
theorem circleIntegral_eq_zero_of_isSimplyConnected (hf : DifferentiableOn ℂ f Ω) (hΩo : IsOpen Ω)
    (hΩc : IsSimplyConnected Ω) {c : ℂ} {R : ℝ} (hR : sphere c |R| ⊆ Ω) :
    (∮ z in C(c, R), f z) = 0 := by
  obtain ⟨F, hF⟩ := TauCeti.DifferentiableOn.isExactOn_of_isSimplyConnected hf hΩo hΩc
  exact circleIntegral.integral_eq_zero_of_hasDerivWithinAt' fun z hz =>
    (hF z (hR hz)).hasDerivWithinAt

end TauCeti

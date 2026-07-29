module

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
public import TauCeti.Analysis.Complex.Conformal.ExtremalFamily
public import Mathlib.Analysis.Calculus.Deriv.Basic
import TauCeti.Analysis.Complex.BranchLogRoot
import TauCeti.Analysis.Complex.Conformal.ImageSimplyConnected
import TauCeti.Analysis.Complex.Conformal.Moebius
import TauCeti.Analysis.Complex.Conformal.PseudoHyperbolic
import TauCeti.Analysis.Complex.Conformal.Schwarz

/-!
# The Koebe square-root step

The Riemann mapping theorem is proved by maximizing `‖deriv f z₀‖` over the holomorphic injections
of a domain into the unit disc that fix a base point. Compactness (`ExtremalFamily.lean`) produces a
maximizer; this file supplies the other half: a maximizer cannot omit a value of the disc.

The engine is a statement about the disc alone: **a proper simply connected subdomain of the unit
disc containing the origin admits a holomorphic injection back into the disc that fixes the origin
and has derivative of norm exceeding `1` there** — no proper subdomain is extremal.

## The construction

Let `U` be such a subdomain and pick `a ∈ ball 0 1 \ U`; write `μ c` for the Möbius factor
`z ↦ (z - c) / (1 - conj c * z)` of `Conformal/Moebius.lean`. Since `μ a` does not vanish on `U`,
which is simply connected, it has a holomorphic square root `h` there
(`TauCeti.exists_differentiableOn_pow_eq`). Put `b := h 0`, so `b ^ 2 = μ a 0 = -a`, and set

* `f := μ b ∘ h`, the improved map;
* `G := μ (-a) ∘ (· ^ 2) ∘ μ (-b)`, an automorphism followed by squaring followed by an
  automorphism.

## Why the derivative grows

Not by computing `deriv f 0`. The four steps are:

1. `G ∘ f` is the identity on `U`, by pure algebra: the Möbius factors cancel in pairs and the
   square meets `h ^ 2 = μ a`. This also gives `InjOn f U` for free, `G` being a left inverse.
2. `G` is **not** injective on the disc: it squares after an automorphism, so `μ b u` and `μ b (-u)`
   collide for any nonzero `u` in the disc — the proof uses `u = 1/2`.
3. Hence `‖deriv G 0‖ < 1`, by the strict Schwarz lemma of `Conformal/Schwarz.lean`: Schwarz gives
   `≤ 1`, and equality would make `G` affine, hence injective.
4. Differentiating `G ∘ f = id` at `0` gives `deriv G 0 * deriv f 0 = 1`.

Together `‖deriv G 0‖ * ‖deriv f 0‖ = 1` with `‖deriv G 0‖ < 1` forces `1 < ‖deriv f 0‖`. This is
the route a lecturer takes, and it is also the cheaper one to formalize: the only chain rule used is
the one on an identity, and no `field_simp` over the Möbius denominators is needed.

## Main statements

* `TauCeti.exists_isPointedDiscInjectionOn_one_lt_norm_deriv` — a proper simply connected subdomain
  of the disc expands.
* `TauCeti.surjOn_ball_of_isMaxOn` — an extremal pointed disc injection is surjective onto the disc.

## Coordination with upstream Mathlib

The Riemann mapping theorem is being formalized upstream at
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), which proves the
L0–L3 prerequisites internally as private lemmas. The declarations here are an explicitly
**temporary shim**: delete them and refactor downstream consumers onto the exported Mathlib
versions once those land.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6 §1.2.
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. VII §4.
-/

public section

namespace TauCeti

open Complex Set Metric Topology

/-- The scalar unit-disc Möbius factor `z ↦ (z - c) / (1 - conj c * z)`, as a function of its
centre `c`. This is a private abbreviation for the expression that `Conformal/Moebius.lean` states
its lemmas about; it keeps the Koebe construction, which juggles four of these factors, readable. -/
private noncomputable def moebius (c z : ℂ) : ℂ := (z - c) / (1 - (starRingEnd ℂ) c * z)

private theorem moebius_apply_zero (c : ℂ) : moebius c 0 = -c := by
  simp [moebius]

private theorem moebius_self (c : ℂ) : moebius c c = 0 := by
  simp [moebius]

/-- **A proper simply connected subdomain of the disc containing the origin expands.** If `U` is an
open simply connected proper subset of the unit disc with `0 ∈ U`, then there is a holomorphic
injection of `U` into the disc fixing the origin whose derivative there has norm exceeding `1`.

This is the engine of the Riemann mapping theorem: no proper subdomain can be extremal. -/
theorem exists_isPointedDiscInjectionOn_one_lt_norm_deriv {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsSimplyConnected U) (hU₀ : (0 : ℂ) ∈ U) (hUd : U ⊆ ball 0 1) (hUne : U ≠ ball 0 1) :
    ∃ f : ℂ → ℂ, IsPointedDiscInjectionOn f U 0 ∧ 1 < ‖deriv f 0‖ := by
  classical
  -- A value of the disc omitted by `U`.
  obtain ⟨a, haU, haU'⟩ : ∃ a ∈ ball (0 : ℂ) 1, a ∉ U := by
    by_contra hcon
    push Not at hcon
    exact hUne (hUd.antisymm hcon)
  have ha1 : ‖a‖ < 1 := mem_ball_zero_iff.mp haU
  have ha0 : a ≠ 0 := fun h => haU' (h ▸ hU₀)
  -- The Möbius factor at `a` does not vanish on `U`, so it has a holomorphic square root there.
  have hnz : (0 : ℂ) ∉ moebius a '' U := by
    rintro ⟨z, hz, hz0⟩
    have hden : 1 - (starRingEnd ℂ) a * z ≠ 0 :=
      one_sub_conj_mul_ne_zero_of_norm_lt_one (mem_ball_zero_iff.mp (hUd hz)) ha1
    have : z - a = 0 := by
      have := hz0
      rw [moebius, div_eq_zero_iff] at this
      exact this.resolve_right hden
    exact haU' (sub_eq_zero.mp this ▸ hz)
  obtain ⟨h, hhd, hhsq⟩ := exists_differentiableOn_pow_eq hUc hUo
    ((differentiableOn_unitDiscMoebiusFormula_of_norm_lt_one ha1).mono hUd) hnz (n := 2) two_ne_zero
  set b : ℂ := h 0 with hb_def
  have hb2 : b ^ 2 = -a := by
    have := hhsq hU₀
    simpa [moebius_apply_zero] using this
  have hb1 : ‖b‖ < 1 := by
    rw [← pow_lt_one_iff_of_nonneg (norm_nonneg b) two_ne_zero, ← norm_pow, hb2, norm_neg]
    exact ha1
  have hb0 : b ≠ 0 := by
    intro h0
    rw [h0] at hb2
    exact ha0 (by simpa using hb2.symm)
  -- The square root lands in the disc, since its square does.
  have hhmem : ∀ z ∈ U, h z ∈ ball (0 : ℂ) 1 := by
    intro z hz
    rw [mem_ball_zero_iff, ← pow_lt_one_iff_of_nonneg (norm_nonneg (h z)) two_ne_zero, ← norm_pow]
    have hsq : h z ^ 2 = moebius a z := hhsq hz
    rw [hsq, ← mem_ball_zero_iff]
    exact mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one ha1 (hUd hz)
  have hna : ‖-a‖ < 1 := by rwa [norm_neg]
  have hnb : ‖-b‖ < 1 := by rwa [norm_neg]
  -- The improved map, and the automorphism-square-automorphism that inverts it.
  set f : ℂ → ℂ := fun z => moebius b (h z) with hf_def
  set G : ℂ → ℂ := fun w => moebius (-a) (moebius (-b) w ^ 2) with hG_def
  have hfd : DifferentiableOn ℂ f U :=
    (differentiableOn_unitDiscMoebiusFormula_of_norm_lt_one hb1).comp hhd hhmem
  have hfm : MapsTo f U (ball (0 : ℂ) 1) := fun z hz =>
    mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one hb1 (hhmem z hz)
  have hf0 : f 0 = 0 := by
    rw [hf_def]
    exact moebius_self b
  -- Step 1: `G` is a left inverse of `f` on `U`, by pure algebra.
  have hGf : LeftInvOn G f U := by
    intro z hz
    have h1 : moebius (-b) (f z) = h z :=
      leftInvOn_unitDiscMoebiusFormula_of_norm_lt_one hb1 (hhmem z hz)
    have h2 : h z ^ 2 = moebius a z := hhsq hz
    simp only [hG_def]
    rw [h1, h2]
    exact leftInvOn_unitDiscMoebiusFormula_of_norm_lt_one ha1 (hUd hz)
  have hfi : InjOn f U := hGf.injOn
  -- `G` is a holomorphic self-map of the disc fixing the origin.
  have hsqm : MapsTo (fun w : ℂ => w ^ 2) (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
    intro w hw
    rw [mem_ball_zero_iff] at hw ⊢
    rwa [norm_pow, pow_lt_one_iff_of_nonneg (norm_nonneg w) two_ne_zero]
  have hGd : DifferentiableOn ℂ G (ball (0 : ℂ) 1) :=
    (differentiableOn_unitDiscMoebiusFormula_of_norm_lt_one hna).comp
      ((differentiableOn_unitDiscMoebiusFormula_of_norm_lt_one hnb).pow 2)
      fun w hw => hsqm (mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one hnb hw)
  have hGm : MapsTo G (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := fun w hw =>
    mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one hna
      (hsqm (mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one hnb hw))
  have hG0 : G 0 = 0 := by
    simp only [hG_def]
    rw [moebius_apply_zero, neg_neg, hb2]
    exact moebius_self (-a)
  -- Step 2: `G` squares, so it is not injective on the disc.
  have hGni : ¬ InjOn G (ball (0 : ℂ) 1) := by
    intro hinj
    have hu : (1 / 2 : ℂ) ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff]
      norm_num
    have hu' : (-(1 / 2) : ℂ) ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff]
      norm_num
    have hcollide : G (moebius b (1 / 2)) = G (moebius b (-(1 / 2))) := by
      have e₁ : moebius (-b) (moebius b (1 / 2)) = 1 / 2 :=
        leftInvOn_unitDiscMoebiusFormula_of_norm_lt_one hb1 hu
      have e₂ : moebius (-b) (moebius b (-(1 / 2))) = -(1 / 2) :=
        leftInvOn_unitDiscMoebiusFormula_of_norm_lt_one hb1 hu'
      simp only [hG_def]
      rw [e₁, e₂]
      norm_num
    have := (leftInvOn_unitDiscMoebiusFormula_of_norm_lt_one hb1).injOn hu hu'
      (hinj (mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one hb1 hu)
        (mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one hb1 hu') hcollide)
    norm_num at this
  -- Step 3: the strict Schwarz lemma.
  have hGcb : MapsTo G (ball (0 : ℂ) 1) (closedBall (G 0) 1) := by
    rw [hG0]
    exact hGm.mono_right ball_subset_closedBall
  have hGderiv : ‖deriv G 0‖ < 1 := norm_deriv_lt_one_of_not_injOn one_pos hGd hGcb hGni
  -- Step 4: differentiate `G ∘ f = id` at the origin.
  have hderiv_mul : deriv G 0 * deriv f 0 = 1 := by
    have hf_at : HasDerivAt f (deriv f 0) 0 :=
      (hfd.differentiableAt (hUo.mem_nhds hU₀)).hasDerivAt
    have hG_at : HasDerivAt G (deriv G 0) (f 0) := by
      rw [hf0]
      exact (hGd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self one_pos))).hasDerivAt
    have hcomp : HasDerivAt (G ∘ f) (deriv G 0 * deriv f 0) 0 := hG_at.comp 0 hf_at
    have hev : (G ∘ f) =ᶠ[𝓝 0] id := by
      filter_upwards [hUo.mem_nhds hU₀] with z hz using hGf hz
    exact hcomp.unique ((hasDerivAt_id (0 : ℂ)).congr_of_eventuallyEq hev)
  refine ⟨f, ⟨hfd, hfm, hfi, hf0⟩, ?_⟩
  have hnorm : ‖deriv G 0‖ * ‖deriv f 0‖ = 1 := by
    rw [← norm_mul, hderiv_mul, norm_one]
  nlinarith [norm_nonneg (deriv f 0), norm_nonneg (deriv G 0)]

/-- **An extremal pointed disc injection is surjective onto the disc.** If `g` maximizes
`‖deriv · z₀‖` over the holomorphic injections of `Ω` into the disc fixing `z₀`, then `g` omits no
value of the disc.

Otherwise `U := g '' Ω` would be an open simply connected proper subdomain of the disc containing
`0`, and composing `g` with the map that
`TauCeti.exists_isPointedDiscInjectionOn_one_lt_norm_deriv` produces on `U` would beat `g`. -/
theorem surjOn_ball_of_isMaxOn {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩc : IsSimplyConnected Ω) {z₀ : ℂ}
    (hz₀ : z₀ ∈ Ω) {g : ℂ → ℂ} (hg : IsPointedDiscInjectionOn g Ω z₀)
    (hmax : ∀ f : ℂ → ℂ, IsPointedDiscInjectionOn f Ω z₀ → ‖deriv f z₀‖ ≤ ‖deriv g z₀‖) :
    SurjOn g Ω (ball 0 1) := by
  by_cases hUeq : g '' Ω = ball (0 : ℂ) 1
  · exact hUeq.ge
  exfalso
  have hUo : IsOpen (g '' Ω) := isOpen_image_of_injOn hΩo hg.differentiableOn hg.injOn
  have hUc : IsSimplyConnected (g '' Ω) :=
    isSimplyConnected_image_of_injOn hΩo hΩc hg.differentiableOn hg.injOn
  have hU₀ : (0 : ℂ) ∈ g '' Ω := ⟨z₀, hz₀, hg.map_base⟩
  obtain ⟨f, hf, hfd1⟩ := exists_isPointedDiscInjectionOn_one_lt_norm_deriv hUo hUc hU₀
    hg.mapsTo.image_subset hUeq
  -- `f ∘ g` competes on `Ω`, and its derivative at the base point is strictly larger.
  have hmt : MapsTo g Ω (g '' Ω) := fun z hz => mem_image_of_mem g hz
  have hcomp : IsPointedDiscInjectionOn (f ∘ g) Ω z₀ :=
    ⟨hf.differentiableOn.comp hg.differentiableOn hmt, hf.mapsTo.comp hmt,
      hf.injOn.comp hg.injOn hmt, by simp [hg.map_base, hf.map_base]⟩
  have hderiv : deriv (f ∘ g) z₀ = deriv f 0 * deriv g z₀ := by
    have hg_at : HasDerivAt g (deriv g z₀) z₀ :=
      (hg.differentiableOn.differentiableAt (hΩo.mem_nhds hz₀)).hasDerivAt
    have hf_at : HasDerivAt f (deriv f 0) (g z₀) := by
      rw [hg.map_base]
      exact (hf.differentiableOn.differentiableAt (hUo.mem_nhds hU₀)).hasDerivAt
    exact (hf_at.comp z₀ hg_at).deriv
  have hpos : 0 < ‖deriv g z₀‖ := norm_pos_iff.mpr (hg.deriv_ne_zero hΩo hz₀)
  have := hmax _ hcomp
  rw [hderiv, norm_mul] at this
  nlinarith

end TauCeti

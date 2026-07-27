module

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
public import Mathlib.Analysis.Complex.BranchLogRoot
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Holomorphic branches of `log` and of `n`-th roots on a simply connected domain

Mathlib's `Complex.exists_continuousOn_eqOn_exp_comp` and
`Complex.exists_continuousOn_pow_eq` produce **continuous** branches of `log ∘ g` and of `ⁿ√g` on a
simply connected open set. The Riemann-mapping argument needs **holomorphic** ones. This file
supplies exactly that upgrade, and nothing else: the branch itself is Mathlib's, consumed rather
than rebuilt.

The upgrade is local and purely formal. Near a point `z₀`, the continuous branch `L` agrees with
`v ↦ w₀ + log (v / exp w₀) ∘ g` where `w₀ = L z₀`: that composite is holomorphic (the argument
sits near `1`, inside the slit plane, where `Complex.log` is), and it agrees with `L` because
continuity of `L` confines `L z - w₀` to the strip `|im| < π` on which `log ∘ exp` is the identity.
So no new analysis is involved — only the observation that a continuous logarithm of a holomorphic
nonvanishing function is automatically holomorphic.

## Upstream coordination

The Riemann mapping theorem is being formalized upstream at
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), which proves
holomorphic log / `n`-th-root statements (`exists_branch_log`, `exists_branch_nthRoot`)
**internally, as private lemmas**, alongside the argument principle, Hurwitz and Montel. The
`ConformalMapping` roadmap's stated contribution at these layers is therefore *named, reusable API*
rather than first proof. Accordingly the declarations here are a **temporary shim**: when the
human-curated Mathlib versions land, these should be deleted and every downstream consumer
refactored onto them.

## Main statements

* `TauCeti.exists_differentiableOn_eqOn_exp_comp` — a holomorphic branch of `log ∘ g`.
* `TauCeti.exists_differentiableOn_pow_eq` — a holomorphic branch of `ⁿ√g`.
-/

public section

namespace TauCeti

open Complex Set

/-- **The local upgrade.** A continuous branch `L` of `log ∘ g` on an open set is complex
differentiable wherever `g` is, because near any point it coincides with an honest local branch of
`log` composed with `g`. -/
private theorem differentiableAt_of_continuousOn_exp_comp {U : Set ℂ} (hU : IsOpen U)
    {L g : ℂ → ℂ} (hL : ContinuousOn L U) (hEq : EqOn (Complex.exp ∘ L) g U)
    (hg : DifferentiableOn ℂ g U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    DifferentiableAt ℂ L z₀ := by
  set w₀ : ℂ := L z₀ with hw₀
  -- The local branch of `log` centred at `w₀`, and the composite it defines.
  set ℓ : ℂ → ℂ := fun v => w₀ + Complex.log (v / Complex.exp w₀) with hℓ
  have hgz₀ : g z₀ = Complex.exp w₀ := (hEq hz₀).symm
  -- `L` is continuous at `z₀` in the ambient sense, `U` being open.
  have hLat : ContinuousAt L z₀ := (hL.continuousAt (hU.mem_nhds hz₀))
  -- Continuity confines `L z - w₀` to the strip where `log ∘ exp` is the identity.
  have hstrip : ∀ᶠ z in nhds z₀, |(L z - w₀).im| < Real.pi := by
    have hcont : ContinuousAt (fun z => |(L z - w₀).im|) z₀ := by
      exact (continuous_abs.comp Complex.continuous_im).continuousAt.comp
        (hLat.sub continuousAt_const)
    have hz : |(L z₀ - w₀).im| < Real.pi := by
      simp [hw₀, Real.pi_pos]
    exact hcont (Iio_mem_nhds hz)
  -- On that neighbourhood (intersected with `U`), `L` and `ℓ ∘ g` agree.
  have hloc : L =ᶠ[nhds z₀] ℓ ∘ g := by
    filter_upwards [hstrip, hU.mem_nhds hz₀] with z hz hzU
    have hgz : g z = Complex.exp (L z) := (hEq hzU).symm
    have hdiv : g z / Complex.exp w₀ = Complex.exp (L z - w₀) := by
      rw [hgz, ← Complex.exp_sub]
    have hlog : Complex.log (Complex.exp (L z - w₀)) = L z - w₀ :=
      Complex.log_exp (by linarith [abs_lt.mp hz |>.1]) (le_of_lt (abs_lt.mp hz).2)
    simp only [hℓ, Function.comp_apply, hdiv, hlog]
    ring
  -- `ℓ ∘ g` is differentiable at `z₀`: the argument of `log` is `1` there.
  have hone : g z₀ / Complex.exp w₀ = 1 := by
    rw [hgz₀, div_self (Complex.exp_ne_zero _)]
  have hdiffℓ : DifferentiableAt ℂ (ℓ ∘ g) z₀ := by
    have hgd : DifferentiableAt ℂ g z₀ := (hg z₀ hz₀).differentiableAt (hU.mem_nhds hz₀)
    have hquot : DifferentiableAt ℂ (fun z => g z / Complex.exp w₀) z₀ :=
      hgd.div_const _
    have hslit : (fun z => g z / Complex.exp w₀) z₀ ∈ Complex.slitPlane := by
      simpa only [hone] using Complex.one_mem_slitPlane
    exact (hquot.clog hslit).const_add _
  exact hdiffℓ.congr_of_eventuallyEq hloc

/-- **A holomorphic branch of `log ∘ g` on a simply connected domain.** If `g` is holomorphic and
nowhere zero on a simply connected open `U ⊆ ℂ`, there is a holomorphic `f` on `U` with
`exp ∘ f = g`. Mathlib's `Complex.exists_continuousOn_eqOn_exp_comp` supplies the branch; only its
holomorphy is added here. -/
theorem exists_differentiableOn_eqOn_exp_comp {U : Set ℂ} (hUc : IsSimplyConnected U)
    (hUo : IsOpen U) {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g U) (hU₀ : 0 ∉ g '' U) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧ EqOn (Complex.exp ∘ f) g U := by
  obtain ⟨L, hLc, hLeq⟩ :=
    Complex.exists_continuousOn_eqOn_exp_comp hUc hUo hg.continuousOn hU₀
  refine ⟨L, fun z hz => ?_, hLeq⟩
  exact ((differentiableAt_of_continuousOn_exp_comp hUo hLc hLeq hg hz).differentiableWithinAt)

/-- **A holomorphic `n`-th root on a simply connected domain.** The Koebe square-root step of the
Riemann mapping theorem is the case `n = 2`. -/
theorem exists_differentiableOn_pow_eq {U : Set ℂ} (hUc : IsSimplyConnected U) (hUo : IsOpen U)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g U) (hU₀ : 0 ∉ g '' U) {n : ℕ} (hn : n ≠ 0) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧ EqOn (fun z => f z ^ n) g U := by
  obtain ⟨L, hLd, hLeq⟩ := exists_differentiableOn_eqOn_exp_comp hUc hUo hg hU₀
  refine ⟨fun z => Complex.exp (L z / n), fun z hz => ((hLd z hz).div_const _).cexp,
    fun z hz => ?_⟩
  have hne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hmul : (n : ℂ) * (L z / n) = L z := by field_simp
  have hpow : Complex.exp (L z / n) ^ n = Complex.exp (L z) := by
    rw [← Complex.exp_nat_mul, hmul]
  simpa only [hpow, Function.comp_apply] using hLeq hz

end TauCeti

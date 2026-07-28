module

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
public import TauCeti.Analysis.Complex.BranchLogRoot
import TauCeti.Analysis.Complex.Conformal.Moebius
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Convex.Contractible

/-!
# A simply connected proper domain injects holomorphically into the unit disc

The first step of the Riemann mapping theorem: the competing family is nonempty. Every nonempty,
simply connected, open, *proper* subset of `ℂ` admits an injective holomorphic map into the open
unit disc.

This is the classical square-root construction. Pick `a ∉ U`. On the simply connected `U` the
nonvanishing function `z - a` has a holomorphic square root `h`
(`TauCeti.exists_differentiableOn_pow_eq` at `n = 2`, constructed as `exp (L / 2)` from the upgraded
holomorphic logarithm branch `L`, not from Mathlib's continuous root branch). Then:

* `h` is injective, since `h z₁ = h z₂` forces `z₁ - a = z₂ - a` after squaring;
* `h '' U` is open (open mapping theorem: `h` is injective, hence nonconstant, on the connected
  `U`), so it contains a ball `ball w₀ r`;
* `-h z` **avoids** that ball for every `z ∈ U`: otherwise `-h z = h z'`, and squaring gives
  `z' = z`, hence `h z = -h z` and so `h z = 0`, which is impossible;
* therefore `r ≤ ‖h z + w₀‖` throughout `U`.

Inverting, `z ↦ (r/2) / (h z + w₀)` is holomorphic, injective, and bounded by `1/2`. Halving `r`
is what makes the bound **strict**, landing in the open disc rather than its closure.

## Attribution and upstream coordination

Two pieces of prior Mathlib work stand behind this file, both © Yury Kudryashov.

*The construction.* This follows the in-tree Mathlib proof of the same step,
`Complex.exists_mapsTo_unitBall_injOn_deriv_ne_zero` (`Mathlib.Analysis.Complex.RiemannMapping`):
the same plan — pick `a ∉ U`, take a holomorphic square root of `z - a`, obtain an open image ball,
observe that `-h` avoids it, and invert. That lemma is present in this checkout but is **not
exported from its module** (it carries no `public` marker under the module system, so an importer
cannot name it — a direct reference elaborates to `Unknown constant`, while a public lemma from the
same file resolves), which is why this file re-derives the construction rather than reusing it.

*The square root it rests on.* The branch used here comes from
`TauCeti.exists_differentiableOn_pow_eq`, which is the holomorphic upgrade of Mathlib's continuous
branch API in `Mathlib.Analysis.Complex.BranchLogRoot` (`Complex.exists_continuousOn_eqOn_exp_comp`,
`Complex.exists_continuousOn_pow_eq`). The existence half of this step is therefore Mathlib's; the
sibling file `BranchLogRoot.lean` records that debt in detail.

The Riemann mapping theorem is also being formalized upstream at
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), which proves the
L0–L3 prerequisites internally as private lemmas. This declaration is an explicitly **temporary
shim**: delete it and refactor downstream consumers onto the exported Mathlib version once it lands.

## Main statements

* `TauCeti.exists_differentiableOn_injOn_mapsTo_unitBall` — the nonempty-family step.
* `TauCeti.exists_differentiableOn_injOn_mapsTo_unitBall_apply_eq_zero` — the same step for the
  **normalized** family, whose members fix a chosen base point. This is the form the roadmap's
  maximization argument consumes.
-/

public section

namespace TauCeti

open Complex Set Metric

/-- **A simply connected proper domain injects into the unit disc.** The Riemann mapping theorem's
competing family — injective holomorphic maps `U → 𝔻` — is nonempty. -/
theorem exists_differentiableOn_injOn_mapsTo_unitBall {U : Set ℂ} (hUc : IsSimplyConnected U)
    (hUo : IsOpen U) (hUne : U ≠ univ) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧ InjOn f U ∧ MapsTo f U (ball (0 : ℂ) 1) := by
  obtain ⟨a, ha⟩ : ∃ a, a ∉ U := by
    by_contra hcon
    exact hUne (eq_univ_of_forall (by simpa using hcon))
  -- `z - a` is nonvanishing on `U`, so it has a holomorphic square root there.
  have hsub : DifferentiableOn ℂ (fun z : ℂ => z - a) U :=
    (differentiable_id.sub_const a).differentiableOn
  have hzero : (0 : ℂ) ∉ (fun z : ℂ => z - a) '' U := by
    rintro ⟨z, hz, hza⟩
    have hza' : z - a = 0 := hza
    exact ha (sub_eq_zero.mp hza' ▸ hz)
  obtain ⟨h, hhd, hheq⟩ :=
    exists_differentiableOn_pow_eq hUc hUo hsub hzero (n := 2) two_ne_zero
  have hsq : ∀ z ∈ U, h z ^ 2 = z - a := fun z hz => hheq hz
  -- `h` never vanishes on `U`, since its square is `z - a ≠ 0`.
  have hne : ∀ z ∈ U, h z ≠ 0 := by
    intro z hz hz0
    have hza : z - a = 0 := by rw [← hsq z hz, hz0]; ring
    exact ha (by rwa [sub_eq_zero.mp hza] at hz)
  -- Squaring makes `h` injective.
  have hinj : InjOn h U := by
    intro z₁ hz₁ z₂ hz₂ hEq
    have hdiff : z₁ - a = z₂ - a := by rw [← hsq z₁ hz₁, ← hsq z₂ hz₂, hEq]
    linear_combination hdiff
  -- `h '' U` is open: `h` is injective, hence nonconstant, on the connected `U`.
  have hconn : IsPreconnected U := hUc.isPathConnected.isConnected.isPreconnected
  have hanal : AnalyticOnNhd ℂ h U := hhd.analyticOnNhd hUo
  obtain ⟨z₀, hz₀⟩ := hUc.nonempty
  have hopen : IsOpen (h '' U) := by
    rcases hanal.is_constant_or_isOpen hconn with hconst | hopenmap
    · exfalso
      obtain ⟨w, hw⟩ := hconst
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUo z₀ hz₀
      have hhalf : (0 : ℝ) < ε / 2 := by linarith
      have hz₁ : z₀ + ((ε / 2 : ℝ) : ℂ) ∈ U := by
        refine hball ?_
        have hnorm : ‖z₀ + ((ε / 2 : ℝ) : ℂ) - z₀‖ = ε / 2 := by
          have hcancel : z₀ + ((ε / 2 : ℝ) : ℂ) - z₀ = ((ε / 2 : ℝ) : ℂ) := by ring
          rw [hcancel, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hhalf]
        rw [mem_ball, dist_eq_norm, hnorm]
        linarith
      have heq : z₀ + ((ε / 2 : ℝ) : ℂ) = z₀ :=
        hinj hz₁ hz₀ (by rw [hw _ hz₁, hw _ hz₀])
      have : ((ε / 2 : ℝ) : ℂ) = 0 := by linear_combination heq
      exact absurd (by exact_mod_cast this) (ne_of_gt hhalf)
    · exact hopenmap U (subset_refl U) hUo
  -- The image contains a ball around `h z₀`, and `-h` avoids it.
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen (h z₀) ⟨z₀, hz₀, rfl⟩
  set w₀ : ℂ := h z₀ with hw₀
  have havoid : ∀ z ∈ U, r ≤ ‖h z + w₀‖ := by
    intro z hz
    by_contra hcon
    have hlt : ‖h z + w₀‖ < r := lt_of_not_ge hcon
    have hmem : -h z ∈ ball w₀ r := by
      rw [mem_ball, dist_eq_norm]
      have hrw : -h z - w₀ = -(h z + w₀) := by ring
      rw [hrw, norm_neg]
      exact hlt
    obtain ⟨z', hz', hz'eq⟩ := hball hmem
    -- Squaring `h z' = -h z` gives `z' = z`, forcing `h z = 0`.
    have hsq' : z' - a = z - a := by
      rw [← hsq z' hz', ← hsq z hz, hz'eq]
      ring
    have hzz : z' = z := by linear_combination hsq'
    rw [hzz] at hz'eq
    exact hne z hz (by linear_combination hz'eq / 2)
  -- Every denominator is nonzero, `r` being positive.
  have hden : ∀ z ∈ U, h z + w₀ ≠ 0 := by
    intro z hz hzero'
    have := havoid z hz
    rw [hzero', norm_zero] at this
    linarith
  have hrhalf : (0 : ℝ) < r / 2 := by linarith
  have hrne : ((r / 2 : ℝ) : ℂ) ≠ 0 := by
    simpa using ne_of_gt hrhalf
  -- Invert. Halving `r` makes the bound strict.
  refine ⟨fun z => ((r / 2 : ℝ) : ℂ) / (h z + w₀), ?_, ?_, ?_⟩
  · exact fun z hz => (differentiableWithinAt_const _).div
      ((hhd z hz).add_const _) (hden z hz)
  · intro z₁ hz₁ z₂ hz₂ hEq
    rw [div_eq_div_iff (hden z₁ hz₁) (hden z₂ hz₂)] at hEq
    have hcancel : h z₂ + w₀ = h z₁ + w₀ := mul_left_cancel₀ hrne hEq
    exact hinj hz₁ hz₂ (by linear_combination -hcancel)
  · intro z hz
    have hlow := havoid z hz
    have hpos : (0 : ℝ) < ‖h z + w₀‖ := lt_of_lt_of_le hr hlow
    rw [mem_ball, dist_zero_right, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hrhalf, div_lt_one hpos]
    linarith

/-- **The normalized competing family is nonempty.** The roadmap's maximization step ranges over
injective holomorphic maps `U → 𝔻` that *fix a chosen base point* `z₀`, so the nonemptiness it needs
is this one, not the bare version above.

The normalization is the textbook one: post-compose with the disc automorphism centred at
`c = f z₀`, `w ↦ (w - c) / (1 - conj c * w)`. That is the L2 disc-automorphism API of this roadmap,
already available here as `TauCeti.unitDiscMoebius` and its scalar formula, so this step consumes
it rather than substituting a weaker correction:

* holomorphy — `TauCeti.differentiableOn_unitDiscMoebiusFormula_of_norm_lt_one`;
* self-map of `𝔻` — `TauCeti.mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one`;
* injectivity on `𝔻` — the factor centred at `-c` is a left inverse
  (`TauCeti.leftInvOn_unitDiscMoebiusFormula_of_norm_lt_one`).

Each is stated for a scalar centre of norm `< 1`, which is exactly what `f z₀ ∈ 𝔻` supplies, so no
passage through the bundled `Complex.UnitDisc` is needed. The Moebius factor is onto `𝔻`, which the
uniqueness half of the Riemann mapping theorem will need; the *nonempty normalized family*
obligation proved here uses only the three properties above. -/
theorem exists_differentiableOn_injOn_mapsTo_unitBall_apply_eq_zero {U : Set ℂ}
    (hUc : IsSimplyConnected U) (hUo : IsOpen U) (hUne : U ≠ univ) {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧ InjOn f U ∧ MapsTo f U (ball (0 : ℂ) 1) ∧ f z₀ = 0 := by
  obtain ⟨f, hfd, hfi, hfm⟩ := exists_differentiableOn_injOn_mapsTo_unitBall hUc hUo hUne
  -- The centre of the normalizing automorphism is the base point's image, which lies in `𝔻`.
  have hc : ‖f z₀‖ < 1 := by simpa [mem_ball, dist_zero_right] using hfm hz₀
  set m : ℂ → ℂ := fun w => (w - f z₀) / (1 - (starRingEnd ℂ) (f z₀) * w) with hm
  have hmd : DifferentiableOn ℂ m (ball (0 : ℂ) 1) :=
    differentiableOn_unitDiscMoebiusFormula_of_norm_lt_one hc
  have hmm : MapsTo m (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) :=
    mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one hc
  have hmi : InjOn m (ball (0 : ℂ) 1) :=
    (leftInvOn_unitDiscMoebiusFormula_of_norm_lt_one hc).injOn
  refine ⟨m ∘ f, hmd.comp hfd hfm, hmi.comp hfi hfm, hmm.comp hfm, ?_⟩
  simp [hm]

/- **Non-vacuity** (documentation, not public API). The hypotheses above are satisfiable: the open
unit ball is simply connected (being convex, hence contractible), open, and proper. Without this the
theorem could be true merely because nothing meets its hypotheses.  Kept as an `example` — it is a
one-off sanity check on `ball 0 1`, with no downstream consumer, so it should not sit in the public
namespace. -/
example :
    IsSimplyConnected (ball (0 : ℂ) 1) ∧ IsOpen (ball (0 : ℂ) 1)
      ∧ (ball (0 : ℂ) 1) ≠ univ := by
  refine ⟨?_, isOpen_ball, ?_⟩
  · haveI : ContractibleSpace (ball (0 : ℂ) 1) :=
      Convex.contractibleSpace (convex_ball (0 : ℂ) 1) (nonempty_ball.2 one_pos)
    exact SimplyConnectedSpace.ofContractible _
  · intro hcon
    have h2 : (2 : ℂ) ∈ ball (0 : ℂ) 1 := hcon ▸ mem_univ _
    rw [mem_ball, dist_zero_right] at h2
    norm_num at h2

end TauCeti

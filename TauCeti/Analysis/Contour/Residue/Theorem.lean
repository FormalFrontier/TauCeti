/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import TauCeti.Analysis.Contour.Residue.Basic
import TauCeti.Analysis.Contour.Cauchy.Goursat
import Mathlib.Analysis.Meromorphic.NormalForm

/-!
# The classical residue theorem on a circle

For `f` meromorphic on a closed disc `C(c, R)` (`R > 0`) whose poles are contained in a finite set
`S` inside the open disc, the contour integral of `f` around the boundary circle is `2πi` times the
sum of the residues over `S`:
`∮_{C(c,R)} f = 2πi · ∑_{s ∈ S} residue f s`.

The hypothesis on `S` asks only that every pole — every point of *negative* meromorphic order — lie
in `S`. `S` may list further points (zeros, or removable/regular points), whose residues are `0` and
so do not affect the sum. No pointwise regularity of the raw function `f` is required — `f` may take
isolated "wrong values" where it disagrees with its meromorphic normal form — since both sides are
stated up to that normal form.

## Main results

* `TauCeti.Contour.classicalResidueTheorem_circle_of_meromorphicOrderAt_neg` — the sharp support
  form: only the poles (points of negative meromorphic order) need lie in `S`.
* `TauCeti.Contour.classicalResidueTheorem_circle` — the roadmap form, asking every point of nonzero
  meromorphic order to lie in `S`; a direct corollary since residues at non-poles vanish.

This is a Layer 2 target of the contour-integration roadmap: the special case of the
Hungerbühler–Wasem generalized residue theorem (HW Thm 3.3) for a round circle, feeding the valence
formula.

## Provenance

Adapted from the AINTLIB `LeanModularForms` project (the residue theorem of
`ForMathlib/GeneralizedResidueTheory/Residue/GeneralizedTheoremBase.lean`), specialised to a circle
and to the raw-function design of the contour-integration roadmap.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997.
-/

public section

open Filter Topology Metric Complex
open scoped Real

namespace TauCeti.Contour

/-- Subtracting the leading Laurent term strictly raises the meromorphic order: for `g` analytic at
`s`, the order of `(· − s) ^ n • g − g s • (· − s) ^ n` at `s` exceeds `n`. -/
private theorem meromorphicOrderAt_sub_leadingTerm_gt {g : ℂ → ℂ} {s : ℂ} {n : ℤ}
    (hg : AnalyticAt ℂ g s) :
    (n : WithTop ℤ) < meromorphicOrderAt (fun z => (z - s) ^ n • g z - g s • (z - s) ^ n) s := by
  have hcongr : (fun z => (z - s) ^ n • g z - g s • (z - s) ^ n)
      = ((· - s) ^ n) • (fun z => g z - g s) := by
    funext z; simp only [Pi.smul_apply', Pi.pow_apply, smul_eq_mul]; ring
  rw [hcongr]
  have hmero_pow : MeromorphicAt ((· - s) ^ n) s := by fun_prop
  have hmero_gsub : MeromorphicAt (fun z => g z - g s) s := (hg.sub analyticAt_const).meromorphicAt
  rw [meromorphicOrderAt_smul hmero_pow hmero_gsub, meromorphicOrderAt_zpow_id_sub_const]
  have hpos : 0 < meromorphicOrderAt (fun z => g z - g s) s := by
    rw [← tendsto_zero_iff_meromorphicOrderAt_pos hmero_gsub]
    have h : Tendsto (fun z => g z - g s) (𝓝 s) (𝓝 (g s - g s)) :=
      (hg.continuousAt.sub continuousAt_const).tendsto
    rw [sub_self] at h; exact h.mono_left nhdsWithin_le_nhds
  calc (n : WithTop ℤ) = (n : WithTop ℤ) + 0 := (add_zero _).symm
    _ < _ := WithTop.add_lt_add_left WithTop.coe_ne_top hpos

/-- The circle integral of a leading monomial equals `2πi` times its residue. For `s₀` in the open
disc and `n < 0`, `∮_{C(c,R)} a·(· − s₀) ^ n = 2πi · residue (a·(· − s₀) ^ n) s₀` (the integral is
`2πi·a` for a simple pole `n = −1` and `0` otherwise). -/
private lemma circleIntegral_const_mul_zpow_sub {c s₀ : ℂ} {R : ℝ} {n : ℤ} (a : ℂ)
    (hs₀ : s₀ ∈ ball c R) (hn : n < 0) : (∮ z in C(c, R), a * (z - s₀) ^ n)
      = 2 * ↑Real.pi * Complex.I * residue (fun z => a * (z - s₀) ^ n) s₀ := by
  -- Residue of the pure monomial: the Taylor coefficient of the constant `1` at index `−1 − n`.
  have hresQ : residue (fun z => (z - s₀) ^ n) s₀
      = (if (-1 - n).toNat = 0 then (1 : ℂ) else 0) / ((-1 - n).toNat.factorial : ℂ) := by
    have h1 : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) s₀ := analyticAt_const
    rw [residue_eq_of_eventuallyEq_zpow_smul (by omega : n ≤ -1) h1
      (Filter.Eventually.of_forall fun z => by simp [smul_eq_mul]), iteratedDeriv_const]
  rw [residue_const_mul a, hresQ]
  rcases eq_or_ne n (-1) with hn1 | hn1
  · subst hn1
    have hinv : (fun z => a * (z - s₀) ^ (-1 : ℤ)) = fun z => a * (z - s₀)⁻¹ := by
      funext z; rw [zpow_neg_one]
    rw [hinv, circleIntegral.integral_const_mul, circleIntegral.integral_sub_inv_of_mem_ball hs₀]
    norm_num
    ring
  · rw [circleIntegral.integral_const_mul, circleIntegral.integral_sub_zpow_of_ne hn1,
      if_neg (by omega)]
    ring

/-- The peeled leading term `a·(· − s₀) ^ n` (`n < 0`, pole at `s₀ ∈ S ⊆ ball c R`) has its
residue sum over `S` concentrated at `s₀`: `∮ = 2πi · ∑_{s ∈ S} residue s`. -/
private lemma circleIntegral_leadingTerm_eq_residueSum {c : ℂ} {R : ℝ} (a : ℂ) {s₀ : ℂ}
    (hs₀ : s₀ ∈ ball c R) {n : ℤ} (hn : n < 0) (S : Finset ℂ) (hs₀S : s₀ ∈ S) :
    circleIntegral (fun z => a * (z - s₀) ^ n) c R
      = 2 * (Real.pi : ℂ) * Complex.I * ∑ s ∈ S, residue (fun z => a * (z - s₀) ^ n) s := by
  have hP_an : ∀ s, s ≠ s₀ → AnalyticAt ℂ (fun z => a * (z - s₀) ^ n) s := fun s hne =>
    analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).fun_zpow (sub_ne_zero.2 hne))
  rw [Finset.sum_eq_single_of_mem s₀ hs₀S fun s _ hne =>
    residue_eq_zero_of_analyticAt (hP_an s hne)]
  exact circleIntegral_const_mul_zpow_sub a hs₀ hn

/-- Pole depth `(-order.untop₀).toNat` does not increase when the order stays at or above a minimum
taken with a nonnegative order: if `min oF oP ≤ oG` and `0 ≤ oP`, the depth of `oG` is at most that
of `oF`. (`oG` is the order of `F − P` where `P` is analytic — `oP ≥ 0` — at the point.) -/
private lemma depthTerm_le_of_sub {oF oP oG : WithTop ℤ} (hP : 0 ≤ oP) (hG : min oF oP ≤ oG) :
    (-oG.untop₀).toNat ≤ (-oF.untop₀).toNat := by
  rcases eq_or_ne oG ⊤ with hGtop | hGtop
  · simp [hGtop]
  · lift oG to ℤ using hGtop with g
    rcases eq_or_ne oF ⊤ with hFtop | hFtop
    · rw [hFtop, min_eq_right le_top] at hG
      have hg : (0 : ℤ) ≤ g := by exact_mod_cast hP.trans hG
      simp only [hFtop, WithTop.untop₀_top, WithTop.untop₀_coe, neg_zero, Int.toNat_zero]
      omega
    · lift oF to ℤ using hFtop with f
      simp only [WithTop.untop₀_coe]
      rcases eq_or_ne oP ⊤ with hPtop | hPtop
      · rw [hPtop, min_eq_left le_top] at hG
        have hfg : f ≤ g := by exact_mod_cast hG
        omega
      · lift oP to ℤ using hPtop with p
        have hp : (0 : ℤ) ≤ p := by exact_mod_cast hP
        have hfpg : min f p ≤ g := by exact_mod_cast hG
        omega

/-- Pole depth strictly decreases when the order strictly rises above a negative integer order:
if `n < 0` and `n < oG`, the depth of `oG` is strictly less than the depth `(-n).toNat` of `n`. -/
private lemma depthTerm_lt_of_lt {n : ℤ} {oG : WithTop ℤ} (hn : n < 0)
    (hlt : (n : WithTop ℤ) < oG) : (-oG.untop₀).toNat < (-n).toNat := by
  rcases eq_or_ne oG ⊤ with hGtop | hGtop
  · simp only [hGtop, WithTop.untop₀_top, neg_zero, Int.toNat_zero]; omega
  · lift oG to ℤ using hGtop with g
    simp only [WithTop.untop₀_coe]
    have hng : n < g := by exact_mod_cast hlt
    omega

/-- A function analytic on the boundary circle `sphere c R` is circle-integrable. -/
private lemma circleIntegrable_of_analyticOn_sphere {A : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hA : ∀ z ∈ sphere c R, AnalyticAt ℂ A z) : CircleIntegrable A c R :=
  ContinuousOn.circleIntegrable hR fun z hz => (hA z hz).continuousAt.continuousWithinAt

/-- **Peeling lowers the total pole depth.** A term `P` analytic away from `s₀` cannot deepen the
pole at any other point of `S`, so a strict drop at `s₀` is a strict drop in the sum over `S`. -/
private lemma sum_depthTerm_sub_lt {c : ℂ} {R : ℝ} (S : Finset ℂ)
    {F P : ℂ → ℂ} (hF_mero : MeromorphicOn F (closedBall c R))
    (hmem_cb : ∀ s ∈ S, s ∈ closedBall c R)
    {s₀ : ℂ} (hs₀S : s₀ ∈ S) (hP_an_off : ∀ z, z ≠ s₀ → AnalyticAt ℂ P z)
    {n₀ : ℤ} (hn₀_neg : n₀ < 0) (hFs₀ : meromorphicOrderAt F s₀ = (n₀ : WithTop ℤ))
    (hG_ord_s₀ : (n₀ : WithTop ℤ) < meromorphicOrderAt (fun z => F z - P z) s₀) :
    (∑ s ∈ S, (-(meromorphicOrderAt (fun z => F z - P z) s).untop₀).toNat)
      < (∑ s ∈ S, (-(meromorphicOrderAt F s).untop₀).toNat) := by
  have hdepth_s₀ : (-(meromorphicOrderAt (fun z => F z - P z) s₀).untop₀).toNat
      < (-(meromorphicOrderAt F s₀).untop₀).toNat := by
    rw [hFs₀]; exact depthTerm_lt_of_lt hn₀_neg hG_ord_s₀
  refine Finset.sum_lt_sum (fun s hs => ?_) ⟨s₀, hs₀S, hdepth_s₀⟩
  by_cases hss₀ : s = s₀
  · subst hss₀; exact le_of_lt hdepth_s₀
  · refine depthTerm_le_of_sub (hP_an_off s hss₀).meromorphicOrderAt_nonneg ?_
    have hadd := meromorphicOrderAt_add (hF_mero s (hmem_cb s hs))
      (hP_an_off s hss₀).meromorphicAt.neg
    rwa [← meromorphicOrderAt_neg, ← sub_eq_add_neg] at hadd

/-- **Transferring the residue formula across a peeled term.** If the formula holds for the
remainder `F − P` and `P` contributes its own residue sum, it holds for `F`: both the circle
integral and the residue sum split additively across the subtraction. -/
private lemma circleIntegral_eq_residueSum_of_sub {c : ℂ} {R : ℝ} (S : Finset ℂ)
    {F P : ℂ → ℂ} (hF_int : CircleIntegrable F c R) (hP_int : CircleIntegrable P c R)
    (hF_mero : MeromorphicOn F (closedBall c R)) (hP_mero : MeromorphicOn P (closedBall c R))
    (hmem_cb : ∀ s ∈ S, s ∈ closedBall c R)
    (hP : circleIntegral P c R = 2 * (Real.pi : ℂ) * Complex.I * ∑ s ∈ S, residue P s)
    (hG : circleIntegral (fun z => F z - P z) c R
      = 2 * (Real.pi : ℂ) * Complex.I * ∑ s ∈ S, residue (fun z => F z - P z) s) :
    circleIntegral F c R = 2 * (Real.pi : ℂ) * Complex.I * ∑ s ∈ S, residue F s := by
  have hG_mero : MeromorphicOn (fun z => F z - P z) (closedBall c R) := hF_mero.sub hP_mero
  have hint : circleIntegral F c R
      = circleIntegral (fun z => F z - P z) c R + circleIntegral P c R := by
    simpa using circleIntegral.integral_add (hF_int.sub hP_int) hP_int
  have hres_add : ∑ s ∈ S, residue F s
      = (∑ s ∈ S, residue (fun z => F z - P z) s) + ∑ s ∈ S, residue P s := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hfun : (fun z => F z - P z) + P = F := by funext z; simp
    conv_lhs => rw [← hfun]
    exact residue_add (hG_mero s (hmem_cb s hs)) (hP_mero s (hmem_cb s hs))
  rw [hint, hG, hP, hres_add]
  ring

/-- One pole-peeling step of the residue theorem. Given `F` analytic off the finite set `S` with a
pole at `s₀ ∈ S`, subtracting the leading Laurent term at `s₀` yields `G` that is still analytic off
`S`, has strictly smaller total pole depth, and whose residue formula implies that of `F`. -/
private lemma residueTheorem_step {c : ℂ} {R : ℝ} (hR : 0 < R) (S : Finset ℂ)
    (hS : (S : Set ℂ) ⊆ ball c R) {F : ℂ → ℂ} (hF_mero : MeromorphicOn F (closedBall c R))
    (hF_off : ∀ z ∈ closedBall c R, z ∉ S → AnalyticAt ℂ F z)
    {s₀ : ℂ} (hs₀S : s₀ ∈ S) (hs₀_neg : meromorphicOrderAt F s₀ < 0) :
    ∃ G : ℂ → ℂ, MeromorphicOn G (closedBall c R) ∧
      (∀ z ∈ closedBall c R, z ∉ S → AnalyticAt ℂ G z) ∧
      (∑ s ∈ S, (-(meromorphicOrderAt G s).untop₀).toNat)
        < (∑ s ∈ S, (-(meromorphicOrderAt F s).untop₀).toNat) ∧
      (circleIntegral G c R = 2 * (Real.pi : ℂ) * Complex.I * ∑ s ∈ S, residue G s →
        circleIntegral F c R = 2 * (Real.pi : ℂ) * Complex.I * ∑ s ∈ S, residue F s) := by
  -- Boundary facts: `S` avoids the circle, so `F` is analytic — hence integrable — there.
  have hmem_cb : ∀ s ∈ S, s ∈ closedBall c R :=
    fun s hs => ball_subset_closedBall (hS (Finset.mem_coe.2 hs))
  have hsphere_notS : ∀ z ∈ sphere c R, z ∉ S := by
    intro z hz hzS
    rw [mem_sphere] at hz
    exact absurd hz (ne_of_lt (mem_ball.1 (hS (Finset.mem_coe.2 hzS))))
  have hF_int : CircleIntegrable F c R :=
    circleIntegrable_of_analyticOn_sphere hR.le fun z hz =>
      hF_off z (sphere_subset_closedBall hz) (hsphere_notS z hz)
  -- Laurent data at the pole `s₀`: a non-vanishing germ `g` and the (negative) order `n₀`.
  have hs₀_ball : s₀ ∈ ball c R := hS (Finset.mem_coe.2 hs₀S)
  have hF_mero_s₀ : MeromorphicAt F s₀ := hF_mero s₀ (hmem_cb s₀ hs₀S)
  have hord_ne_top : meromorphicOrderAt F s₀ ≠ ⊤ := ne_top_of_lt hs₀_neg
  obtain ⟨g, hg_an, hg_ne, hF_germ⟩ := (meromorphicOrderAt_ne_top_iff hF_mero_s₀).1 hord_ne_top
  set n₀ : ℤ := (meromorphicOrderAt F s₀).untop₀ with hn₀_def
  have hFs₀ : meromorphicOrderAt F s₀ = (n₀ : WithTop ℤ) :=
    (WithTop.coe_untop₀_of_ne_top hord_ne_top).symm
  have hn₀_neg : n₀ < 0 := by rw [hFs₀] at hs₀_neg; exact_mod_cast hs₀_neg
  -- Peel the leading term `P = g s₀ · (· − s₀) ^ n₀`; set `G := F − P`, still analytic off `S`.
  set P : ℂ → ℂ := fun z => g s₀ * (z - s₀) ^ n₀ with hP_def
  set G : ℂ → ℂ := fun z => F z - P z with hG_def
  have hP_an_off : ∀ z, z ≠ s₀ → AnalyticAt ℂ P z := fun z hz =>
    analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).fun_zpow (sub_ne_zero.2 hz))
  have hP_mero : MeromorphicOn P (closedBall c R) := fun z _ => by rw [hP_def]; fun_prop
  have hG_mero : MeromorphicOn G (closedBall c R) := hF_mero.sub hP_mero
  have hG_off : ∀ z ∈ closedBall c R, z ∉ S → AnalyticAt ℂ G z := by
    intro z hz hzS
    exact (hF_off z hz hzS).sub (hP_an_off z fun h => hzS (h ▸ hs₀S))
  -- Total pole depth strictly drops: the order at `s₀` rises above `n₀`, and nowhere else falls.
  have hG_germ : G =ᶠ[𝓝[≠] s₀] fun z => (z - s₀) ^ n₀ • g z - g s₀ • (z - s₀) ^ n₀ := by
    filter_upwards [hF_germ] with z hz
    simp only [hG_def, hP_def, hz, smul_eq_mul]
  have hG_ord_s₀ : (n₀ : WithTop ℤ) < meromorphicOrderAt G s₀ := by
    rw [meromorphicOrderAt_congr hG_germ]; exact meromorphicOrderAt_sub_leadingTerm_gt hg_an
  have hdepth_lt : (∑ s ∈ S, (-(meromorphicOrderAt G s).untop₀).toNat)
      < (∑ s ∈ S, (-(meromorphicOrderAt F s).untop₀).toNat) :=
    sum_depthTerm_sub_lt S hF_mero hmem_cb hs₀S hP_an_off hn₀_neg hFs₀ hG_ord_s₀
  -- Split `∮ F = ∮ G + ∮ P` and `∑ res F = ∑ res G + ∑ res P`, transferring `G`'s formula to `F`.
  have hP_int : CircleIntegrable P c R :=
    circleIntegrable_of_analyticOn_sphere hR.le fun z hz =>
      hP_an_off z fun h => hsphere_notS z hz (h ▸ hs₀S)
  have hPint : circleIntegral P c R = 2 * (Real.pi : ℂ) * Complex.I * ∑ s ∈ S, residue P s := by
    rw [hP_def]; exact circleIntegral_leadingTerm_eq_residueSum (g s₀) hs₀_ball hn₀_neg S hs₀S
  exact ⟨G, hG_mero, hG_off, hdepth_lt, fun hG_eq =>
    circleIntegral_eq_residueSum_of_sub S hF_int hP_int hF_mero hP_mero hmem_cb hPint hG_eq⟩

/-- The residue theorem for a function `F` analytic off the finite set `S` (so `S` contains every
pole and `F` is continuous on the boundary circle): `∮ F = 2πi · ∑_{s ∈ S} residue F s`. The
parameter `d` is the total pole depth `∑_{s ∈ S} (-(order F s).untop₀).toNat`, carried by the strong
induction that peels one pole per step via `residueTheorem_step`. -/
private lemma residueTheorem_aux {c : ℂ} {R : ℝ} (hR : 0 < R) (S : Finset ℂ)
    (hS : (S : Set ℂ) ⊆ ball c R) (d : ℕ) : ∀ F : ℂ → ℂ, MeromorphicOn F (closedBall c R) →
      (∀ z ∈ closedBall c R, z ∉ S → AnalyticAt ℂ F z) →
      (∑ s ∈ S, (-(meromorphicOrderAt F s).untop₀).toNat) = d →
      circleIntegral F c R = 2 * (Real.pi : ℂ) * Complex.I * ∑ s ∈ S, residue F s := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro F hF_mero hF_off hdepth
    have hmem_cb : ∀ s ∈ S, s ∈ closedBall c R :=
      fun s hs => ball_subset_closedBall (hS (Finset.mem_coe.2 hs))
    by_cases hpole : ∃ s₀ ∈ S, meromorphicOrderAt F s₀ < 0
    · obtain ⟨s₀, hs₀S, hs₀_neg⟩ := hpole
      obtain ⟨G, hG_mero, hG_off, hdepth_lt, hreduce⟩ :=
        residueTheorem_step hR S hS hF_mero hF_off hs₀S hs₀_neg
      refine hreduce (ih _ ?_ G hG_mero hG_off rfl)
      rw [← hdepth]; exact hdepth_lt
    · simp only [not_exists, not_and, not_lt] at hpole
      have hnonneg : ∀ z ∈ closedBall c R, 0 ≤ meromorphicOrderAt F z := by
        intro z hz
        by_cases hzS : z ∈ S
        · exact hpole z hzS
        · exact (hF_off z hz hzS).meromorphicOrderAt_nonneg
      rw [circleIntegral_eq_zero_of_meromorphicOrderAt_nonneg hR.le hF_mero hnonneg,
        Finset.sum_eq_zero fun s hs =>
          residue_eq_zero_of_meromorphicOrderAt_nonneg (hnonneg s (hmem_cb s hs))]
      ring

/-- **The classical residue theorem on a circle** (sharp support form). If `f` is meromorphic on the
closed disc `C(c, R)` (`R > 0`) and every pole lies in a finite set `S` inside the open disc, then
the contour integral of `f` around the boundary circle is `2πi` times the sum of the residues over
`S`:
`∮_{C(c,R)} f = 2πi · ∑_{s ∈ S} residue f s`.
`S` need only contain the poles (the points of negative meromorphic order); residues at points of
nonnegative order vanish, so listing extra points leaves the sum unchanged. -/
theorem classicalResidueTheorem_circle_of_meromorphicOrderAt_neg {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (S : Finset ℂ) (hf : MeromorphicOn f (Metric.closedBall c R))
    (hS : (S : Set ℂ) ⊆ Metric.ball c R)
    (hsupp : ∀ z ∈ Metric.closedBall c R, meromorphicOrderAt f z < 0 → z ∈ S) :
    circleIntegral f c R = 2 * (Real.pi : ℂ) * Complex.I * (∑ s ∈ S, residue f s) := by
  -- Pass to the meromorphic normal form `F` of `f`: it is genuinely analytic off `S` (whereas raw
  -- `f` may take isolated "wrong values"), and the circle integral and residues are unchanged.
  set F := toMeromorphicNFOn f (closedBall c R) with hF_def
  have hF_mero : MeromorphicOn F (closedBall c R) :=
    (meromorphicNFOn_toMeromorphicNFOn f _).meromorphicOn
  have hordF : ∀ z ∈ closedBall c R, meromorphicOrderAt F z = meromorphicOrderAt f z :=
    fun z hz => meromorphicOrderAt_toMeromorphicNFOn hf hz
  have hF_off : ∀ z ∈ closedBall c R, z ∉ S → AnalyticAt ℂ F z := by
    intro z hz hzS
    have h0 : 0 ≤ meromorphicOrderAt F z := by
      rw [hordF z hz]; by_contra h; exact hzS (hsupp z hz (not_le.1 h))
    exact (meromorphicNFOn_toMeromorphicNFOn f _ hz).meromorphicOrderAt_nonneg_iff_analyticAt.1 h0
  have htransfer_int : circleIntegral f c R = circleIntegral F c R := by
    refine circleIntegral.circleIntegral_congr_codiscreteWithin ?_ hR.ne'
    have hspU : sphere c |R| ⊆ closedBall c R := by
      rw [abs_of_pos hR]; exact sphere_subset_closedBall
    exact (toMeromorphicNFOn_eqOn_codiscrete hf).filter_mono (Filter.codiscreteWithin_mono hspU)
  have htransfer_res : ∀ s ∈ S, residue f s = residue F s := fun s hs =>
    residue_congr_nhdsNE
      (hf.toMeromorphicNFOn_eq_self_on_nhdsNE
        (ball_subset_closedBall (hS (Finset.mem_coe.2 hs)))).symm
  rw [htransfer_int, Finset.sum_congr rfl htransfer_res]
  exact residueTheorem_aux hR S hS _ F hF_mero hF_off rfl

/-- **The classical residue theorem on a circle** (roadmap form). If `f` is meromorphic on the
closed disc `C(c, R)` (`R > 0`) and every point of nonzero meromorphic order lies in a finite set
`S` inside the open disc, then `∮_{C(c,R)} f = 2πi · ∑_{s ∈ S} residue f s`. Since residues at
non-poles vanish, `classicalResidueTheorem_circle_of_meromorphicOrderAt_neg` proves the same
conclusion asking only the poles (points of negative order) to lie in `S`. -/
theorem classicalResidueTheorem_circle {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R) (S : Finset ℂ)
    (hf : MeromorphicOn f (Metric.closedBall c R)) (hS : (S : Set ℂ) ⊆ Metric.ball c R)
    (hsupp : ∀ z ∈ Metric.closedBall c R, meromorphicOrderAt f z ≠ 0 → z ∈ S) :
    circleIntegral f c R = 2 * (Real.pi : ℂ) * Complex.I * (∑ s ∈ S, residue f s) :=
  classicalResidueTheorem_circle_of_meromorphicOrderAt_neg hR S hf hS
    fun z hz h => hsupp z hz (ne_of_lt h)

end TauCeti.Contour

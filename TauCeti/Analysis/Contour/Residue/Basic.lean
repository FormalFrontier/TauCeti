/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# The residue of a meromorphic function

For `f : ℂ → ℂ` and `z₀ : ℂ`, the **residue** `TauCeti.Contour.residue f z₀` is the order-`(−1)`
Laurent coefficient of `f` at `z₀` — the quantity summed in Cauchy's residue theorem. It is built
directly on Mathlib's `meromorphicOrderAt` / analytic-part API rather than a parallel
order-of-vanishing notion: writing `f z = (z − z₀) ^ n • g z` near `z₀` with `g` analytic and
`g z₀ ≠ 0` (where `n = meromorphicOrderAt f z₀`), the order-`(−1)` coefficient is the Taylor
coefficient of `g` at index `−1 − n`, i.e. `iteratedDeriv (−1 − n) g z₀ / (−1 − n)!`. The residue
is `0` at a point where `f` is analytic (`n ≥ 0`), and at a **simple pole** (`n = −1`) it is the
leading Laurent coefficient `meromorphicTrailingCoeffAt f z₀ = lim_{z→z₀} (z − z₀) · f z`.

As an unconditional value it is junk (`0`) when `f` is not meromorphic at `z₀`.

## Main definitions

* `TauCeti.Contour.residue` — the residue of `f` at `z₀`.

## Main results

* `TauCeti.Contour.residue_eq_of_order_lt_zero` — the characteristic value: from a reduced local
  presentation `f =ᶠ[𝓝[≠] z₀] (· − z₀) ^ n • g` with `g` analytic, `g z₀ ≠ 0`, and `n < 0`, the
  residue is `iteratedDeriv (−1 − n) g z₀ / (−1 − n)!`, independently of the presentation.
* `TauCeti.Contour.residue_eq_of_eventuallyEq_zpow_smul` — the same value from any presentation
  `f =ᶠ[𝓝[≠] z₀] (· − z₀) ^ n • g` with `g` analytic and `n ≤ −1`, dropping `g z₀ ≠ 0`.
* `TauCeti.Contour.residue_add`, `TauCeti.Contour.residue_const_mul`,
  `TauCeti.Contour.residue_smul`, `TauCeti.Contour.residue_sub`, `TauCeti.Contour.residue_sum` — the
  residue is linear in `f` (over functions meromorphic at `z₀`), including over finite sums.
* `TauCeti.Contour.residue_congr_nhdsNE` — the residue depends only on the germ of `f` on a
  punctured neighborhood of `z₀`.
* `TauCeti.Contour.residue_eq_zero_of_analyticAt` — the residue vanishes where `f` is analytic.
* `TauCeti.Contour.residue_eq_meromorphicTrailingCoeffAt_of_order_eq_neg_one` — at a simple pole the
  residue is the leading Laurent (trailing) coefficient.
* `TauCeti.Contour.residue_div_sub_pow_of_analyticAt` — the Cauchy-kernel computation
  `Res_{z₀} (g / (· − z₀) ^ (k + 1)) = g^{(k)}(z₀) / k !` for `g` analytic at `z₀`.

This is a Layer 0 object of the Hungerbühler–Wasem generalized residue theorem (HW Thm 3.3).

## Provenance

Adapted from the AINTLIB `LeanModularForms` project (the residue material of
`ForMathlib/GeneralizedResidueTheory/Residue.lean` and
`ForMathlib/GeneralizedResidueTheory/Residue/GeneralizedTheoremBase.lean`), specialised to the
raw-function design of the contour-integration roadmap and defined against Mathlib's
`meromorphicOrderAt` / `meromorphicTrailingCoeffAt` API.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997.
-/

public section

noncomputable section

open Filter Topology

namespace TauCeti.Contour

/-- The **residue** of `f` at `z₀`: the order-`(−1)` Laurent coefficient. When `f` is meromorphic at
`z₀` with a pole (`meromorphicOrderAt f z₀ = n < 0`), it is the Taylor coefficient at index `−1 − n`
of the analytic part `g` (with `f z = (z − z₀) ^ n • g z` near `z₀`); it is `0` when `f` is analytic
at `z₀` (`n ≥ 0`) and junk (`0`) when `f` is not meromorphic at `z₀`. See
`residue_eq_of_order_lt_zero` for the characteristic value from an arbitrary presentation and
`residue_eq_meromorphicTrailingCoeffAt_of_order_eq_neg_one` for the simple-pole value. -/
noncomputable def residue (f : ℂ → ℂ) (z₀ : ℂ) : ℂ :=
  haveI : Decidable (MeromorphicAt f z₀ ∧ meromorphicOrderAt f z₀ < 0) := Classical.propDecidable _
  if h : MeromorphicAt f z₀ ∧ meromorphicOrderAt f z₀ < 0 then
    iteratedDeriv (-1 - (meromorphicOrderAt f z₀).untop₀).toNat
        ((meromorphicOrderAt_ne_top_iff h.1).1 (ne_top_of_lt h.2)).choose z₀ /
      ((-1 - (meromorphicOrderAt f z₀).untop₀).toNat.factorial : ℂ)
  else 0

/-- **Characteristic value of the residue at a pole.** If `f z = (z − z₀) ^ n • g z` near `z₀` (on
the punctured neighborhood) with `g` analytic at `z₀`, `g z₀ ≠ 0`, and `n < 0`, then the residue is
the Taylor coefficient of `g` at index `−1 − n`. This is the standard reduced analytic presentation;
the order equality `meromorphicOrderAt f z₀ = n` is derived from it, and the value is independent of
the chosen presentation `g`. -/
theorem residue_eq_of_order_lt_zero {f g : ℂ → ℂ} {z₀ : ℂ} {n : ℤ}
    (hlt : n < 0) (hg : AnalyticAt ℂ g z₀) (hg_ne : g z₀ ≠ 0)
    (hfg : f =ᶠ[𝓝[≠] z₀] fun z => (z - z₀) ^ n • g z) :
    residue f z₀ = iteratedDeriv (-1 - n).toNat g z₀ / ((-1 - n).toNat.factorial : ℂ) := by
  have hf : MeromorphicAt f z₀ :=
    MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt.mpr ⟨n, g, hg, hfg⟩
  have hn : meromorphicOrderAt f z₀ = n :=
    (meromorphicOrderAt_eq_int_iff hf).mpr ⟨g, hg, hg_ne, hfg⟩
  have hlt' : meromorphicOrderAt f z₀ < 0 := by rw [hn]; exact_mod_cast hlt
  have huntop : (meromorphicOrderAt f z₀).untop₀ = n := by rw [hn, WithTop.untop₀_coe]
  rw [residue, dif_pos ⟨hf, hlt'⟩]
  set g₀ := ((meromorphicOrderAt_ne_top_iff hf).1 (ne_top_of_lt hlt')).choose with hg₀
  rw [huntop]
  obtain ⟨hg₀_an, -, hg₀_eq⟩ :=
    ((meromorphicOrderAt_ne_top_iff hf).1 (ne_top_of_lt hlt')).choose_spec
  rw [← hg₀] at hg₀_an hg₀_eq
  have hne : g₀ =ᶠ[𝓝[≠] z₀] g := by
    filter_upwards [hg₀_eq, hfg, self_mem_nhdsWithin] with z hz1 hz2 hz3
    rw [huntop] at hz1
    have hzne : (z - z₀) ^ n ≠ 0 := zpow_ne_zero n (sub_ne_zero.mpr hz3)
    have hcancel : (z - z₀) ^ n • g₀ z = (z - z₀) ^ n • g z := hz1.symm.trans hz2
    simpa only [smul_eq_mul] using mul_left_cancel₀ hzne (by simpa only [smul_eq_mul] using hcancel)
  have hnhds : g₀ =ᶠ[𝓝 z₀] g :=
    (hg₀_an.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hg.continuousAt).1 hne
  exact congrArg (· / ((-1 - n).toNat.factorial : ℂ)) (hnhds.iteratedDeriv_eq (-1 - n).toNat)

/-- If `f` is not meromorphic at `z₀`, its residue is `0` by definition. -/
@[simp]
theorem residue_of_not_meromorphicAt {f : ℂ → ℂ} {z₀ : ℂ} (h : ¬ MeromorphicAt f z₀) :
    residue f z₀ = 0 := by
  rw [residue, dif_neg]
  rintro ⟨h1, -⟩
  exact h h1

/-- The residue vanishes at a point where `f` has nonnegative meromorphic order (in particular where
`f` is analytic): there is no order-`(−1)` Laurent coefficient. -/
@[simp]
theorem residue_eq_zero_of_meromorphicOrderAt_nonneg {f : ℂ → ℂ} {z₀ : ℂ}
    (h : 0 ≤ meromorphicOrderAt f z₀) : residue f z₀ = 0 := by
  rw [residue, dif_neg]
  rintro ⟨-, h2⟩
  exact absurd h2 (not_lt.mpr h)

/-- The residue vanishes where `f` is analytic. -/
@[simp]
theorem residue_eq_zero_of_analyticAt {f : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀) :
    residue f z₀ = 0 :=
  residue_eq_zero_of_meromorphicOrderAt_nonneg hf.meromorphicOrderAt_nonneg

/-- The residue depends only on the germ of `f` on a punctured neighborhood of `z₀`: functions
agreeing near (but not necessarily at) `z₀` have the same residue. -/
theorem residue_congr_nhdsNE {f g : ℂ → ℂ} {z₀ : ℂ} (h : f =ᶠ[𝓝[≠] z₀] g) :
    residue f z₀ = residue g z₀ := by
  have hord : meromorphicOrderAt f z₀ = meromorphicOrderAt g z₀ := meromorphicOrderAt_congr h
  rcases lt_or_ge (meromorphicOrderAt g z₀) 0 with hlt | hge
  · have hgm : MeromorphicAt g z₀ := meromorphicAt_of_meromorphicOrderAt_ne_zero (ne_of_lt hlt)
    have hgn : meromorphicOrderAt g z₀ = ((meromorphicOrderAt g z₀).untop₀ : WithTop ℤ) :=
      (WithTop.coe_untop₀_of_ne_top (ne_top_of_lt hlt)).symm
    have hnlt : (meromorphicOrderAt g z₀).untop₀ < 0 := by
      have h0 := hlt; rw [hgn] at h0; exact_mod_cast h0
    obtain ⟨g₀, hg₀_an, hg₀_ne, hg₀_eq⟩ := (meromorphicOrderAt_ne_top_iff hgm).1 (ne_top_of_lt hlt)
    rw [residue_eq_of_order_lt_zero hnlt hg₀_an hg₀_ne (h.trans hg₀_eq),
      residue_eq_of_order_lt_zero hnlt hg₀_an hg₀_ne hg₀_eq]
  · rw [residue_eq_zero_of_meromorphicOrderAt_nonneg (f := f) (by rw [hord]; exact hge),
      residue_eq_zero_of_meromorphicOrderAt_nonneg (f := g) hge]

/-- At a **simple pole** (`meromorphicOrderAt f z₀ = −1`), the residue is the leading Laurent
coefficient `meromorphicTrailingCoeffAt f z₀`, i.e. `lim_{z→z₀} (z − z₀) · f z`. The `n = −1`
specialization of `residue_eq_of_order_lt_zero`: the Taylor coefficient at index `−1 − (−1) = 0` of
the analytic part `g` is just `g z₀`, which is the trailing coefficient. -/
@[simp]
theorem residue_eq_meromorphicTrailingCoeffAt_of_order_eq_neg_one {f : ℂ → ℂ} {z₀ : ℂ}
    (hord : meromorphicOrderAt f z₀ = -1) :
    residue f z₀ = meromorphicTrailingCoeffAt f z₀ := by
  have hf : MeromorphicAt f z₀ :=
    meromorphicAt_of_meromorphicOrderAt_ne_zero (by rw [hord]; decide)
  obtain ⟨g, hg_an, hg_ne, hg_eq⟩ := (meromorphicOrderAt_ne_top_iff hf).1 (by rw [hord]; decide)
  have htc : meromorphicTrailingCoeffAt f z₀ = g z₀ :=
    hg_an.meromorphicTrailingCoeffAt_of_eq_nhdsNE hg_eq
  have huntop : (meromorphicOrderAt f z₀).untop₀ = -1 := by
    rw [hord]; exact WithTop.untop₀_coe (-1 : ℤ)
  rw [huntop] at hg_eq
  rw [residue_eq_of_order_lt_zero (by decide) hg_an hg_ne hg_eq, htc]
  norm_num [iteratedDeriv_zero]

/-- **Taylor-shift invariance of the residue coefficient.** For `h` analytic at `z₀`, dividing the
`(p + i)`-th derivative at `z₀` of `(· − z₀) ^ p · h` by `(p + i)!` gives the same value as dividing
the `i`-th derivative of `h` by `i!`: multiplying an analytic germ by `(· − z₀) ^ p` shifts its
Taylor coefficients up by `p` without changing them. Only the top Leibniz term of the product rule
survives, since `(· − z₀) ^ p` and its first `p − 1` derivatives vanish at `z₀`. -/
private lemma iteratedDeriv_pow_sub_mul_div_factorial {z₀ : ℂ} (p i : ℕ) {h : ℂ → ℂ}
    (hh : AnalyticAt ℂ h z₀) :
    iteratedDeriv (p + i) (fun z => (z - z₀) ^ p * h z) z₀ / ((p + i).factorial : ℂ)
      = iteratedDeriv i h z₀ / (i.factorial : ℂ) := by
  have hpow_pd : ∀ j : ℕ, iteratedDeriv j (fun z : ℂ => (z - z₀) ^ p) z₀
      = ((if j = p then p.factorial else 0 : ℕ) : ℂ) := by
    intro j
    have hrw : (fun z : ℂ => (z - z₀) ^ p) = fun z : ℂ => (fun w : ℂ => w ^ p) (z + (-z₀)) := by
      funext z; rw [sub_eq_add_neg]
    rw [hrw, iteratedDeriv_comp_add_const j (fun w : ℂ => w ^ p) (-z₀)]
    simp only [add_neg_cancel, iteratedDeriv_fun_pow_zero]
  have hleib : iteratedDeriv (p + i) (fun z => (z - z₀) ^ p * h z) z₀
      = ((p + i).choose p * p.factorial : ℕ) * iteratedDeriv i h z₀ := by
    rw [iteratedDeriv_fun_mul (f := fun z : ℂ => (z - z₀) ^ p) (g := h) (by fun_prop)
        hh.contDiffAt, Finset.sum_eq_single p]
    · rw [hpow_pd p, Nat.add_sub_cancel_left, if_pos rfl]; push_cast; ring
    · intro j _ hjp; rw [hpow_pd j, if_neg hjp]; push_cast; ring
    · intro hp
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_add_right p i))) hp
  have hfac_pi : ((p + i).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hfac_i : (i.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hid : (((p + i).choose p * p.factorial : ℕ) : ℂ) * (i.factorial : ℂ)
      = ((p + i).factorial : ℂ) := by
    have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right p i)
    rw [Nat.add_sub_cancel_left] at h
    exact_mod_cast h
  rw [hleib, div_eq_div_iff hfac_pi hfac_i]
  linear_combination iteratedDeriv i h z₀ * hid

/-- The pole case (`meromorphicOrderAt f z₀ < 0`) of `residue_eq_of_eventuallyEq_zpow_smul`: the
residue of `f` at `z₀` equals the Taylor coefficient
`iteratedDeriv (-1 - n) g z₀ / (-1 - n)!` of the presentation factor `g`. -/
private theorem residue_eq_of_eventuallyEq_zpow_smul_of_order_lt_zero {f g : ℂ → ℂ} {z₀ : ℂ} {n : ℤ}
    (hg : AnalyticAt ℂ g z₀) (hfg : f =ᶠ[𝓝[≠] z₀] fun z => (z - z₀) ^ n • g z)
    (hf : MeromorphicAt f z₀)
    (hord_eq : meromorphicOrderAt f z₀ = (n : WithTop ℤ) + meromorphicOrderAt g z₀)
    (ha : meromorphicOrderAt f z₀ < 0) :
    residue f z₀ = iteratedDeriv (-1 - n).toNat g z₀ / ((-1 - n).toNat.factorial : ℂ) := by
  -- Reduce to `residue_eq_of_order_lt_zero` at the true order, then shift back to `g`.
  have hle : (n : WithTop ℤ) ≤ meromorphicOrderAt f z₀ :=
    hord_eq ▸ le_add_of_nonneg_right hg.meromorphicOrderAt_nonneg
  obtain ⟨g₀, hg₀_an, hg₀_ne, hf_eq⟩ := (meromorphicOrderAt_ne_top_iff hf).1 (ne_top_of_lt ha)
  set a := (meromorphicOrderAt f z₀).untop₀ with ha_def
  have hcoe : (a : WithTop ℤ) = meromorphicOrderAt f z₀ :=
    WithTop.coe_untop₀_of_ne_top (ne_top_of_lt ha)
  have ha_lt : a < 0 := by rw [← WithTop.coe_lt_coe, hcoe]; exact_mod_cast ha
  have hna : n ≤ a := by rw [← WithTop.coe_le_coe, hcoe]; exact hle
  rw [residue_eq_of_order_lt_zero ha_lt hg₀_an hg₀_ne hf_eq]
  have hg_eqNE : g =ᶠ[𝓝[≠] z₀] fun z => (z - z₀) ^ (a - n).toNat • g₀ z := by
    filter_upwards [hfg, hf_eq, self_mem_nhdsWithin] with z hz1 hz2 hz3
    have hzne : z - z₀ ≠ 0 := sub_ne_zero.mpr hz3
    have heq : (z - z₀) ^ n • g z = (z - z₀) ^ a • g₀ z := hz1.symm.trans hz2
    rw [smul_eq_mul, smul_eq_mul] at heq
    rw [smul_eq_mul]
    have h2 : (z - z₀) ^ a = (z - z₀) ^ n * (z - z₀) ^ (a - n).toNat := by
      rw [← zpow_natCast (z - z₀) (a - n).toNat, ← zpow_add₀ hzne, Int.toNat_of_nonneg (by omega)]
      congr 1; omega
    rw [h2, mul_assoc] at heq
    exact mul_left_cancel₀ (zpow_ne_zero n hzne) heq
  have hana : AnalyticAt ℂ (fun z => (z - z₀) ^ (a - n).toNat • g₀ z) z₀ := by
    simp only [smul_eq_mul]
    exact ((analyticAt_id.sub analyticAt_const).pow _).mul hg₀_an
  have hg_eq : g =ᶠ[𝓝 z₀] fun z => (z - z₀) ^ (a - n).toNat • g₀ z :=
    (hg.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hana.continuousAt).1 hg_eqNE
  have hsum : (a - n).toNat + (-1 - a).toNat = (-1 - n).toNat := by omega
  rw [hg_eq.iteratedDeriv_eq (-1 - n).toNat]
  simp only [smul_eq_mul]
  rw [← hsum, iteratedDeriv_pow_sub_mul_div_factorial (a - n).toNat (-1 - a).toNat hg₀_an]

/-- The pole-free case of `residue_eq_of_eventuallyEq_zpow_smul`: when
`meromorphicOrderAt f z₀ ≥ 0`, `f` has no pole so its residue is `0`, and `g` vanishes to
order `> -1 - n`, so the Taylor coefficient on the right is `0` as well. -/
private theorem residue_eq_of_eventuallyEq_zpow_smul_of_order_nonneg {f g : ℂ → ℂ} {z₀ : ℂ} {n : ℤ}
    (hn : n ≤ -1) (hg : AnalyticAt ℂ g z₀)
    (hord_eq : meromorphicOrderAt f z₀ = (n : WithTop ℤ) + meromorphicOrderAt g z₀)
    (ha : meromorphicOrderAt f z₀ ≥ 0) :
    residue f z₀ = iteratedDeriv (-1 - n).toNat g z₀ / ((-1 - n).toNat.factorial : ℂ) := by
  rw [residue_eq_zero_of_meromorphicOrderAt_nonneg ha]
  have hvanish : iteratedDeriv (-1 - n).toNat g z₀ = 0 := by
    refine (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hg).1 ?_ _ (Nat.lt_succ_self _)
    rcases eq_or_ne (analyticOrderAt g z₀) ⊤ with htop | htop
    · rw [htop]; exact le_top
    · lift analyticOrderAt g z₀ to ℕ using htop with m hm
      rw [Nat.cast_le]
      have hcompute : meromorphicOrderAt g z₀ = ((m : ℤ) : WithTop ℤ) := by
        rw [hg.meromorphicOrderAt_eq, ← hm]; simp
      have h0 : (0 : WithTop ℤ) ≤ (n : WithTop ℤ) + ((m : ℤ) : WithTop ℤ) := by
        rw [← hcompute, ← hord_eq]; exact ha
      rw [← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_le_coe] at h0
      omega
  rw [hvanish, zero_div]

/-- **Generalized characteristic value of the residue.** If `f z = (z − z₀) ^ n • g z` near `z₀` (on
the punctured neighborhood) with `g` analytic at `z₀` and `n ≤ −1`, then the residue is the Taylor
coefficient `iteratedDeriv (−1 − n) g z₀ / (−1 − n)!`. Unlike `residue_eq_of_order_lt_zero` this
drops the hypothesis `g z₀ ≠ 0`, so the presentation exponent `n` need not be the meromorphic order
of `f`: `g` may vanish at `z₀`, raising the true pole order above `n`; only when `g`'s vanishing
order is at least `-n` is `f` analytic (residue `0`). -/
theorem residue_eq_of_eventuallyEq_zpow_smul {f g : ℂ → ℂ} {z₀ : ℂ} {n : ℤ}
    (hn : n ≤ -1) (hg : AnalyticAt ℂ g z₀)
    (hfg : f =ᶠ[𝓝[≠] z₀] fun z => (z - z₀) ^ n • g z) :
    residue f z₀ = iteratedDeriv (-1 - n).toNat g z₀ / ((-1 - n).toNat.factorial : ℂ) := by
  have hf : MeromorphicAt f z₀ :=
    MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt.mpr ⟨n, g, hg, hfg⟩
  have hord_eq : meromorphicOrderAt f z₀ = (n : WithTop ℤ) + meromorphicOrderAt g z₀ := by
    have hsmul : (fun z => (z - z₀) ^ n • g z) = ((fun x : ℂ => x - z₀) ^ n) • g := by
      funext z; simp only [Pi.smul_apply', Pi.pow_apply]
    rw [meromorphicOrderAt_congr hfg, hsmul,
      meromorphicOrderAt_smul (by fun_prop) hg.meromorphicAt, meromorphicOrderAt_zpow_id_sub_const]
  rcases lt_or_ge (meromorphicOrderAt f z₀) 0 with ha | ha
  · exact residue_eq_of_eventuallyEq_zpow_smul_of_order_lt_zero hg hfg hf hord_eq ha
  · exact residue_eq_of_eventuallyEq_zpow_smul_of_order_nonneg hn hg hord_eq ha

/-- Any meromorphic `f` admits an analytic presentation `f z = (z − z₀) ^ m • φ z` near `z₀` at any
exponent `m` at or below its meromorphic order (padding the reduced presentation with a nonnegative
power of `z − z₀`). The factor `φ` is analytic but may vanish at `z₀` when `m` is strictly below the
order. Brings two meromorphic functions to a common exponent before adding their residues, and is
the factorisation entry point for the canonical Laurent data (`MeromorphicLaurent.lean`). -/
lemma exists_analyticAt_eventuallyEq_zpow_smul {f : ℂ → ℂ} {z₀ : ℂ} {m : ℤ}
    (hf : MeromorphicAt f z₀) (hm : (m : WithTop ℤ) ≤ meromorphicOrderAt f z₀) :
    ∃ φ : ℂ → ℂ, AnalyticAt ℂ φ z₀ ∧ f =ᶠ[𝓝[≠] z₀] fun z => (z - z₀) ^ m • φ z := by
  rcases eq_or_ne (meromorphicOrderAt f z₀) ⊤ with htop | htop
  · refine ⟨fun _ => 0, analyticAt_const, ?_⟩
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 htop] with z hz
    simp [hz]
  · obtain ⟨g₀, hg₀_an, _, hf_eq⟩ := (meromorphicOrderAt_ne_top_iff hf).1 htop
    set a := (meromorphicOrderAt f z₀).untop₀ with ha_def
    have hma : m ≤ a := by
      rw [← WithTop.coe_le_coe, WithTop.coe_untop₀_of_ne_top htop]; exact hm
    refine ⟨fun z => (z - z₀) ^ (a - m).toNat • g₀ z, ?_, ?_⟩
    · simp only [smul_eq_mul]
      exact ((analyticAt_id.sub analyticAt_const).pow _).mul hg₀_an
    · filter_upwards [hf_eq, self_mem_nhdsWithin] with z hz1 hz2
      have hzne : z - z₀ ≠ 0 := sub_ne_zero.mpr hz2
      have hexp : m + ((a - m).toNat : ℤ) = a := by omega
      rw [hz1, smul_eq_mul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
        ← zpow_natCast (z - z₀) (a - m).toNat, ← zpow_add₀ hzne, hexp]

/-- **Additivity of the residue.** The residue is additive on functions meromorphic at `z₀`. -/
@[simp]
theorem residue_add {f g : ℂ → ℂ} {z₀ : ℂ} (hf : MeromorphicAt f z₀) (hg : MeromorphicAt g z₀) :
    residue (f + g) z₀ = residue f z₀ + residue g z₀ := by
  obtain ⟨m, hm1, hmf, hmg⟩ : ∃ m : ℤ, m ≤ -1 ∧ (m : WithTop ℤ) ≤ meromorphicOrderAt f z₀ ∧
      (m : WithTop ℤ) ≤ meromorphicOrderAt g z₀ := by
    refine ⟨min (min (meromorphicOrderAt f z₀).untop₀ (meromorphicOrderAt g z₀).untop₀) (-1),
      min_le_right _ _, ?_, ?_⟩
    · rcases eq_or_ne (meromorphicOrderAt f z₀) ⊤ with h | h
      · rw [h]; exact le_top
      · rw [← WithTop.coe_untop₀_of_ne_top h, WithTop.coe_le_coe]
        exact (min_le_left _ _).trans (min_le_left _ _)
    · rcases eq_or_ne (meromorphicOrderAt g z₀) ⊤ with h | h
      · rw [h]; exact le_top
      · rw [← WithTop.coe_untop₀_of_ne_top h, WithTop.coe_le_coe]
        exact (min_le_left _ _).trans (min_le_right _ _)
  obtain ⟨φf, hφf_an, hφf_eq⟩ := exists_analyticAt_eventuallyEq_zpow_smul hf hmf
  obtain ⟨φg, hφg_an, hφg_eq⟩ := exists_analyticAt_eventuallyEq_zpow_smul hg hmg
  have hφfg_eq : (f + g) =ᶠ[𝓝[≠] z₀] fun z => (z - z₀) ^ m • (φf + φg) z := by
    filter_upwards [hφf_eq, hφg_eq] with z hz1 hz2
    simp only [Pi.add_apply, hz1, hz2, smul_add]
  rw [residue_eq_of_eventuallyEq_zpow_smul hm1 hφf_an hφf_eq,
    residue_eq_of_eventuallyEq_zpow_smul hm1 hφg_an hφg_eq,
    residue_eq_of_eventuallyEq_zpow_smul hm1 (hφf_an.add hφg_an) hφfg_eq,
    iteratedDeriv_add hφf_an.contDiffAt hφg_an.contDiffAt, add_div]

/-- **Scaling of the residue.** Scaling `f` by a constant scales its residue by that constant. -/
@[simp]
theorem residue_const_mul {f : ℂ → ℂ} {z₀ : ℂ} (c : ℂ) (hf : MeromorphicAt f z₀) :
    residue (fun z => c * f z) z₀ = c * residue f z₀ := by
  obtain ⟨m, hm1, hmf⟩ : ∃ m : ℤ, m ≤ -1 ∧ (m : WithTop ℤ) ≤ meromorphicOrderAt f z₀ := by
    refine ⟨min (meromorphicOrderAt f z₀).untop₀ (-1), min_le_right _ _, ?_⟩
    rcases eq_or_ne (meromorphicOrderAt f z₀) ⊤ with h | h
    · rw [h]; exact le_top
    · rw [← WithTop.coe_untop₀_of_ne_top h, WithTop.coe_le_coe]; exact min_le_left _ _
  obtain ⟨φ, hφ_an, hφ_eq⟩ := exists_analyticAt_eventuallyEq_zpow_smul hf hmf
  have hcφ_an : AnalyticAt ℂ (fun z => c * φ z) z₀ := analyticAt_const.mul hφ_an
  have hcf_eq : (fun z => c * f z) =ᶠ[𝓝[≠] z₀] fun z => (z - z₀) ^ m • (fun z => c * φ z) z := by
    filter_upwards [hφ_eq] with z hz
    simp only [hz, smul_eq_mul]; ring
  rw [residue_eq_of_eventuallyEq_zpow_smul hm1 hφ_an hφ_eq,
    residue_eq_of_eventuallyEq_zpow_smul hm1 hcφ_an hcf_eq,
    iteratedDeriv_const_mul_field c φ, mul_div_assoc]

/-- **Scaling of the residue (pointwise `•`).** The residue commutes with scalar multiplication;
the `Pi.smul` companion to `residue_const_mul`. -/
@[simp]
theorem residue_smul {f : ℂ → ℂ} {z₀ : ℂ} (c : ℂ) (hf : MeromorphicAt f z₀) :
    residue (c • f) z₀ = c • residue f z₀ := by
  have hcf : (c • f) = fun z => c * f z := by funext z; rw [Pi.smul_apply, smul_eq_mul]
  rw [hcf, residue_const_mul c hf, smul_eq_mul]

/-- **Subtractivity of the residue.** The residue distributes over subtraction of meromorphic
functions; the `−1` scaling case of `residue_add` and `residue_const_mul`. -/
@[simp]
theorem residue_sub {f g : ℂ → ℂ} {z₀ : ℂ} (hf : MeromorphicAt f z₀) (hg : MeromorphicAt g z₀) :
    residue (f - g) z₀ = residue f z₀ - residue g z₀ := by
  have hng : MeromorphicAt (fun z => (-1 : ℂ) * g z) z₀ :=
    analyticAt_const.meromorphicAt.mul hg
  have heq : f - g = f + fun z => (-1 : ℂ) * g z := by
    funext z; simp only [Pi.sub_apply, Pi.add_apply, neg_one_mul]; ring
  rw [heq, residue_add hf hng, residue_const_mul (-1) hg]
  ring

/-- **The residue of a finite sum.** For a finite family of functions meromorphic at `z₀`, the
residue of the sum is the sum of the residues — the form consumed by the residue theorem. -/
@[simp]
theorem residue_sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℂ} {z₀ : ℂ}
    (hf : ∀ i ∈ s, MeromorphicAt (f i) z₀) :
    residue (∑ i ∈ s, f i) z₀ = ∑ i ∈ s, residue (f i) z₀ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact residue_eq_zero_of_analyticAt analyticAt_const
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      residue_add (hf a (Finset.mem_insert_self a s))
        (MeromorphicAt.sum fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

/-- **The residue of a Laurent monomial**: `residue (a / (z - z₀)^(k+1)) z₀` is `a` for `k = 0`
and `0` for higher-order terms. -/
@[simp]
theorem residue_const_div_sub_pow (a z₀ : ℂ) (k : ℕ) :
    residue (fun z => a / (z - z₀) ^ (k + 1)) z₀ = if k = 0 then a else 0 := by
  have hfg : (fun z => a / (z - z₀) ^ (k + 1)) =ᶠ[𝓝[≠] z₀]
      fun z => (z - z₀) ^ (-(k + 1 : ℕ) : ℤ) • a :=
    Filter.Eventually.of_forall fun z => by
      -- `change` beta-reduces the applied lambdas; the `rw` patterns do not match otherwise.
      change a / (z - z₀) ^ (k + 1) = (z - z₀) ^ (-(k + 1 : ℕ) : ℤ) • a
      rw [smul_eq_mul, zpow_neg, zpow_natCast, mul_comm, div_eq_mul_inv]
  rw [residue_eq_of_eventuallyEq_zpow_smul (by omega) analyticAt_const hfg]
  have htoNat : (-1 - (-(k + 1 : ℕ) : ℤ)).toNat = k := by omega
  rw [htoNat, iteratedDeriv_const]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · simp [hk.ne']

/-- **The residue of the Cauchy kernel.** If `g` is analytic at `z₀`, then the function
`g z / (z - z₀) ^ (k + 1)` has residue the Taylor coefficient `iteratedDeriv k g z₀ / k !` at `z₀`:
the whole Laurent principal part comes from the first `k + 1` Taylor terms of `g`, and only the one
of index `k` sits at order `−1`. This is the residue behind Cauchy's integral formula for the
`k`-th derivative; the constant case is `TauCeti.Contour.residue_const_div_sub_pow`. -/
theorem residue_div_sub_pow_of_analyticAt {g : ℂ → ℂ} {z₀ : ℂ} (hg : AnalyticAt ℂ g z₀) (k : ℕ) :
    residue (fun z => g z / (z - z₀) ^ (k + 1)) z₀
      = iteratedDeriv k g z₀ / (k.factorial : ℂ) := by
  have hfg : (fun z => g z / (z - z₀) ^ (k + 1)) =ᶠ[𝓝[≠] z₀]
      fun z => (z - z₀) ^ (-(k + 1 : ℕ) : ℤ) • g z :=
    Filter.Eventually.of_forall fun z => by
      -- `change` beta-reduces the applied lambdas; the `rw` patterns do not match otherwise.
      change g z / (z - z₀) ^ (k + 1) = (z - z₀) ^ (-(k + 1 : ℕ) : ℤ) • g z
      rw [smul_eq_mul, zpow_neg, zpow_natCast, mul_comm, div_eq_mul_inv]
  rw [residue_eq_of_eventuallyEq_zpow_smul (by omega) hg hfg,
    show (-1 - (-(k + 1 : ℕ) : ℤ)).toNat = k by omega]

/-- **The residue from a Laurent expansion.** If `f z = g z + ∑ k, a k / (z - z₀)^(k+1)` near
`z₀` with `g` analytic at `z₀`, then `residue f z₀` is the first Laurent coefficient `a 0` (or
`0` for an empty expansion): the analytic part and the higher-order terms contribute nothing. -/
theorem residue_of_laurent_expansion {f g : ℂ → ℂ} {z₀ : ℂ} {N : ℕ} {a : Fin N → ℂ}
    (hg : AnalyticAt ℂ g z₀)
    (hf_eq : ∀ᶠ z in 𝓝[≠] z₀, f z = g z + ∑ k : Fin N, a k / (z - z₀) ^ (k.val + 1)) :
    residue f z₀ = if h : 0 < N then a ⟨0, h⟩ else 0 := by
  have hmono : ∀ k : Fin N, MeromorphicAt (fun z => a k / (z - z₀) ^ (k.val + 1)) z₀ :=
    fun k => by fun_prop
  have hf_eq' : f =ᶠ[𝓝[≠] z₀]
      g + ∑ k : Fin N, fun z => a k / (z - z₀) ^ (k.val + 1) := by
    filter_upwards [hf_eq] with z hz
    simpa [Finset.sum_apply] using hz
  rw [residue_congr_nhdsNE hf_eq',
    residue_add hg.meromorphicAt (MeromorphicAt.sum fun k _ => hmono k),
    residue_eq_zero_of_analyticAt hg, zero_add, residue_sum _ fun k _ => hmono k]
  simp only [residue_const_div_sub_pow]
  rcases Nat.eq_zero_or_pos N with rfl | hpos
  · simp
  · rw [dif_pos hpos, Finset.sum_eq_single ⟨0, hpos⟩ (fun k _ hk => if_neg fun h0 =>
      hk (Fin.ext h0)) (by simp), if_pos rfl]

end TauCeti.Contour

end

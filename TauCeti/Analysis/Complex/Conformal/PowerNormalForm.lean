/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.BranchLogRoot
public import TauCeti.Analysis.Complex.Conformal.LocalDegree
import Mathlib.Analysis.Normed.Module.Connected

/-!
# The local normal form of a holomorphic map

`Conformal/LocalDegree.lean` proves that a holomorphic `f` attains every value near `f z₀` exactly
`n` times near `z₀`, where `n` is the order of vanishing of `f - f z₀`, and reads that as saying
that `f` is a branched cover behaving "like `z ↦ z ^ n` up to a change of coordinates". This file
supplies the change of coordinates: on a small disc about `z₀` there is a **holomorphic chart** `φ`,
injective and with `φ z₀ = 0` and `deriv φ z₀ ≠ 0`, in which

`f z = f z₀ + φ z ^ n`.

So `f` is not merely `n`-to-one near `z₀`; it *is* the `n`-th power map, read in a holomorphic
coordinate. This is the qualitative half of the third target, the open-mapping degree, of layer
**L0 (the local-mapping engine)** of the conformal-mapping roadmap, of which
`Conformal/LocalDegree.lean` proves the counting half.

## The construction

Everything comes from the factorisation `A z = (z - z₀) ^ n • g z` with `g z₀ ≠ 0` that Mathlib's
`AnalyticAt.analyticOrderAt_eq_natCast` attaches to a zero of order `n` — here `A = f - f z₀`. On a
disc small enough that `g` is holomorphic and zero-free, `g` has a holomorphic `n`-th root `h`
(`TauCeti.exists_differentiableOn_pow_eq`, the disc being convex, hence simply connected), and
`φ z = (z - z₀) * h z` is the chart: `φ ^ n = (z - z₀) ^ n * h ^ n = A`, while `deriv φ z₀ = h z₀`
is nonzero because `h z₀ ^ n = g z₀ ≠ 0`. A nonvanishing derivative buys injectivity on a possibly
smaller disc, by the local injectivity criterion `TauCeti.exists_injOn_nhds_iff_deriv_ne_zero` of
`Conformal/LocalDegree.lean`.

Injectivity is what makes `φ` a chart rather than a bare factorisation, and it is the geometric
content the counting form of the degree leaves implicit: through it the `n` preimages of a value
`w` near `f z₀` are located as the `φ`-preimages of the `n` `n`-th roots of `w - f z₀`.

The chart is not unique — replacing `φ` by `ζ * φ` for an `n`-th root of unity `ζ` changes nothing
— so it is produced existentially and not named.

## Local `n`-th roots

Read backwards, the normal form answers the question of when a holomorphic germ has a holomorphic
`n`-th root: exactly when `n` divides its order of vanishing
(`TauCeti.exists_eventually_pow_eq_iff_dvd`). One direction takes `φ ^ (m / n)` for the chart `φ` of
an order-`m` zero, the other reads off `analyticOrderNatAt (ψ ^ n) = n * analyticOrderNatAt ψ`.
Mathlib's `Complex.exists_continuousOn_pow_eq` and the holomorphic upgrade of it in
`TauCeti/Analysis/Complex/BranchLogRoot.lean` require the function to be **zero-free**, so between
them they settle only the case of order `0`; a germ that does vanish is what the criterion here
covers.

## Main results

* `TauCeti.exists_pow_eq_of_analyticOrderAt` — a zero of finite order `n ≠ 0` is the `n`-th power
  of an injective holomorphic chart vanishing at the point.
* `TauCeti.localNormalForm` — the local normal form `f z = f z₀ + φ z ^ n` of a holomorphic map at
  a point at which it is not locally constant.
* `TauCeti.exists_eventually_pow_eq_iff_dvd` — a holomorphic germ of finite order `m` has a
  holomorphic `n`-th root iff `n ∣ m`.

## Coordination with upstream Mathlib

Per the *Coordination with upstream Mathlib* section of `ConformalMapping/README.md`, L0 material
overlaps [mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), the
in-progress human-curated Riemann-mapping-theorem effort, which proves several L0 statements
internally as private lemmas. **This file is therefore a temporary shim**: once corresponding
Mathlib lemmas land, these statements should be backed by them — or deleted and their consumers
refactored — rather than maintained as independent re-proofs. What Tau Ceti adds at L0 is named,
discoverable API, not first proof. The branch statements underneath, Mathlib's
`Complex.exists_continuousOn_eqOn_exp_comp` and `Complex.exists_continuousOn_pow_eq`
(`Mathlib/Analysis/Complex/BranchLogRoot.lean`), are consumed through the holomorphic upgrade in
`TauCeti/Analysis/Complex/BranchLogRoot.lean`, not rebuilt.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 4 §3.3.
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. IV §7.
-/

public section

open Complex Metric Filter Topology

namespace TauCeti

/-- A holomorphic germ that does not vanish at `z₀` has a holomorphic `n`-th root on a disc about
`z₀`: the disc is convex, hence simply connected, so `TauCeti.exists_differentiableOn_pow_eq`
applies once the disc is small enough for the germ to be holomorphic and zero-free on it. -/
private lemma exists_ball_pow_eq_of_ne_zero {A : ℂ → ℂ} {z₀ : ℂ} {n : ℕ} (hA : AnalyticAt ℂ A z₀)
    (h0 : A z₀ ≠ 0) (hn : n ≠ 0) :
    ∃ r > 0, ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (ball z₀ r) ∧ ∀ z ∈ ball z₀ r, h z ^ n = A z := by
  have hloc : ∀ᶠ z in 𝓝 z₀, AnalyticAt ℂ A z ∧ A z ≠ 0 :=
    hA.eventually_analyticAt.and (hA.continuousAt.eventually_ne h0)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hloc
  have hsc : IsSimplyConnected (ball z₀ r) := by
    have : ContractibleSpace (ball z₀ r) := Metric.contractibleSpace_ball hr
    exact SimplyConnectedSpace.ofContractible _
  have hAd : DifferentiableOn ℂ A (ball z₀ r) := fun z hz =>
    ((hball (mem_ball.mp hz)).1.differentiableAt).differentiableWithinAt
  have hA0 : (0 : ℂ) ∉ A '' ball z₀ r := by
    rintro ⟨z, hz, hz0⟩
    exact (hball (mem_ball.mp hz)).2 hz0
  obtain ⟨h, hhd, hheq⟩ := exists_differentiableOn_pow_eq hsc isOpen_ball hAd hA0 hn
  exact ⟨r, hr, h, hhd, fun z hz => hheq hz⟩

/-- **The local normal form at a zero.** A holomorphic function vanishing to finite order `n ≠ 0`
at `z₀` is, on a disc about `z₀`, the `n`-th power of an injective holomorphic function vanishing
at `z₀` with nonvanishing derivative there. -/
theorem exists_pow_eq_of_analyticOrderAt {A : ℂ → ℂ} {z₀ : ℂ} {n : ℕ} (hA : AnalyticAt ℂ A z₀)
    (hord : analyticOrderAt A z₀ = n) (hn : n ≠ 0) :
    ∃ r > 0, ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ (ball z₀ r) ∧ Set.InjOn φ (ball z₀ r) ∧
      φ z₀ = 0 ∧ deriv φ z₀ ≠ 0 ∧ ∀ z ∈ ball z₀ r, A z = φ z ^ n := by
  -- Factor out the zero: `A z = (z - z₀) ^ n • g z` near `z₀`, with `g z₀ ≠ 0`.
  obtain ⟨g, hg, hg0, hgeq⟩ := hA.analyticOrderAt_eq_natCast.mp hord
  obtain ⟨r₀, hr₀, hgball⟩ := Metric.eventually_nhds_iff.mp hgeq
  -- Take a holomorphic `n`-th root `h` of `g` near `z₀`, and put `φ z = (z - z₀) * h z`.
  obtain ⟨r₁, hr₁, h, hhd, hheq⟩ := exists_ball_pow_eq_of_ne_zero hg hg0 hn
  have hballnhds : ball z₀ r₁ ∈ 𝓝 z₀ := isOpen_ball.mem_nhds (mem_ball_self hr₁)
  have hh0 : h z₀ ≠ 0 := by
    intro hz
    have hroot := hheq z₀ (mem_ball_self hr₁)
    rw [hz, zero_pow hn] at hroot
    exact hg0 hroot.symm
  set φ : ℂ → ℂ := fun z => (z - z₀) * h z with hφdef
  have hφd : DifferentiableOn ℂ φ (ball z₀ r₁) := fun z hz =>
    ((differentiableAt_id.sub_const z₀).mul
      (hhd.differentiableAt (isOpen_ball.mem_nhds hz))).differentiableWithinAt
  -- `φ` vanishes at `z₀`, and its derivative there is `h z₀ ≠ 0`.
  have hφ₀ : φ z₀ = 0 := by simp [hφdef]
  have hφderiv : deriv φ z₀ = h z₀ := by
    have hd : HasDerivAt φ (1 * h z₀ + (z₀ - z₀) * deriv h z₀) z₀ :=
      ((hasDerivAt_id z₀).sub_const z₀).mul (hhd.differentiableAt hballnhds).hasDerivAt
    simpa using hd.deriv
  have hφne : deriv φ z₀ ≠ 0 := by rw [hφderiv]; exact hh0
  -- A nonvanishing derivative makes `φ` injective on some neighbourhood of `z₀`.
  obtain ⟨V, hV, hVinj⟩ :=
    (exists_injOn_nhds_iff_deriv_ne_zero (hφd.analyticAt hballnhds)).mpr hφne
  obtain ⟨r₂, hr₂, hr₂V⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨min r₀ (min r₁ r₂), lt_min hr₀ (lt_min hr₁ hr₂), φ,
    hφd.mono (ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _))), ?_, hφ₀, hφne,
    fun z hz => ?_⟩
  · exact hVinj.mono
      ((ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _))).trans hr₂V)
  · have hz₀ : dist z z₀ < r₀ :=
      mem_ball.mp (ball_subset_ball (min_le_left _ _) hz)
    have hz₁ : z ∈ ball z₀ r₁ :=
      ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hz
    calc A z = (z - z₀) ^ n • g z := hgball hz₀
      _ = φ z ^ n := by rw [smul_eq_mul, ← hheq z hz₁, hφdef, mul_pow]

/-- **The local normal form of a holomorphic map.** Near a point at which it is not locally
constant, a holomorphic map is the `n`-th power map read in a holomorphic coordinate: there is an
injective holomorphic `φ` on a disc about `z₀`, vanishing at `z₀` with `deriv φ z₀ ≠ 0`, with
`f z = f z₀ + φ z ^ n`, where `n` is the order of vanishing of `f - f z₀` at `z₀`.

This is the qualitative form of the open-mapping degree of `Conformal/LocalDegree.lean`, which
counts the preimages of the values near `f z₀`; here `n` is the same exponent
`analyticOrderNatAt (f · - f z₀) z₀` that the counting statements return. -/
theorem localNormalForm {f : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀)
    (hisol : ∀ᶠ z in 𝓝[≠] z₀, f z ≠ f z₀) :
    ∃ r > 0, ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ (ball z₀ r) ∧ Set.InjOn φ (ball z₀ r) ∧
      φ z₀ = 0 ∧ deriv φ z₀ ≠ 0 ∧
      ∀ z ∈ ball z₀ r, f z = f z₀ + φ z ^ analyticOrderNatAt (fun ζ => f ζ - f z₀) z₀ := by
  set A : ℂ → ℂ := fun ζ => f ζ - f z₀ with hAdef
  have hAan : AnalyticAt ℂ A z₀ := hf.sub analyticAt_const
  -- `f` is not locally constant, so the order of `A` at `z₀` is finite.
  have htop : analyticOrderAt A z₀ ≠ ⊤ := by
    intro htop
    have hfalse : ∀ᶠ z in 𝓝[≠] z₀, False := by
      filter_upwards [hisol, nhdsWithin_le_nhds (analyticOrderAt_eq_top.mp htop)] with z h1 h2
      exact h1 (sub_eq_zero.mp h2)
    obtain ⟨_, hz⟩ := hfalse.exists
    exact hz
  set n := analyticOrderNatAt A z₀
  have hord : analyticOrderAt A z₀ = (n : ℕ∞) := (Nat.cast_analyticOrderNatAt htop).symm
  -- `A` vanishes at `z₀`, so that order is not `0` either.
  have hn0 : n ≠ 0 := fun h0 => (analyticOrderAt_ne_zero.mpr ⟨hAan, by simp [hAdef]⟩)
    (by rw [hord, h0]; simp)
  obtain ⟨r, hr, φ, hφd, hφi, hφ₀, hφne, heq⟩ := exists_pow_eq_of_analyticOrderAt hAan hord hn0
  exact ⟨r, hr, φ, hφd, hφi, hφ₀, hφne, fun z hz => sub_eq_iff_eq_add'.mp (heq z hz)⟩

/-- **When a holomorphic germ has a holomorphic `n`-th root.** A germ vanishing to finite order `m`
at `z₀` is an `n`-th power near `z₀` exactly when `n` divides `m`.

The case `m = 0` — a germ that does not vanish — is Mathlib's `Complex.exists_continuousOn_pow_eq`
in its holomorphic form; the content here is the vanishing case, where a root exists only under the
divisibility condition that the normal form makes visible. -/
theorem exists_eventually_pow_eq_iff_dvd {A : ℂ → ℂ} {z₀ : ℂ} {m n : ℕ} (hA : AnalyticAt ℂ A z₀)
    (hord : analyticOrderAt A z₀ = m) (hn : n ≠ 0) :
    (∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ z₀ ∧ ∀ᶠ z in 𝓝 z₀, A z = ψ z ^ n) ↔ n ∣ m := by
  constructor
  · rintro ⟨ψ, hψ, hψeq⟩
    have hpi : A =ᶠ[𝓝 z₀] ψ ^ n := by
      filter_upwards [hψeq] with z hz
      simpa using hz
    have hm : analyticOrderNatAt A z₀ = m := by simp [analyticOrderNatAt, hord]
    have hmul : analyticOrderNatAt A z₀ = n * analyticOrderNatAt ψ z₀ := by
      simp only [analyticOrderNatAt, analyticOrderAt_congr hpi]
      simpa [smul_eq_mul] using congrArg ENat.toNat (analyticOrderAt_pow hψ n)
    exact ⟨analyticOrderNatAt ψ z₀, by rw [← hm, hmul]⟩
  · rintro ⟨k, rfl⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · -- order `0`: the germ does not vanish, and the zero-free branch supplies the root
      have h0 : A z₀ ≠ 0 := hA.analyticOrderAt_eq_zero.mp (by simpa using hord)
      obtain ⟨r, hr, h, hhd, hheq⟩ := exists_ball_pow_eq_of_ne_zero hA h0 hn
      refine ⟨h, hhd.analyticAt (isOpen_ball.mem_nhds (mem_ball_self hr)), ?_⟩
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with z hz
      exact (hheq z hz).symm
    · -- positive order: the `k`-th power of the chart of the normal form is the root
      have hnk : n * k ≠ 0 := Nat.mul_ne_zero hn hk.ne'
      obtain ⟨r, hr, φ, hφd, -, -, -, heq⟩ := exists_pow_eq_of_analyticOrderAt hA hord hnk
      have hballnhds : ball z₀ r ∈ 𝓝 z₀ := isOpen_ball.mem_nhds (mem_ball_self hr)
      refine ⟨fun z => φ z ^ k, (hφd.analyticAt hballnhds).pow k, ?_⟩
      filter_upwards [hballnhds] with z hz
      rw [heq z hz, mul_comm n k, pow_mul]

end TauCeti

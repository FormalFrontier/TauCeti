/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.Residue.Basic

/-!
# Canonical Laurent data of a meromorphic function

For `f` meromorphic at `s`, this file extracts its **canonical Laurent data**: the polar order
`meromorphicPolarOrderAt` — computed from `meromorphicOrderAt`, not chosen — together with Laurent
coefficients, the finite polar part, and the analytic part, satisfying
`f = analytic part + ∑ k, coeff k / (z - s)^(k+1)` near `s`. Because the tail length is the
computable canonical order, downstream facts about it are provable (it is `1` at a simple pole)
rather than opaque to a `Classical.choose` witness — which is what lets condition (A′) of the
generalized residue theorem be discharged at simple poles by flatness of order one.

## Main definitions

* `Contour.meromorphicPolarOrderAt f s` — the canonical polar order: the negative part of
  `meromorphicOrderAt f s` (`0` at an analytic-or-removable point).
* `Contour.meromorphicPolarCoeffAt hMero k` — the `k`-th Laurent coefficient at `s`.
* `Contour.meromorphicPolarPartAt hMero` — the finite polar part `∑ k, coeff k / (z - s)^(k+1)`.
* `Contour.meromorphicAnalyticPartAt hMero` — the analytic part at `s`.

## Main results

* `Contour.exists_laurent_data_of_meromorphicAt` — the Laurent decomposition with tail length
  pinned to the canonical order.
* `Contour.eventuallyEq_meromorphicAnalyticPartAt_add_meromorphicPolarPartAt` — `f` equals
  analytic part plus polar part near `s`.
* `Contour.meromorphicPolarPartAt_eq_sum` — the polar part as its explicit Laurent sum.
* `Contour.meromorphicPolarCoeffAt_zero_eq_residue` — the leading coefficient is the residue.
* `Contour.meromorphicPolarOrderAt_eq_one` — the canonical order at a simple pole is `1`.
* `Contour.laurent_coeff_unique`, `Contour.laurent_coeff_eq_meromorphicPolarCoeffAt` —
  uniqueness of finite principal-part expansions: any Laurent witness of `f` at `s` has the
  canonical coefficients, compared through zero-padding.

## Provenance

Migrated from the per-point Laurent-extraction block of
`HungerbuhlerWasem/LaurentExtraction.lean` in the AINTLIB `LeanModularForms` development
(`meroPolarOrderAt` through `meroPolarCoeffAt_zero_eq_residue`, here with `meromorphic` spelled
out); the residue identification is by `Contour.residue_of_laurent_expansion` against the
Taylor-coefficient residue. The coefficient-uniqueness block is new glue relative to the
source: AINTLIB transfers condition (B)'s Laurent data through a dedicated constructor
(`ofMeromorphicWithCondB`), while here uniqueness identifies **any** witness with the
canonical coefficients. See
N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
Theorem*, arXiv:1808.00997, §3.
-/

public section

noncomputable section

namespace TauCeti.Contour

open Filter Set Topology

/-- **The canonical polar order** of a meromorphic function at `s`: the negative part of
`meromorphicOrderAt f s`. For a pole of order `k` this is `k` (in particular `1` at a simple
pole, `meromorphicPolarOrderAt_eq_one`); at an analytic-or-removable point — including locally
vanishing `f` — it is `0`. Computed from `f` alone, so callers can evaluate it, unlike a
`Classical.choose`-extracted tail length. -/
def meromorphicPolarOrderAt (f : ℂ → ℂ) (s : ℂ) : ℕ :=
  (-(meromorphicOrderAt f s).untop₀).toNat

/-- The canonical polar order, computed from `meromorphicOrderAt`. -/
theorem meromorphicPolarOrderAt_eq_of_order_eq {f : ℂ → ℂ} {s : ℂ}
    {n : ℤ} (h : meromorphicOrderAt f s = n) :
    meromorphicPolarOrderAt f s = (-n).toNat := by
  rw [meromorphicPolarOrderAt, h, WithTop.untop₀_coe]

/-- **At a simple pole the canonical polar order is `1`.** With flatness of order one
(`IsPwC1ImmersionOn.flatOfOrder_one`), this discharges condition (A′) of the generalized residue
theorem at simple poles. -/
theorem meromorphicPolarOrderAt_eq_one {f : ℂ → ℂ} {s : ℂ}
    (h : meromorphicOrderAt f s = -1) :
    meromorphicPolarOrderAt f s = 1 := by
  rw [meromorphicPolarOrderAt_eq_of_order_eq h]
  rfl

/-- The canonical polar order bounds the meromorphic order from below:
`-(meromorphicPolarOrderAt f s) ≤ meromorphicOrderAt f s`. In particular, polar order `0` means
the meromorphic order is nonnegative. -/
theorem neg_meromorphicPolarOrderAt_le (f : ℂ → ℂ) (s : ℂ) :
    (-(meromorphicPolarOrderAt f s : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f s := by
  rcases eq_or_ne (meromorphicOrderAt f s) ⊤ with h | h
  · rw [h]; exact le_top
  · rw [← WithTop.coe_untop₀_of_ne_top h]
    rw [show (-(meromorphicPolarOrderAt f s : ℤ) : WithTop ℤ) =
        ((-(meromorphicPolarOrderAt f s : ℤ) : ℤ) : WithTop ℤ) by norm_cast,
      WithTop.coe_le_coe, meromorphicPolarOrderAt]
    omega

/-- **A positive canonical polar order pins the meromorphic order**:
`meromorphicOrderAt f s = -(meromorphicPolarOrderAt f s)` whenever the polar order is
positive. -/
theorem meromorphicOrderAt_eq_neg_of_meromorphicPolarOrderAt_pos {f : ℂ → ℂ} {s : ℂ}
    (h_pos : 0 < meromorphicPolarOrderAt f s) :
    meromorphicOrderAt f s = (-(meromorphicPolarOrderAt f s : ℤ) : WithTop ℤ) := by
  rcases eq_or_ne (meromorphicOrderAt f s) ⊤ with h | h
  · rw [meromorphicPolarOrderAt, h] at h_pos
    simp at h_pos
  · rw [← WithTop.coe_untop₀_of_ne_top h]
    rw [meromorphicPolarOrderAt] at h_pos ⊢
    norm_cast
    omega

/-- **A pole of order `> 1` in the canonical sense is a pole of order `> 1` for
`meromorphicOrderAt`** — the guard of condition (B)'s clauses. -/
theorem meromorphicOrderAt_lt_neg_one_of_one_lt_meromorphicPolarOrderAt {f : ℂ → ℂ} {s : ℂ}
    (h : 1 < meromorphicPolarOrderAt f s) :
    meromorphicOrderAt f s < (-1 : ℤ) := by
  rw [meromorphicOrderAt_eq_neg_of_meromorphicPolarOrderAt_pos (by omega)]
  exact_mod_cast WithTop.coe_lt_coe.mpr (by omega)

/-- Taylor decomposition of an analytic function to order `k`:
`g z = ∑ j < k, c j * (z - s)^j + (z - s)^k * R z` with `R` analytic at `s`. Mathlib's
`AnalyticAt.exists_eventuallyEq_sum_add_pow_mul` at the translate `g (· + s)`. -/
private theorem analyticAt_taylor_decomp {g : ℂ → ℂ} {s : ℂ}
    (hg : AnalyticAt ℂ g s) (k : ℕ) :
    ∃ (c : Fin k → ℂ) (R : ℂ → ℂ), AnalyticAt ℂ R s ∧
      ∀ᶠ z in 𝓝 s, g z = (∑ j : Fin k, c j * (z - s) ^ j.val) + (z - s) ^ k * R z := by
  have h1 : AnalyticAt ℂ (fun w : ℂ => w + s) 0 := analyticAt_id.add analyticAt_const
  have hg0 : AnalyticAt ℂ (fun w => g (w + s)) 0 := by
    have := AnalyticAt.comp (f := fun w : ℂ => w + s) (x := (0 : ℂ)) (by simpa using hg) h1
    exact this
  obtain ⟨F, hF_an, hF_eq⟩ := hg0.exists_eventuallyEq_sum_add_pow_mul k
  have h2 : AnalyticAt ℂ (fun z : ℂ => z - s) s := analyticAt_id.sub analyticAt_const
  have hF_comp : AnalyticAt ℂ (fun z => F (z - s)) s := by
    have := AnalyticAt.comp (f := fun z : ℂ => z - s) (x := s) (by simpa using hF_an) h2
    exact this
  refine ⟨fun j => iteratedDeriv j.val (fun w => g (w + s)) 0 / j.val.factorial,
    fun z => F (z - s), hF_comp, ?_⟩
  have h_tend : Filter.Tendsto (fun z : ℂ => z - s) (𝓝 s) (𝓝 0) := by
    simpa using (continuous_sub_right s).tendsto s
  filter_upwards [h_tend.eventually hF_eq] with z hz
  have hz' : g z = ∑ i ∈ Finset.range k,
      ((z - s) ^ i / (i.factorial : ℂ)) • iteratedDeriv i (fun w => g (w + s)) 0 +
        (z - s) ^ k • F (z - s) := by simpa using hz
  rw [hz', smul_eq_mul, mul_comm ((z - s) ^ k)]
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun j => iteratedDeriv j (fun w => g (w + s)) 0 /
    (j.factorial : ℂ) * (z - s) ^ j)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul]
  ring

private theorem pow_div_pow_neg {w : ℂ} (hw : w ≠ 0) {k j : ℕ} (hjk : j < k) :
    w ^ j * (w ^ k)⁻¹ = (w ^ (k - j))⁻¹ := by
  have h_exp : (k - j) + j = k := by omega
  rw [show (w ^ k)⁻¹ = (w ^ ((k - j) + j))⁻¹ by rw [h_exp], pow_add]
  field_simp

private theorem reindex_sum_fin_neg {k : ℕ} (c : Fin k → ℂ) (w : ℂ) :
    (∑ j : Fin k, c j / w ^ (k - j.val)) =
      ∑ i : Fin k,
        c ⟨k - 1 - i.val, by have := i.isLt; omega⟩ / w ^ (i.val + 1) := by
  let σ : Fin k → Fin k := fun j => ⟨k - 1 - j.val, by have := j.isLt; omega⟩
  have hσ_invol : Function.Involutive σ := fun j => by
    ext
    have := j.isLt
    simp only [σ]
    omega
  have h_sum_eq : (∑ i : Fin k, c (σ i) / w ^ (k - (σ i).val)) =
      ∑ j : Fin k, c j / w ^ (k - j.val) :=
    Equiv.sum_comp ⟨σ, σ, hσ_invol.leftInverse, hσ_invol.rightInverse⟩
      (fun j => c j / w ^ (k - j.val))
  rw [← h_sum_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  simp only [σ]
  omega

/-- Laurent data of length exactly `k` from a `(z - s)^(-k)`-factorisation with analytic
cofactor: Taylor-expand the cofactor to order `k` and divide. -/
private theorem laurent_data_of_zpow_factor {f g₀ : ℂ → ℂ} {s : ℂ} (k : ℕ)
    (hg₀_an : AnalyticAt ℂ g₀ s)
    (hg₀_eq : ∀ᶠ z in 𝓝[≠] s, f z = (z - s) ^ (-(k : ℤ)) • g₀ z) :
    ∃ (a : Fin k → ℂ) (g : ℂ → ℂ),
      AnalyticAt ℂ g s ∧
      ∀ᶠ z in 𝓝[≠] s, f z = g z + ∑ i : Fin k, a i / (z - s) ^ (i.val + 1) := by
  obtain ⟨c, R, hR_an, hR_eq⟩ := analyticAt_taylor_decomp hg₀_an k
  refine ⟨fun i : Fin k => c ⟨k - 1 - i.val, by have := i.isLt; omega⟩, R, hR_an, ?_⟩
  filter_upwards [hg₀_eq, nhdsWithin_le_nhds hR_eq, self_mem_nhdsWithin]
    with z hf_eq hR_eq_z hz_ne
  have hz_sub : (z - s) ≠ 0 := sub_ne_zero.mpr hz_ne
  rw [hf_eq, hR_eq_z, smul_eq_mul, zpow_neg, zpow_natCast, mul_add]
  have h1 : ((z - s) ^ k)⁻¹ * ((z - s) ^ k * R z) = R z := by field_simp
  rw [h1, add_comm]
  congr 1
  rw [Finset.mul_sum, show ∑ j : Fin k, ((z - s) ^ k)⁻¹ * (c j * (z - s) ^ j.val) =
      ∑ j : Fin k, c j / (z - s) ^ (k - j.val) from
    Finset.sum_congr rfl fun j _ => by
      rw [div_eq_mul_inv, show ((z - s) ^ k)⁻¹ * (c j * (z - s) ^ j.val) =
          c j * ((z - s) ^ j.val * ((z - s) ^ k)⁻¹) by ring,
        pow_div_pow_neg hz_sub j.isLt]]
  exact reindex_sum_fin_neg c (z - s)

/-- **Canonical Laurent data of a meromorphic function**: near `s`,
`f = g + ∑ k, a k / (z - s)^(k+1)` with `g` analytic at `s`, where the tail length is the
canonical polar order `meromorphicPolarOrderAt f s` — pinned, not existentially chosen, so it is
provable (`1` at a simple pole). -/
theorem exists_laurent_data_of_meromorphicAt {f : ℂ → ℂ} {s : ℂ} (hMero : MeromorphicAt f s) :
    ∃ (a : Fin (meromorphicPolarOrderAt f s) → ℂ) (g : ℂ → ℂ),
      AnalyticAt ℂ g s ∧
      ∀ᶠ z in 𝓝[≠] s,
        f z = g z + ∑ k : Fin (meromorphicPolarOrderAt f s), a k / (z - s) ^ (k.val + 1) := by
  obtain ⟨g₀, hg₀_an, hg₀_eq⟩ :=
    exists_analyticAt_eventuallyEq_zpow_smul hMero (neg_meromorphicPolarOrderAt_le f s)
  exact laurent_data_of_zpow_factor _ hg₀_an hg₀_eq

/-- The `k`-th canonical Laurent coefficient of `f` at `s`. -/
def meromorphicPolarCoeffAt {f : ℂ → ℂ} {s : ℂ} (hMero : MeromorphicAt f s)
    (k : Fin (meromorphicPolarOrderAt f s)) : ℂ :=
  (exists_laurent_data_of_meromorphicAt hMero).choose k

/-- The canonical finite polar part of `f` at `s`: the Laurent tail of length
`meromorphicPolarOrderAt f s`. -/
def meromorphicPolarPartAt {f : ℂ → ℂ} {s : ℂ} (hMero : MeromorphicAt f s) (z : ℂ) : ℂ :=
  ∑ k : Fin (meromorphicPolarOrderAt f s), meromorphicPolarCoeffAt hMero k / (z - s) ^ (k.val + 1)

/-- The canonical analytic part of `f` at `s`. -/
def meromorphicAnalyticPartAt {f : ℂ → ℂ} {s : ℂ} (hMero : MeromorphicAt f s) : ℂ → ℂ :=
  (exists_laurent_data_of_meromorphicAt hMero).choose_spec.choose

/-- The analytic part is analytic at `s`. -/
theorem meromorphicAnalyticPartAt_analyticAt {f : ℂ → ℂ} {s : ℂ}
    (hMero : MeromorphicAt f s) : AnalyticAt ℂ (meromorphicAnalyticPartAt hMero) s :=
  (exists_laurent_data_of_meromorphicAt hMero).choose_spec.choose_spec.1

/-- **The canonical Laurent decomposition**: near `s`, `f` is the analytic part plus the polar
part. -/
theorem eventuallyEq_meromorphicAnalyticPartAt_add_meromorphicPolarPartAt {f : ℂ → ℂ} {s : ℂ}
    (hMero : MeromorphicAt f s) :
    ∀ᶠ z in 𝓝[≠] s, f z = meromorphicAnalyticPartAt hMero z + meromorphicPolarPartAt hMero z :=
  (exists_laurent_data_of_meromorphicAt hMero).choose_spec.choose_spec.2

/-- The polar part as its explicit Laurent sum — the characteristic unfolding of
`meromorphicPolarPartAt`. -/
theorem meromorphicPolarPartAt_eq_sum {f : ℂ → ℂ} {s : ℂ}
    (hMero : MeromorphicAt f s) (z : ℂ) :
    meromorphicPolarPartAt hMero z =
      ∑ k : Fin (meromorphicPolarOrderAt f s),
        meromorphicPolarCoeffAt hMero k / (z - s) ^ (k.val + 1) := by
  unfold meromorphicPolarPartAt
  rfl

/-- The polar part is analytic away from its pole. -/
theorem meromorphicPolarPartAt_analyticAt_of_ne {f : ℂ → ℂ} {s : ℂ}
    (hMero : MeromorphicAt f s) {w : ℂ} (hw : w ≠ s) :
    AnalyticAt ℂ (meromorphicPolarPartAt hMero) w := by
  unfold meromorphicPolarPartAt
  refine Finset.analyticAt_fun_sum _ fun k _ => ?_
  exact analyticAt_const.div ((analyticAt_id.sub analyticAt_const).pow _)
    (pow_ne_zero _ (sub_ne_zero.mpr hw))

/-- **The leading canonical Laurent coefficient is the residue.** -/
theorem meromorphicPolarCoeffAt_zero_eq_residue {f : ℂ → ℂ} {s : ℂ}
    (hMero : MeromorphicAt f s) (h_pos : 0 < meromorphicPolarOrderAt f s) :
    meromorphicPolarCoeffAt hMero ⟨0, h_pos⟩ = residue f s := by
  have hres := residue_of_laurent_expansion
    (exists_laurent_data_of_meromorphicAt hMero).choose_spec.choose_spec.1
    (exists_laurent_data_of_meromorphicAt hMero).choose_spec.choose_spec.2
  rw [dif_pos h_pos] at hres
  exact hres.symm

/-! ### Uniqueness of the Laurent coefficients

Any finite principal-part expansion of `f` at `s` with analytic remainder has the canonical
coefficients: the sector condition (B) of the generalized residue theorem carries its own
Laurent witness, and uniqueness is what lets its resonance constraints transfer to the
canonical polar data. Internally the coefficients are total functions `ℕ → ℂ` summed over
`Finset.range`, so expansions of different lengths compare after zero-padding. -/

/-- The top coefficient of a finite principal part that agrees with a function continuous at
`s` vanishes. -/
private theorem coeff_top_eq_zero_of_eventuallyEq {s : ℂ} {N : ℕ} {c : ℕ → ℂ}
    {g : ℂ → ℂ} (hg : ContinuousAt g s)
    (h_eq : ∀ᶠ z in 𝓝[≠] s,
      ∑ k ∈ Finset.range (N + 1), c k / (z - s) ^ (k + 1) = g z) :
    c N = 0 := by
  have h_mul : ∀ᶠ z in 𝓝[≠] s,
      ∑ k ∈ Finset.range (N + 1), c k * (z - s) ^ (N - k) = g z * (z - s) ^ (N + 1) := by
    filter_upwards [h_eq, self_mem_nhdsWithin] with z hz hz_ne
    have hw : z - s ≠ 0 := sub_ne_zero.mpr hz_ne
    rw [← hz, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkN : k + 1 ≤ N + 1 := Finset.mem_range.mp hk
    have h_sub : N + 1 - (k + 1) = N - k := by omega
    rw [div_mul_eq_mul_div, mul_div_assoc, div_eq_mul_inv ((z - s) ^ (N + 1)),
      ← pow_sub₀ (z - s) hw hkN, h_sub]
  have h_lhs : Tendsto (fun z => ∑ k ∈ Finset.range (N + 1), c k * (z - s) ^ (N - k))
      (𝓝[≠] s) (𝓝 (c N)) := by
    have h_cont : Tendsto (fun z => ∑ k ∈ Finset.range (N + 1), c k * (z - s) ^ (N - k))
        (𝓝 s) (𝓝 (∑ k ∈ Finset.range (N + 1), c k * ((s : ℂ) - s) ^ (N - k))) :=
      (continuous_finsetSum _ fun k _ =>
        continuous_const.mul ((continuous_id.sub continuous_const).pow _)).tendsto s
    have h_eval : ∑ k ∈ Finset.range (N + 1), c k * ((s : ℂ) - s) ^ (N - k) = c N := by
      rw [sub_self, Finset.sum_eq_single N
        (fun k hk hne => by
          rw [zero_pow (by
            have := Finset.mem_range.mp hk
            omega : N - k ≠ 0), mul_zero])
        (fun h => absurd (Finset.self_mem_range_succ N) h),
        Nat.sub_self, pow_zero, mul_one]
    exact h_eval ▸ h_cont.mono_left nhdsWithin_le_nhds
  have h_rhs : Tendsto (fun z => g z * (z - s) ^ (N + 1)) (𝓝[≠] s) (𝓝 0) := by
    have h_sub : Tendsto (fun z : ℂ => z - s) (𝓝 s) (𝓝 0) := by
      simpa using (continuous_sub_right s).tendsto s
    have h_pow : Tendsto (fun z : ℂ => (z - s) ^ (N + 1)) (𝓝 s) (𝓝 0) := by
      simpa [zero_pow (Nat.succ_ne_zero N)] using h_sub.pow (N + 1)
    have h0 := (hg.tendsto.mul h_pow).mono_left
      (nhdsWithin_le_nhds (s := {s}ᶜ))
    simpa using h0
  exact tendsto_nhds_unique (h_lhs.congr' h_mul) h_rhs

/-- A finite principal part agreeing with a function continuous at `s` is zero: all its
coefficients vanish. -/
private theorem laurent_coeff_eq_zero_of_eventuallyEq {s : ℂ} {g : ℂ → ℂ}
    (hg : ContinuousAt g s) :
    ∀ {N : ℕ} {c : ℕ → ℂ},
      (∀ᶠ z in 𝓝[≠] s, ∑ k ∈ Finset.range N, c k / (z - s) ^ (k + 1) = g z) →
      ∀ k < N, c k = 0 := by
  intro N
  induction N with
  | zero => exact fun _ k hk => absurd hk (Nat.not_lt_zero k)
  | succ N IH =>
    intro c h_eq k hk
    have h_top : c N = 0 := coeff_top_eq_zero_of_eventuallyEq hg h_eq
    have h_eq' : ∀ᶠ z in 𝓝[≠] s,
        ∑ k ∈ Finset.range N, c k / (z - s) ^ (k + 1) = g z := by
      filter_upwards [h_eq] with z hz
      rwa [Finset.sum_range_succ, h_top, zero_div, add_zero] at hz
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | rfl
    · exact IH h_eq' k hk'
    · exact h_top

/-- A `Fin`-indexed principal-part sum as a `Finset.range` sum of its zero-padding, extended
to any length `L ≥ N`. -/
private theorem sum_fin_div_pow_eq_sum_range {s : ℂ} {N L : ℕ} (hNL : N ≤ L)
    (a : Fin N → ℂ) (z : ℂ) :
    ∑ k : Fin N, a k / (z - s) ^ (k.val + 1)
      = ∑ k ∈ Finset.range L,
        (if hk : k < N then a ⟨k, hk⟩ else 0) / (z - s) ^ (k + 1) := by
  have h₁ : ∑ k : Fin N, a k / (z - s) ^ (k.val + 1)
      = ∑ k ∈ Finset.range N,
        (if hk : k < N then a ⟨k, hk⟩ else 0) / (z - s) ^ (k + 1) := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun k _ => by rw [dif_pos k.isLt]
  rw [h₁]
  exact Finset.sum_subset
    (fun x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hNL))
    fun k _ hk => by
    rw [dif_neg (Finset.mem_range.not.mp hk), zero_div]

/-- **Uniqueness of finite principal-part expansions**: two expansions of the same function
near `s` with remainders continuous at `s` have the same coefficients, compared through
their zero-paddings. -/
theorem laurent_coeff_unique {s : ℂ} {N M : ℕ} {a : Fin N → ℂ} {b : Fin M → ℂ}
    {g h : ℂ → ℂ} (hg : ContinuousAt g s) (hh : ContinuousAt h s)
    (h_eq : ∀ᶠ z in 𝓝[≠] s,
      g z + ∑ k : Fin N, a k / (z - s) ^ (k.val + 1)
        = h z + ∑ k : Fin M, b k / (z - s) ^ (k.val + 1)) (k : ℕ) :
    (if hk : k < N then a ⟨k, hk⟩ else 0) = (if hk : k < M then b ⟨k, hk⟩ else 0) := by
  rcases lt_or_ge k (max N M) with hk_lt | hk_ge
  · have h_diff : ∀ᶠ z in 𝓝[≠] s,
        ∑ j ∈ Finset.range (max N M),
          ((if hj : j < N then a ⟨j, hj⟩ else 0) - (if hj : j < M then b ⟨j, hj⟩ else 0))
            / (z - s) ^ (j + 1)
          = h z - g z := by
      filter_upwards [h_eq] with z hz
      rw [sum_fin_div_pow_eq_sum_range (le_max_left N M) a z,
        sum_fin_div_pow_eq_sum_range (le_max_right N M) b z] at hz
      rw [Finset.sum_congr rfl fun j _ =>
        sub_div (if hj : j < N then a ⟨j, hj⟩ else 0)
          (if hj : j < M then b ⟨j, hj⟩ else 0) ((z - s) ^ (j + 1)),
        Finset.sum_sub_distrib]
      linear_combination hz
    exact sub_eq_zero.mp
      (laurent_coeff_eq_zero_of_eventuallyEq (hh.sub hg) h_diff k hk_lt)
  · rw [dif_neg (by omega : ¬ k < N), dif_neg (by omega : ¬ k < M)]

/-- **Any Laurent witness has the canonical coefficients**: an eventual finite principal-part
expansion of a meromorphic `f` at `s` with remainder continuous at `s` agrees, coefficient by
coefficient through zero-padding, with the canonical polar data. This is what transfers the
sector condition (B)'s resonance constraints from its own Laurent witness to
`meromorphicPolarCoeffAt`. -/
theorem laurent_coeff_eq_meromorphicPolarCoeffAt {f : ℂ → ℂ} {s : ℂ}
    (hMero : MeromorphicAt f s) {N : ℕ} {a : Fin N → ℂ} {g : ℂ → ℂ}
    (hg : ContinuousAt g s)
    (h_eq : ∀ᶠ z in 𝓝[≠] s, f z = g z + ∑ k : Fin N, a k / (z - s) ^ (k.val + 1)) (k : ℕ) :
    (if hk : k < N then a ⟨k, hk⟩ else 0)
      = (if hk : k < meromorphicPolarOrderAt f s then
          meromorphicPolarCoeffAt hMero ⟨k, hk⟩ else 0) := by
  refine laurent_coeff_unique hg
    (meromorphicAnalyticPartAt_analyticAt hMero).continuousAt ?_ k
  filter_upwards [h_eq, eventuallyEq_meromorphicAnalyticPartAt_add_meromorphicPolarPartAt
    hMero] with z hz hz'
  rw [← hz, hz', meromorphicPolarPartAt_eq_sum]

end TauCeti.Contour

end

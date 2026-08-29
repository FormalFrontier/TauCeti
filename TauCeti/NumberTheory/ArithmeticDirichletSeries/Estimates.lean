/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Convergence
public import Mathlib.NumberTheory.LSeries.SumCoeff
public import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Trivial

/-!
# Linear ideal counts and the exact abscissa of the trivial ideal weight

Mathlib's `NumberField.Ideal.tendsto_norm_le_div_atTop₀` says that the number of nonzero integral
ideals of `𝓞 K` of absolute norm at most `x` is asymptotic to `ρ x`, with `ρ` the positive residue
of the Dedekind zeta function.  This file turns that single asymptotic into the *two-sided* linear
bounds that every later estimate of the roadmap counts against, and then spends them on the exact
abscissa of absolute convergence of the trivial ideal weight.

Both directions are needed.  Convergence uses the upper bound alone: it makes the partial sums of
the norm coefficients `O(n)`, so Mathlib's `LSeriesSummable_of_sum_norm_bigO` gives absolute
convergence on `Re s > 1`.  Divergence at `s = 1` uses both bounds together, to estimate the mass
of a block `N < n ≤ m N` of fixed ratio `m` as a difference of endpoint counts: the lower bound at
the right endpoint `m N` and the upper bound at the left endpoint `N` leave the block at least
`lower * m N - upper * N` of coefficient mass, so the terms `‖a n‖ / n` add up to at least
`lower - upper / m`, which is at least `lower / 2` once `m ≥ 2 * upper / lower`, while the blocks
of a convergent series of nonnegative terms must become arbitrarily small.

## Main definitions

* `TauCeti.IdealCountingLinearBounds K` packages positive constants `lower` and `upper` with the
  two-sided bound `lower * x ≤ #{I ≠ 0 | N(I) ≤ x} ≤ upper * x`, valid from cutoff `1` on.

## Main results

* `TauCeti.idealCount_linearBounds`: such a package exists for every number field.
* `TauCeti.abscissaOfAbsConv_normCoeff_one`: the abscissa of absolute convergence of the trivial
  ideal weight is exactly `1`; `TauCeti.LSeriesSummable_normCoeff_one_iff` is the sharp
  convergence criterion.
* `TauCeti.abscissaOfAbsConv_dedekindZetaCoeff` and `TauCeti.LSeriesSummable_dedekindZetaCoeff_iff`
  are the same two statements for `TauCeti.dedekindZetaCoeff`, the coefficient system Mathlib's
  `NumberField.dedekindZeta` is the `LSeries` of.  That system counts *all* integral ideals, so it
  differs from the trivial norm coefficients at `n = 0` and the two statements are related only
  through the `n ≠ 0` congruence `LSeries.abscissaOfAbsConv_congr`.

## Implementation notes

The counting function is Mathlib's own
`Nat.card {I : (Ideal (𝓞 K))⁰ // (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x}`, written out rather
than abbreviated, so that the bounds apply to `NumberField.Ideal.tendsto_norm_le_div_atTop₀`
without a translation lemma.  The inclusive real cutoff is the one fixed by the conventions table
of the roadmap.

`TauCeti.NumberTheory.EffectiveBounds.IdealCount` proves the *effective* bound
`#{I ≠ 0 | N(I) ≤ x} ≤ x² 2^[K:ℚ]`, with an explicit constant but the wrong exponent; it cannot
prove convergence at `Re s > 1`, and it has no lower bound at all.

## Roadmap role

This is Layer **5.1** (the ideal-count half) together with Layer **5.1a** of
`TauCetiRoadmap/ArithmeticDirichletSeries/README.md`.  As that layer demands, the exact abscissa
is derived from the two-sided linear ideal counts alone: neither the analytic continuation of the
Dedekind zeta function nor its pole at `s = 1` is used.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapters II--III.
-/

public section

namespace TauCeti

open Filter
open scoped nonZeroDivisors NumberField Topology

variable (K : Type*) [Field K] [NumberField K]

/-! ### Finiteness and monotonicity of the ideal count -/

/-- The nonzero integral ideals of absolute norm at most a real cutoff form a finite set. -/
theorem finite_setOf_absNorm_real_le (x : ℝ) :
    {I : (Ideal (𝓞 K))⁰ | (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x}.Finite :=
  (Ideal.finite_setOfPred_absNorm_le₀ ⌊x⌋₊).subset fun _ hI ↦ Nat.le_floor hI

/-- The number of nonzero integral ideals of bounded absolute norm is monotone in the cutoff. -/
theorem card_absNorm_real_le_mono {x y : ℝ} (h : x ≤ y) :
    Nat.card {I : (Ideal (𝓞 K))⁰ // (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x} ≤
      Nat.card {I : (Ideal (𝓞 K))⁰ // (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ y} := by
  have : Finite {I : (Ideal (𝓞 K))⁰ // (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ y} :=
    (finite_setOf_absNorm_real_le K y).to_subtype
  refine Nat.card_le_card_of_injective (fun I ↦ ⟨I.1, I.2.trans h⟩) fun a b hab ↦ ?_
  injection hab with hab'
  exact Subtype.ext hab'

/-- From cutoff `1` on there is at least one nonzero integral ideal of bounded absolute norm,
namely the unit ideal. -/
theorem one_le_card_absNorm_real_le {x : ℝ} (hx : 1 ≤ x) :
    1 ≤ Nat.card {I : (Ideal (𝓞 K))⁰ // (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x} := by
  have hfin : Finite {I : (Ideal (𝓞 K))⁰ // (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x} :=
    (finite_setOf_absNorm_real_le K x).to_subtype
  have hne : Nonempty {I : (Ideal (𝓞 K))⁰ // (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x} :=
    ⟨⟨1, by simpa using hx⟩⟩
  exact Nat.one_le_iff_ne_zero.mpr (Nat.card_ne_zero.mpr ⟨hne, hfin⟩)

/-! ### Two-sided linear bounds -/

/-- **Two-sided positive linear bounds for the ideal-counting function** of a number field `K`:
constants `lower` and `upper`, both positive, with
`lower * x ≤ #{I ≠ 0 | N(I) ≤ x} ≤ upper * x` for every cutoff `x ≥ 1`.

Only the existence of such a package matters; `TauCeti.idealCount_linearBounds` provides it from
Mathlib's asymptotic `NumberField.Ideal.tendsto_norm_le_div_atTop₀`. Both inequalities are used:
the upper one alone gives absolute convergence to the right of `1`, and the two together give
divergence at `1`. -/
structure IdealCountingLinearBounds where
  /-- The constant in the lower bound. -/
  lower : ℝ
  /-- The constant in the upper bound. -/
  upper : ℝ
  /-- The constant in the lower bound is positive. -/
  lower_pos : 0 < lower
  /-- The constant in the upper bound is positive. -/
  upper_pos : 0 < upper
  /-- The lower bound, valid from cutoff `1` on. -/
  le_card (x : ℝ) (hx : 1 ≤ x) :
    lower * x ≤ Nat.card {I : (Ideal (𝓞 K))⁰ // (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x}
  /-- The upper bound, valid from cutoff `1` on. -/
  card_le (x : ℝ) (hx : 1 ≤ x) :
    (Nat.card {I : (Ideal (𝓞 K))⁰ // (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x} : ℝ) ≤ upper * x

/-- **Two-sided linear ideal counts.** The number of nonzero integral ideals of absolute norm at
most `x` is bounded above and below by positive multiples of `x`, for every cutoff `x ≥ 1`.

Both constants come from Mathlib's asymptotic `NumberField.Ideal.tendsto_norm_le_div_atTop₀`,
whose limit is positive by `NumberField.dedekindZeta_residue_pos`; below the threshold produced by
that limit the bounds are secured by the unit ideal and by monotonicity of the count. -/
theorem idealCount_linearBounds : Nonempty (IdealCountingLinearBounds K) := by
  set r : ℝ := NumberField.dedekindZeta_residue K with hr
  have hpos : 0 < r := NumberField.dedekindZeta_residue_pos K
  have htend : Tendsto (fun x : ℝ ↦
      (Nat.card {I : (Ideal (𝓞 K))⁰ // (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x} : ℝ) / x)
      atTop (𝓝 r) := by
    rw [hr, NumberField.dedekindZeta_residue_def]
    exact NumberField.Ideal.tendsto_norm_le_div_atTop₀ K
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp
    (((htend.eventually_const_lt (by linarith : r / 2 < r)).and
      (htend.eventually_lt_const (by linarith : r < r + 1))).and (eventually_ge_atTop (1 : ℝ)))
  set X : ℝ := max X₀ 1
  have hX1 : 1 ≤ X := le_max_right _ _
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX1
  set M : ℝ :=
    (Nat.card {I : (Ideal (𝓞 K))⁰ // (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ X} : ℝ) with hM
  have hmain : ∀ x : ℝ, X ≤ x →
      r / 2 * x ≤ Nat.card {I : (Ideal (𝓞 K))⁰ // (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x} ∧
      (Nat.card {I : (Ideal (𝓞 K))⁰ // (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x} : ℝ) ≤
        (r + 1) * x := by
    intro x hx
    obtain ⟨⟨h₁, h₂⟩, h₃⟩ := hX₀ x ((le_max_left X₀ 1).trans hx)
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one h₃
    exact ⟨(le_div_iff₀ hxpos).mp h₁.le, (div_le_iff₀ hxpos).mp h₂.le⟩
  have hupos : (0 : ℝ) < max (r + 1) M := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  refine ⟨{
    lower := min (r / 2) X⁻¹
    upper := max (r + 1) M
    lower_pos := lt_min (by linarith) (inv_pos.mpr hXpos)
    upper_pos := hupos
    le_card := ?_
    card_le := ?_ }⟩
  · intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
    rcases le_or_gt X x with hxX | hxX
    · exact le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hxpos.le) (hmain x hxX).1
    · refine le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hxpos.le) ?_
      have h1 : X⁻¹ * x ≤ 1 :=
        calc X⁻¹ * x ≤ X⁻¹ * X := mul_le_mul_of_nonneg_left hxX.le (inv_nonneg.mpr hXpos.le)
          _ = 1 := inv_mul_cancel₀ hXpos.ne'
      exact le_trans h1 (by exact_mod_cast one_le_card_absNorm_real_le K hx)
  · intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
    rcases le_or_gt X x with hxX | hxX
    · exact le_trans (hmain x hxX).2 (mul_le_mul_of_nonneg_right (le_max_left _ _) hxpos.le)
    · have h1 : (Nat.card {I : (Ideal (𝓞 K))⁰ // (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ x} : ℝ)
          ≤ M := by rw [hM]; exact_mod_cast card_absNorm_real_le_mono K hxX.le
      exact h1.trans ((le_max_right _ _).trans (le_mul_of_one_le_right hupos.le hx))

/-! ### Partial sums of the trivial norm coefficients -/

/-- The trivial ideal weight has norm coefficient the number of nonzero integral ideals of the
given absolute norm, so its absolute value is that count. -/
theorem norm_normCoeff_one (n : ℕ) :
    ‖normCoeff K (1 : IdealArithmeticFunction K) n‖ = (normFiber K n).card := by
  rw [normCoeff_eq_sum_normFiber]
  simp

/-- **The partial sums of the trivial norm coefficients are the ideal counts.** Summing the norm
coefficients of the trivial ideal weight over `1 ≤ k ≤ n` counts the nonzero integral ideals of
absolute norm at most `n`, because the absolute-norm fibres partition them. -/
theorem sum_norm_normCoeff_one (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, ‖normCoeff K (1 : IdealArithmeticFunction K) k‖
      = Nat.card {I : (Ideal (𝓞 K))⁰ // (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ (n : ℝ)} := by
  classical
  have hfin := finite_setOf_absNorm_real_le K (n : ℝ)
  have key : hfin.toFinset.card = ∑ k ∈ Finset.Icc 1 n, (normFiber K k).card := by
    refine Finset.card_eq_sum_card_fiberwise
      (f := fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K)))
      (t := Finset.Icc 1 n) (fun I hI ↦ ?_) |>.trans (Finset.sum_congr rfl fun k hk ↦ ?_)
    · rw [Finset.mem_coe, Finset.mem_Icc]
      refine ⟨Ideal.absNorm_pos_of_nonZeroDivisors I, ?_⟩
      rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hI
      exact_mod_cast hI
    · congr 1
      ext I
      rw [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, mem_normFiber]
      refine ⟨fun h ↦ h.2, fun h ↦ ⟨?_, h⟩⟩
      rw [h]
      exact_mod_cast (Finset.mem_Icc.mp hk).2
  have hcard : Nat.card {I : (Ideal (𝓞 K))⁰ // (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ (n : ℝ)}
      = hfin.toFinset.card := Nat.card_eq_card_finite_toFinset hfin
  rw [hcard, key, Nat.cast_sum]
  exact Finset.sum_congr rfl fun k _ ↦ norm_normCoeff_one K k

/-! ### The exact abscissa of the trivial ideal weight -/

/-- The upper linear ideal count makes the partial sums of the trivial norm coefficients `O(n)`. -/
theorem isBigO_sum_norm_normCoeff_one :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, ‖normCoeff K (1 : IdealArithmeticFunction K) k‖)
      =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ) := by
  obtain ⟨b⟩ := idealCount_linearBounds K
  refine Asymptotics.IsBigO.of_bound b.upper ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [sum_norm_normCoeff_one, Real.rpow_one, Real.norm_natCast, Real.norm_natCast]
  exact b.card_le n h1

/-- The Dirichlet series of the trivial ideal weight converges absolutely on `Re s > 1`. -/
theorem abscissaOfAbsConv_normCoeff_one_le :
    LSeries.abscissaOfAbsConv (normCoeff K (1 : IdealArithmeticFunction K)) ≤ 1 := by
  refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1) fun y hy ↦ ?_
  exact LSeriesSummable_of_sum_norm_bigO (isBigO_sum_norm_normCoeff_one K) zero_le_one
    (by simpa using hy)

/-- The partial sums of the trivial norm coefficients over a half-open initial interval. -/
private theorem sum_Ioc_norm_normCoeff_one (n : ℕ) :
    ∑ k ∈ Finset.Ioc 0 n, ‖normCoeff K (1 : IdealArithmeticFunction K) k‖
      = Nat.card {I : (Ideal (𝓞 K))⁰ // (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ (n : ℝ)} := by
  -- Normalize the order-theoretic successor in the interval rewrite to the natural numeral `1`.
  have hinterval : Finset.Icc 1 n = Finset.Ioc 0 n := by
    simpa only [Nat.succ_eq_succ] using Finset.Icc_succ_left_eq_Ioc 0 n
  rw [← sum_norm_normCoeff_one, hinterval]

/-- The difference of the endpoint ideal-count bounds controls the coefficient mass in a block. -/
private theorem lower_mul_sub_upper_mul_le_sum_Ioc_norm_normCoeff_one
    (b : IdealCountingLinearBounds K) {m N : ℕ} (hm : 1 ≤ m) (hN : 1 ≤ N) :
    b.lower * ((m * N : ℕ) : ℝ) - b.upper * (N : ℝ) ≤
      ∑ k ∈ Finset.Ioc N (m * N), ‖normCoeff K (1 : IdealArithmeticFunction K) k‖ := by
  have hNM : N ≤ m * N := Nat.le_mul_of_pos_left N (lt_of_lt_of_le zero_lt_one hm)
  have hsplit : (∑ k ∈ Finset.Ioc 0 N, ‖normCoeff K (1 : IdealArithmeticFunction K) k‖)
      + ∑ k ∈ Finset.Ioc N (m * N), ‖normCoeff K (1 : IdealArithmeticFunction K) k‖
      = ∑ k ∈ Finset.Ioc 0 (m * N), ‖normCoeff K (1 : IdealArithmeticFunction K) k‖ :=
    Finset.sum_Ioc_consecutive _ (Nat.zero_le N) hNM
  have hlow : b.lower * ((m * N : ℕ) : ℝ)
      ≤ ∑ k ∈ Finset.Ioc 0 (m * N), ‖normCoeff K (1 : IdealArithmeticFunction K) k‖ := by
    rw [sum_Ioc_norm_normCoeff_one]
    exact b.le_card _ (by exact_mod_cast Nat.lt_of_lt_of_le hN hNM)
  have hup : (∑ k ∈ Finset.Ioc 0 N, ‖normCoeff K (1 : IdealArithmeticFunction K) k‖)
      ≤ b.upper * (N : ℝ) := by
    rw [sum_Ioc_norm_normCoeff_one]
    exact b.card_le _ (by exact_mod_cast hN)
  linarith

/-- Dividing all coefficients in a positive block by its right endpoint underestimates the
corresponding Dirichlet-series terms at `s = 1`. -/
private theorem sum_Ioc_norm_normCoeff_one_div_le_sum_Ioc_norm_term {m N : ℕ} (hN : 1 ≤ N) :
    (∑ k ∈ Finset.Ioc N (m * N), ‖normCoeff K (1 : IdealArithmeticFunction K) k‖) /
        ((m * N : ℕ) : ℝ) ≤
      ∑ k ∈ Finset.Ioc N (m * N),
        ‖LSeries.term (normCoeff K (1 : IdealArithmeticFunction K)) 1 k‖ := by
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun k hk ↦ ?_
  obtain ⟨hk1, hk2⟩ := Finset.mem_Ioc.mp hk
  have hk0 : k ≠ 0 := by omega
  have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk0
  rw [LSeries.norm_term_eq]
  simp only [Complex.one_re, ite_eq_right hk0, Real.rpow_one]
  refine div_le_div_of_nonneg_left (norm_nonneg _) hkpos ?_
  exact_mod_cast hk2

/-- **The fixed-ratio block lower bound.** Once the block ratio `m` is at least
`2 * upper / lower`, the terms of the Dirichlet series of the trivial ideal weight at `s = 1` over
a block `N < k ≤ m N` add up to at least `lower / 2`, uniformly in `N ≥ 1`.

Both linear ideal counts enter, as a difference of endpoint counts: the lower bound at the right
endpoint `m N` and the upper bound at the left endpoint `N` leave the block at least
`lower * m N - upper * N` of coefficient mass, and every term of the block is divided by at most
`m N`. -/
private theorem lower_div_two_le_sum_Ioc_norm_term (b : IdealCountingLinearBounds K) {m N : ℕ}
    (hm : 2 * b.upper / b.lower ≤ (m : ℝ)) (hN : 1 ≤ N) :
    b.lower / 2 ≤ ∑ k ∈ Finset.Ioc N (m * N),
      ‖LSeries.term (normCoeff K (1 : IdealArithmeticFunction K)) 1 k‖ := by
  have hmpos : (0 : ℝ) < m :=
    lt_of_lt_of_le (div_pos (by linarith [b.upper_pos]) b.lower_pos) hm
  have hm1 : 1 ≤ m := by exact_mod_cast hmpos
  have hupperm : b.upper / m ≤ b.lower / 2 := by
    rw [div_le_div_iff₀ hmpos two_pos]
    have := (div_le_iff₀ b.lower_pos).mp hm
    linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hMpos : (0 : ℝ) < (m * N : ℕ) := by positivity
  refine le_trans ?_ (sum_Ioc_norm_normCoeff_one_div_le_sum_Ioc_norm_term K hN)
  rw [le_div_iff₀ hMpos]
  have hcast : ((m * N : ℕ) : ℝ) = (m : ℝ) * (N : ℝ) := by push_cast; ring
  have hkey : b.lower / 2 * ((m : ℝ) * N) ≤ b.lower * ((m : ℝ) * N) - b.upper * N := by
    have h2 : b.upper * (N : ℝ) ≤ b.lower / 2 * ((m : ℝ) * N) := by
      have := mul_le_mul_of_nonneg_right hupperm (le_of_lt hNpos)
      rw [div_mul_eq_mul_div, div_le_iff₀ hmpos] at this
      nlinarith
    nlinarith [b.lower_pos]
  calc b.lower / 2 * ((m * N : ℕ) : ℝ) = b.lower / 2 * ((m : ℝ) * N) := by rw [hcast]
    _ ≤ b.lower * ((m : ℝ) * N) - b.upper * N := hkey
    _ = b.lower * ((m * N : ℕ) : ℝ) - b.upper * N := by rw [hcast]
    _ ≤ ∑ k ∈ Finset.Ioc N (m * N), ‖normCoeff K (1 : IdealArithmeticFunction K) k‖ :=
      lower_mul_sub_upper_mul_le_sum_Ioc_norm_normCoeff_one K b hm1 hN

/-- **Divergence at `s = 1`.** The Dirichlet series of the trivial ideal weight does not converge
at `s = 1`.

The two-sided linear ideal counts are what force this: by
`TauCeti.lower_div_two_le_sum_Ioc_norm_term` every block `N < n ≤ m N` of fixed ratio
`m ≥ 2 * upper / lower` carries mass at least `lower / 2`, whereas the blocks of a convergent
series of nonnegative terms become arbitrarily small. -/
theorem not_LSeriesSummable_normCoeff_one :
    ¬ LSeriesSummable (normCoeff K (1 : IdealArithmeticFunction K)) 1 := by
  intro hsum
  obtain ⟨b⟩ := idealCount_linearBounds K
  set g : ℕ → ℝ := fun n ↦ ‖LSeries.term (normCoeff K (1 : IdealArithmeticFunction K)) 1 n‖
    with hgdef
  have hgsum : Summable g := summable_norm_iff.mpr hsum
  have hgnn : ∀ n, 0 ≤ g n := fun n ↦ norm_nonneg _
  set m : ℕ := ⌈2 * b.upper / b.lower⌉₊ + 1 with hmdef
  have hm1 : 1 ≤ m := Nat.le_add_left 1 _
  have hmR : 2 * b.upper / b.lower ≤ (m : ℝ) := by
    rw [hmdef]
    push_cast
    linarith [Nat.le_ceil (2 * b.upper / b.lower)]
  -- the blocks of a convergent series of nonnegative terms are eventually small
  have hpartial : Tendsto (fun N : ℕ ↦ ∑ k ∈ Finset.Ioc 0 N, g k) atTop (𝓝 (∑' k, g k)) := by
    refine (hgsum.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).congr fun N ↦ ?_
    simp only [Function.comp_apply]
    refine (Finset.sum_subset ?_ ?_).symm
    · intro k hk
      rw [Finset.mem_range]
      exact Nat.lt_succ_of_le (Finset.mem_Ioc.mp hk).2
    · intro k hk hknot
      have hk0 : k = 0 := by
        rcases Nat.eq_zero_or_pos k with h | h
        · exact h
        · exact absurd (Finset.mem_Ioc.mpr ⟨h, Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)⟩) hknot
      rw [hk0, hgdef]
      simp
  have htail : Tendsto (fun N : ℕ ↦ (∑' k, g k) - ∑ k ∈ Finset.Ioc 0 N, g k) atTop (𝓝 0) := by
    simpa using hpartial.const_sub (∑' k, g k)
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((htail.eventually_lt_const (by linarith [b.lower_pos] : (0 : ℝ) < b.lower / 2)).and
      (eventually_ge_atTop 1))
  obtain ⟨h1, h2⟩ := hN N le_rfl
  have hNM : N ≤ m * N := Nat.le_mul_of_pos_left N (lt_of_lt_of_le zero_lt_one hm1)
  have hle : ∑ k ∈ Finset.Ioc N (m * N), g k ≤ (∑' k, g k) - ∑ k ∈ Finset.Ioc 0 N, g k := by
    have hsplit : (∑ k ∈ Finset.Ioc 0 N, g k) + ∑ k ∈ Finset.Ioc N (m * N), g k
        = ∑ k ∈ Finset.Ioc 0 (m * N), g k :=
      Finset.sum_Ioc_consecutive _ (Nat.zero_le N) hNM
    have hbound : ∑ k ∈ Finset.Ioc 0 (m * N), g k ≤ ∑' k, g k :=
      hgsum.sum_le_tsum _ (fun k _ ↦ hgnn k)
    linarith
  linarith [lower_div_two_le_sum_Ioc_norm_term K b hmR h2]

/-! ### The exact abscissa, and its Dedekind zeta form -/

/-- **The exact abscissa of absolute convergence of the trivial ideal weight is `1`.**

The upper linear ideal count on its own supplies convergence on `Re s > 1`, and the two counts
together supply divergence at `s = 1`; no analytic continuation of the Dedekind zeta function, and
no knowledge of its pole, is involved. -/
@[simp]
theorem abscissaOfAbsConv_normCoeff_one :
    LSeries.abscissaOfAbsConv (normCoeff K (1 : IdealArithmeticFunction K)) = 1 := by
  refine le_antisymm (abscissaOfAbsConv_normCoeff_one_le K) ?_
  by_contra h
  exact not_LSeriesSummable_normCoeff_one K
    (LSeriesSummable_of_abscissaOfAbsConv_lt_re (s := 1) (by simpa using not_le.mp h))

/-- The Dirichlet series of the trivial ideal weight converges exactly on the open half-plane
`Re s > 1`; on the line `Re s = 1` it diverges. -/
@[simp]
theorem LSeriesSummable_normCoeff_one_iff {s : ℂ} :
    LSeriesSummable (normCoeff K (1 : IdealArithmeticFunction K)) s ↔ 1 < s.re := by
  refine ⟨fun h ↦ ?_, fun h ↦ LSeriesSummable_of_abscissaOfAbsConv_lt_re ?_⟩
  · have h1 : (1 : ℝ) ≤ s.re := by
      have hle := h.abscissaOfAbsConv_le
      rw [abscissaOfAbsConv_normCoeff_one K] at hle
      exact_mod_cast hle
    rcases h1.lt_or_eq with h2 | h2
    · exact h2
    · exact absurd
        ((LSeriesSummable_iff_of_re_eq_re (s' := 1) (by rw [Complex.one_re, ← h2])).mp h)
        (not_LSeriesSummable_normCoeff_one K)
  · rw [abscissaOfAbsConv_normCoeff_one K]
    exact_mod_cast h

/-- **The Dedekind zeta series has abscissa of absolute convergence `1`.** -/
@[simp]
theorem abscissaOfAbsConv_dedekindZetaCoeff :
    LSeries.abscissaOfAbsConv (fun n ↦ (dedekindZetaCoeff K n : ℂ)) = 1 := by
  rw [← abscissaOfAbsConv_normCoeff_one K]
  refine LSeries.abscissaOfAbsConv_congr fun {n} hn ↦ ?_
  rw [normCoeff_one_apply, ite_eq_right hn]

/-- The Dedekind zeta series converges exactly on the open half-plane `Re s > 1`. -/
@[simp]
theorem LSeriesSummable_dedekindZetaCoeff_iff {s : ℂ} :
    LSeriesSummable (fun n ↦ (dedekindZetaCoeff K n : ℂ)) s ↔ 1 < s.re := by
  rw [← LSeriesSummable_normCoeff_one_iff K]
  exact LSeriesSummable_congr s fun {n} hn ↦ by rw [normCoeff_one_apply, ite_eq_right hn]

end TauCeti

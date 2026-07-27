/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.L2.Covariance

/-!
# Two-window L² bounds for block averages of a contractable sequence

This file continues the Layer 3 (L²) lane of the Exchangeability roadmap
(`TauCetiRoadmap/Exchangeability/README.md`, "Layer 3: L² averaging library and the
standard-Borel de Finetti route"), building the "two-window L² bounds for block averages"
milestone (`l2_bound_two_windows_uniform`) on top of the uniform covariance structure of a
contractable L² sequence (`contractable_covariance_structure`).

For a real-valued process `X : ℕ → Ω → ℝ` and a finite selection `k : Fin n → ℕ`, the
*block average* `blockAverage X k = n⁻¹ • ∑ i, X (k i)` is the empirical mean of the block
`(X (k i))ᵢ`. When `X` is contractable with `L²` coordinates, its second-moment structure is
uniform: all coordinate variances agree and all off-diagonal covariances agree
(`contractable_covariance_structure`). Writing `v = Var[X 0]` and `c = cov[X 0, X 1]`, this
uniformity forces the block average to have the explicit variance

```text
Var[blockAverage X k] = (v - c) / n + c,
```

and any two blocks over *disjoint* index sets to have covariance exactly `c`. Consequently two
disjoint block averages of lengths `n` and `m` satisfy

```text
Var[blockAverage X k - blockAverage X k'] = (v - c) / n + (v - c) / m,
```

and, since contractability makes the two averages share the common mean `μ[X 0]`, this is the
squared `L²` distance `∫ (blockAverage X k - blockAverage X k')² dμ` itself. The squared
distance vanishes like `1 / n + 1 / m` (equivalently, the `L²` norm like `n^(-1/2)` for equal
windows), which is the analytic engine that later drives the `L²` convergence of the observables
`blockAverage X k` toward their common conditional mean, the intermediate real-valued step
before the roadmap's determining-class argument identifies the directing random measure.

The elementary L² route to de Finetti's theorem formalised here is the one presented in
Kallenberg, *Probabilistic Symmetries and Invariance Principles* (Springer, 2005), Chapter 1
(around Theorem 1.1); the Lean identities below were derived independently.

The covariance/variance bilinearity (`ProbabilityTheory.covariance_sum_sum`,
`variance_sum`, `covariance_smul_left`, `variance_const_mul`) and the integral manipulations are
Mathlib's; the contractability input is the Layer 0/3 API in
`TauCeti.Probability.Exchangeability.Contractability` and
`TauCeti.Probability.Exchangeability.L2.Covariance`. No material from
`cameronfreer/exchangeability` is reused: the source carries the block-average bounds through a
different, sequence-specific `L²` development, whereas this file records the closed-form
second-moment identities directly.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators

namespace TauCeti

namespace Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- The **block average** of a real-valued process `X` over a finite selection `k : Fin n → ℕ`:
the empirical mean `n⁻¹ • ∑ i, X (k i)` of the block `(X (k i))ᵢ`. -/
def blockAverage (X : ℕ → Ω → ℝ) {n : ℕ} (k : Fin n → ℕ) : Ω → ℝ :=
  𝔼 i, X (k i)

omit [MeasurableSpace Ω] in
@[simp]
theorem blockAverage_apply {n : ℕ} (k : Fin n → ℕ) (ω : Ω) :
    blockAverage X k ω = (n : ℝ)⁻¹ * ∑ i, X (k i) ω := by
  rw [blockAverage, Finset.expect_apply, Fintype.expect_eq_sum_div_card]
  simp [div_eq_inv_mul]

omit [MeasurableSpace Ω] in
/-- A block average as a real-scaled finite sum. -/
theorem blockAverage_eq_sum {n : ℕ} (k : Fin n → ℕ) :
    blockAverage X k = (n : ℝ)⁻¹ • ∑ i, X (k i) := by
  ext ω
  simp

/-- A block average of `L²` coordinates is itself `L²`. -/
theorem memLp_blockAverage {n : ℕ} (k : Fin n → ℕ) (hX_L2 : ∀ i, MemLp (X (k i)) 2 μ) :
    MemLp (blockAverage X k) 2 μ := by
  rw [blockAverage_eq_sum]
  exact (memLp_finsetSum' _ fun i _ => hX_L2 i).const_smul _

/-- The double sum of block covariances splits along the diagonal into the common variance and
the common off-diagonal covariance of a contractable `L²` sequence. -/
private theorem sum_sum_cov_eq (hX : Contractable μ X)
    (hmeas : ∀ m, AEMeasurable (X m) μ) {n : ℕ} {k : Fin n → ℕ} (hk : Function.Injective k) :
    ∑ i, ∑ j, cov[X (k i), X (k j); μ]
      = (n : ℝ) ^ 2 * cov[X 0, X 1; μ] + n * (Var[X 0; μ] - cov[X 0, X 1; μ]) := by
  have hcov : ∀ i j : Fin n, cov[X (k i), X (k j); μ]
      = cov[X 0, X 1; μ] + (if i = j then Var[X 0; μ] - cov[X 0, X 1; μ] else 0) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, covariance_self (hmeas _), hX.variance_coord_eq (hmeas _) (hmeas 0)]
      ring
    · rw [if_neg hij, hX.covariance_eq_of_ne (hmeas _) (hmeas _) (hmeas 0) (hmeas 1)
        (fun h => hij (hk h)) (by norm_num)]
      ring
  simp_rw [hcov]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **The variance of a block average of a contractable L² sequence.** For a contractable
real-valued process with `L²` coordinates and an injective selection `k : Fin n → ℕ` (`0 < n`),
the block average has the closed-form variance `(v - c) / n + c`, where `v = Var[X 0]` is the
common coordinate variance and `c = cov[X 0, X 1]` is the common off-diagonal covariance. -/
theorem Contractable.variance_blockAverage [IsFiniteMeasure μ] (hX : Contractable μ X)
    (hX_L2 : ∀ n, MemLp (X n) 2 μ) {n : ℕ} (hn : 0 < n) {k : Fin n → ℕ}
    (hk : Function.Injective k) :
    Var[blockAverage X k; μ] = (Var[X 0; μ] - cov[X 0, X 1; μ]) / n + cov[X 0, X 1; μ] := by
  have hmeas : ∀ m, AEMeasurable (X m) μ := fun m => (hX_L2 m).aestronglyMeasurable.aemeasurable
  have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [blockAverage_eq_sum, variance_smul, variance_sum (fun i => hX_L2 (k i)),
    sum_sum_cov_eq hX hmeas hk]
  field_simp
  ring

/-- **The mean of a block average of a contractable process.** A block average over any
selection of length `0 < n` has the common coordinate mean `μ[X 0]`. -/
theorem Contractable.integral_blockAverage (hX : Contractable μ X)
    (hint0 : Integrable (X 0) μ) {n : ℕ} (hn : 0 < n) {k : Fin n → ℕ}
    (hint : ∀ i, Integrable (X (k i)) μ) :
    μ[blockAverage X k] = μ[X 0] := by
  have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  simp_rw [blockAverage_apply]
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => hint i)]
  simp_rw [fun i => hX.integral_coord_eq (hint i).aemeasurable hint0.aemeasurable]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ hne, one_mul]

/-- **The covariance of two disjoint block averages of a contractable L² sequence.** Two block
averages over selections `k : Fin n → ℕ` and `k' : Fin m → ℕ` with disjoint ranges
(`0 < n`, `0 < m`) have covariance exactly the common off-diagonal covariance `c = cov[X 0, X 1]`,
regardless of the two block lengths. -/
theorem Contractable.covariance_blockAverage_of_disjoint [IsFiniteMeasure μ] (hX : Contractable μ X)
    (hX_L2 : ∀ n, MemLp (X n) 2 μ) {n m : ℕ} (hn : 0 < n) (hm : 0 < m) {k : Fin n → ℕ}
    {k' : Fin m → ℕ} (hdisj : ∀ i j, k i ≠ k' j) :
    cov[blockAverage X k, blockAverage X k'; μ] = cov[X 0, X 1; μ] := by
  have hmeas : ∀ p, AEMeasurable (X p) μ := fun p => (hX_L2 p).aestronglyMeasurable.aemeasurable
  have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hne' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  rw [blockAverage_eq_sum, blockAverage_eq_sum, covariance_smul_left, covariance_smul_right,
    covariance_sum_sum (fun i => hX_L2 (k i)) (fun j => hX_L2 (k' j))]
  simp_rw [fun i j => hX.covariance_eq_of_ne (hmeas (k i)) (hmeas (k' j)) (hmeas 0) (hmeas 1)
    (hdisj i j) (by norm_num : (0 : ℕ) ≠ 1)]
  rw [Finset.sum_const, Finset.sum_const]
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- **The two-window L² bound for block averages.** For a contractable real-valued process with
`L²` coordinates, two block averages over injective selections `k : Fin n → ℕ` and
`k' : Fin m → ℕ` with disjoint ranges (`0 < n`, `0 < m`) satisfy

```text
Var[blockAverage X k - blockAverage X k'] = (v - c) / n + (v - c) / m,
```

where `v = Var[X 0]` and `c = cov[X 0, X 1]`. The bound vanishes as the block lengths grow, which
is the analytic core of the L² route to de Finetti's theorem. -/
theorem Contractable.variance_blockAverage_sub_of_disjoint [IsFiniteMeasure μ]
    (hX : Contractable μ X) (hX_L2 : ∀ n, MemLp (X n) 2 μ) {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {k : Fin n → ℕ} {k' : Fin m → ℕ}
    (hk : Function.Injective k) (hk' : Function.Injective k') (hdisj : ∀ i j, k i ≠ k' j) :
    Var[blockAverage X k - blockAverage X k'; μ]
      = (Var[X 0; μ] - cov[X 0, X 1; μ]) / n + (Var[X 0; μ] - cov[X 0, X 1; μ]) / m := by
  rw [variance_sub (memLp_blockAverage k fun i => hX_L2 (k i))
      (memLp_blockAverage k' fun i => hX_L2 (k' i)),
    hX.variance_blockAverage hX_L2 hn hk, hX.variance_blockAverage hX_L2 hm hk',
    hX.covariance_blockAverage_of_disjoint hX_L2 hn hm hdisj]
  ring

/-- **The two-window L² distance for block averages.** Since two disjoint block averages of a
contractable process share the common mean `μ[X 0]`, the two-window variance bound is the
squared `L²` distance between them:

```text
∫ (blockAverage X k - blockAverage X k')² dμ = (v - c) / n + (v - c) / m.
```
-/
theorem Contractable.integral_sq_blockAverage_sub_of_disjoint [IsFiniteMeasure μ]
    (hX : Contractable μ X) (hX_L2 : ∀ n, MemLp (X n) 2 μ) {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {k : Fin n → ℕ} {k' : Fin m → ℕ}
    (hk : Function.Injective k) (hk' : Function.Injective k') (hdisj : ∀ i j, k i ≠ k' j) :
    ∫ ω, (blockAverage X k ω - blockAverage X k' ω) ^ 2 ∂μ
      = (Var[X 0; μ] - cov[X 0, X 1; μ]) / n + (Var[X 0; μ] - cov[X 0, X 1; μ]) / m := by
  have hmean : μ[blockAverage X k - blockAverage X k'] = 0 := by
    simp only [Pi.sub_apply]
    rw [integral_sub ((memLp_blockAverage k fun i => hX_L2 (k i)).integrable one_le_two)
      ((memLp_blockAverage k' fun i => hX_L2 (k' i)).integrable one_le_two),
      hX.integral_blockAverage ((hX_L2 0).integrable one_le_two) hn
        (fun i => (hX_L2 (k i)).integrable one_le_two),
      hX.integral_blockAverage ((hX_L2 0).integrable one_le_two) hm
        (fun i => (hX_L2 (k' i)).integrable one_le_two),
      sub_self]
  have hae : AEMeasurable (blockAverage X k - blockAverage X k') μ :=
    ((memLp_blockAverage k fun i => hX_L2 (k i)).sub
      (memLp_blockAverage k' fun i => hX_L2 (k' i))).aestronglyMeasurable.aemeasurable
  rw [← hX.variance_blockAverage_sub_of_disjoint hX_L2 hn hm hk hk' hdisj,
    variance_of_integral_eq_zero hae hmean]
  simp [Pi.sub_apply]

end Probability

end TauCeti

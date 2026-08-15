/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Matrix.PosSemidef

/-!
# Bounded positive-definite kernels decrease along a symmetric shift

Let `K` be a positive-definite kernel on a type `α` and let `σ : α → α` be a *symmetric shift*,
meaning `K (σ p) q = K p (σ q)`. If `K` is bounded, then the shifted kernel is dominated by `K`:
the difference

`(p, q) ↦ K p q - K (σ p) q`

is again positive definite. Boundedness cannot be dropped — for `K p q = exp (p + q)` on `ℝ` and
`σ = (· + 1)` the difference is *negative* definite — and it is exactly what the proof consumes.

The mechanism is a moment-problem estimate. Fixing a finite family of points and coefficients, the
numbers `a n = ∑ᵢⱼ conj (cᵢ) K (σⁿ pᵢ) (pⱼ) c ⱼ` form a positive-semidefinite Hankel matrix
`(m, n) ↦ a (m + n)`, because the shift can be moved from one argument to the other. Cauchy--Schwarz
for that matrix gives `a n ^ 2 ≤ a 0 * a (2 n)`, so `a 1 > a 0 ≥ 0` would force
`a (2 ^ k) ≥ a 0 (a 1 / a 0) ^ (2 ^ k) → ∞`, contradicting boundedness. Hence `a 0 - a 1 ≥ 0`,
which is the quadratic form of the difference kernel.

This advances `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part C, Milestone 2
("BCR semigroup--Bochner"): applied to the Berg--Christensen--Ressel kernel of a bounded
positive-definite function on `[0,∞) × V` with the time shift, it is the step that turns positive
definiteness into complete monotonicity in the time variable.

## Main declarations

* `TauCeti.sub_nonneg_of_posSemidef_hankel`: a bounded positive-semidefinite Hankel sequence does
  not increase at the first step.
* `TauCeti.posSemidef_sub_comp_shift`: the difference of a bounded positive-definite kernel and its
  shift by a symmetric shift is positive definite.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 4.
-/

public section

open scoped ComplexOrder

namespace TauCeti

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]

/-! ## Bounded positive-semidefinite Hankel sequences -/

/-- The numerical core of the Hankel estimate: a bounded sequence of reals whose squares satisfy
the Cauchy--Schwarz inequality `b n ^ 2 ≤ b 0 * b (n + n)` cannot increase at the first step. If it
did, the ratio `r = b 1 / b 0` would exceed `1` and the doubling inequality would push
`b (2 ^ k)` past `b 0 * r ^ (2 ^ k)`, which is unbounded. -/
private theorem apply_one_le_apply_zero_of_sq_le_mul {b : ℕ → ℝ} {D : ℝ} (hb0 : 0 ≤ b 0)
    (hsq : ∀ n, b n ^ 2 ≤ b 0 * b (n + n)) (hbd : ∀ n, b n ≤ D) : b 1 ≤ b 0 := by
  rcases le_or_gt (b 1) (b 0) with hle | hlt
  · exact hle
  exfalso
  have hb0pos : 0 < b 0 := by
    rcases hb0.lt_or_eq with h | h
    · exact h
    · have h1 := hsq 1
      rw [← h] at h1
      nlinarith
  set r : ℝ := b 1 / b 0 with hr
  have hr1 : 1 < r := (one_lt_div hb0pos).mpr hlt
  have hrpos : 0 < r := lt_trans zero_lt_one hr1
  have key : ∀ k : ℕ, b 0 * r ^ 2 ^ k ≤ b (2 ^ k) := by
    intro k
    induction k with
    | zero =>
        have : b 0 * r = b 1 := by
          rw [hr, mul_div_cancel₀ _ hb0pos.ne']
        simpa using this.le
    | succ k ih =>
        have hpow : (0 : ℝ) < r ^ 2 ^ k := pow_pos hrpos _
        have hsplit : (2 : ℕ) ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
        have hsq' := hsq (2 ^ k)
        have hrw : r ^ 2 ^ (k + 1) = (r ^ 2 ^ k) ^ 2 := by
          rw [hsplit, pow_add, sq]
        rw [hrw, hsplit]
        nlinarith [mul_pos hb0pos hpow]
  obtain ⟨k, hk⟩ := exists_nat_gt ((D / b 0 - 1) / (r - 1))
  have hkr : D / b 0 - 1 < k * (r - 1) := (div_lt_iff₀ (by linarith)).mp hk
  have hD : D < b 0 * (1 + k * (r - 1)) := by
    have h : D / b 0 < 1 + k * (r - 1) := by linarith
    rw [mul_comm]
    exact (div_lt_iff₀ hb0pos).mp h
  have hbern : 1 + k * (r - 1) ≤ r ^ k := by
    simpa using one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ r - 1) k
  have hmono : r ^ k ≤ r ^ 2 ^ k :=
    pow_le_pow_right₀ hr1.le (Nat.le_of_lt k.lt_two_pow_self)
  have hchain : b 0 * (1 + k * (r - 1)) ≤ D :=
    le_trans (le_trans (mul_le_mul_of_nonneg_left (hbern.trans hmono) hb0pos.le) (key k))
      (hbd _)
  linarith

/-- **A bounded positive-semidefinite Hankel sequence does not increase at the first step.**
If `(m, n) ↦ a (m + n)` is positive semidefinite and `a` is bounded in norm, then `a 1 ≤ a 0`
in the `RCLike` order. This is the moment-problem estimate behind `posSemidef_sub_comp_shift`:
Cauchy--Schwarz alone gives `a n ^ 2 ≤ a 0 * a (2 n)`, and boundedness rules out a ratio
`a 1 / a 0` greater than `1`. -/
theorem sub_nonneg_of_posSemidef_hankel {a : ℕ → 𝕜} {D : ℝ}
    (ha : Matrix.PosSemidef fun m n : ℕ => a (m + n)) (hbd : ∀ n, ‖a n‖ ≤ D) :
    0 ≤ a 0 - a 1 := by
  have hreal : ∀ n, (starRingEnd 𝕜) (a n) = a n := by
    intro n
    simpa using ha.isHermitian.apply n 0
  have him : ∀ n, RCLike.im (a n) = 0 := fun n => RCLike.conj_eq_iff_im.mp (hreal n)
  set b : ℕ → ℝ := fun n => RCLike.re (a n) with hbdef
  have hnormSq : ∀ n, RCLike.normSq (a n) = b n ^ 2 := by
    intro n
    rw [RCLike.normSq_apply, him n]
    simp [hbdef, sq]
  have hb0 : 0 ≤ b 0 := by
    have h := ha.diag_nonneg (i := 0)
    simpa [hbdef] using (RCLike.nonneg_iff.mp (by simpa using h)).1
  have hsq : ∀ n, b n ^ 2 ≤ b 0 * b (n + n) := by
    intro n
    have h := ha.normSq_le 0 n
    simpa [hnormSq, hbdef] using h
  have hbdb : ∀ n, b n ≤ D := fun n =>
    le_trans (RCLike.re_le_norm (a n)) (hbd n)
  have hmain : b 1 ≤ b 0 := apply_one_le_apply_zero_of_sq_le_mul hb0 hsq hbdb
  rw [RCLike.nonneg_iff]
  constructor
  · simpa [hbdef] using sub_nonneg.mpr hmain
  · simp [him 0, him 1]

/-! ## Positive-definite kernels and symmetric shifts -/

section Shift

variable {α : Type v} {K : α → α → 𝕜} {σ : α → α}

omit [RCLike 𝕜] in
/-- A symmetric shift can be split between the two arguments of the kernel:
`K (σ^[m + n] p) q = K (σ^[m] p) (σ^[n] q)`. -/
private theorem apply_iterate_add (hshift : ∀ p q, K (σ p) q = K p (σ q)) (m n : ℕ) (p q : α) :
    K (σ^[m + n] p) q = K (σ^[m] p) (σ^[n] q) := by
  induction n generalizing q with
  | zero => simp
  | succ n ih =>
      rw [show m + (n + 1) = m + n + 1 from rfl, Function.iterate_succ_apply', hshift, ih,
        ← Function.iterate_succ_apply]

omit [RCLike 𝕜] in
/-- Moving the whole iterated shift onto the left argument. -/
private theorem apply_iterate_right (hshift : ∀ p q, K (σ p) q = K p (σ q)) (n : ℕ) (p q : α) :
    K p (σ^[n] q) = K (σ^[n] p) q := by
  simpa using (apply_iterate_add hshift 0 n p q).symm

/-- **The difference of a bounded positive-definite kernel and its shift is positive definite.**
Here `σ` is a *symmetric* shift, `K (σ p) q = K p (σ q)`, and `K` is bounded in norm by `C`.
Boundedness is essential: for the (unbounded) kernel `(p, q) ↦ exp (p + q)` on `ℝ` and the shift
`σ = (· + 1)` the difference below is the negative of a positive-definite kernel. -/
theorem posSemidef_sub_comp_shift {C : ℝ} (hK : Matrix.PosSemidef K)
    (hshift : ∀ p q, K (σ p) q = K p (σ q)) (hbdd : ∀ p q, ‖K p q‖ ≤ C) :
    Matrix.PosSemidef fun p q : α => K p q - K (σ p) q := by
  have hherm : ∀ p q : α, star (K p q) = K q p :=
    (posSemidef_iff_finite_sum.{u, v, v}.mp hK).1
  refine posSemidef_iff_finite_sum.{u, v, v}.mpr ⟨fun p q => ?_, ?_⟩
  · rw [star_sub, hherm, hherm, hshift]
  intro ι _ v c
  -- the Hankel sequence attached to the finite family `(v, c)`
  let a : ℕ → 𝕜 := fun n => ∑ i, ∑ j, star (c i) * K (σ^[n] (v i)) (v j) * c j
  have hadef : ∀ n, a n = ∑ i, ∑ j, star (c i) * K (σ^[n] (v i)) (v j) * c j := fun _ => rfl
  have hHankel : Matrix.PosSemidef fun m n : ℕ => a (m + n) := by
    refine posSemidef_iff_finite_sum.{u, 0, v}.mpr ⟨fun m n => ?_, ?_⟩
    · -- the entries are real, by Hermitian symmetry of `K` and the shift symmetry
      have hstar : ∀ k : ℕ, star (a k) = a k := by
        intro k
        simp only [hadef, star_sum, star_mul', star_star]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [hherm, apply_iterate_right hshift]
        ring
      rw [hstar, Nat.add_comm]
    · intro κ _ w e
      have h := (posSemidef_iff_finite_sum.{u, v, v}.mp hK).2 (ι := κ × ι)
        (fun p => σ^[w p.1] (v p.2)) (fun p => e p.1 * c p.2)
      have hexp : ∀ s t : κ, star (e s) * a (w s + w t) * e t =
          ∑ i, ∑ j, star (e s * c i) *
            K (σ^[w s] (v i)) (σ^[w t] (v j)) * (e t * c j) := by
        intro s t
        simp only [hadef, Finset.mul_sum, Finset.sum_mul, star_mul',
          apply_iterate_add hshift (w s) (w t)]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      calc (0 : 𝕜) ≤ ∑ p : κ × ι, ∑ q : κ × ι, star (e p.1 * c p.2) *
            K (σ^[w p.1] (v p.2)) (σ^[w q.1] (v q.2)) * (e q.1 * c q.2) := h
        _ = ∑ s, ∑ i, ∑ t, ∑ j, star (e s * c i) *
              K (σ^[w s] (v i)) (σ^[w t] (v j)) * (e t * c j) := by
            simp only [Fintype.sum_prod_type]
        _ = ∑ s, ∑ t, ∑ i, ∑ j, star (e s * c i) *
              K (σ^[w s] (v i)) (σ^[w t] (v j)) * (e t * c j) := by
            exact Finset.sum_congr rfl fun s _ => Finset.sum_comm
        _ = ∑ s, ∑ t, star (e s) * a (w s + w t) * e t := by
            simp only [hexp]
  have hbda : ∀ n, ‖a n‖ ≤ ∑ i, ∑ j, ‖c i‖ * ‖c j‖ * C := by
    intro n
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    calc ‖star (c i) * K (σ^[n] (v i)) (v j) * c j‖
        = ‖c i‖ * ‖K (σ^[n] (v i)) (v j)‖ * ‖c j‖ := by simp [norm_mul]
      _ ≤ ‖c i‖ * C * ‖c j‖ := by gcongr; exact hbdd _ _
      _ = ‖c i‖ * ‖c j‖ * C := by ring
  have hstep := sub_nonneg_of_posSemidef_hankel hHankel hbda
  have hsub : a 0 - a 1 = ∑ i, ∑ j, star (c i) * (K (v i) (v j) - K (σ (v i)) (v j)) * c j := by
    simp only [hadef, Function.iterate_zero, Function.iterate_one, id_eq, mul_sub, sub_mul,
      ← Finset.sum_sub_distrib]
  rwa [hsub] at hstep

end Shift

end TauCeti

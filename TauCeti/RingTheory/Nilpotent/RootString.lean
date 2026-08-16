/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.RingTheory.DividedPowers.RootString
public import TauCeti.RingTheory.Nilpotent.ChevalleyCommutator

/-!
# The Chevalley commutator relation along a root string of length three

Let `V` be a module over a `ℚ`-algebra `A`, let `M ≤ V` be an additive subgroup, and let `x`, `y`,
`z`, `w` be elements of `A` with

```text
x * y = y * x + z,   x * z = z * x + 2 • w,
```

`w` commuting with `x`, and `y`, `z`, `w` commuting with one another. The integral divided-power
exponentials of the four elements act on `R ⊗[ℤ] M` over every commutative ring `R`, by
`TauCeti.baseChangeExp`. The main result below is that they satisfy the **Chevalley commutator
relation for a root string of length three**

```text
E_x(t) E_y(u) = E_y(u) E_z(t * u) E_w(t ^ 2 * u) E_x(t).
```

This is the case of the Chevalley commutator formula in which the roots of the form `i α + j β`
with `i, j > 0` are exactly `α + β` and `2 α + β`, which is what the multiply-laced types `B`, `C`,
`F₄` and `G₂` contribute beyond the class-two case of
`TauCeti.baseChangeExp_mul_baseChangeExp_of_commutator_eq`. The parameter of the extra factor is
`t ^ 2 * u`, matching the exponents `(i, j) = (2, 1)` of the root `2 α + β`.

Nothing here divides by a factorial in `R`, so the relation holds over a ring of arbitrary
characteristic. The whole point is the coefficient-one straightening rule
`TauCeti.Associative.dividedPower_mul_dividedPower_of_root_string`; the exponential identity is its
generating-function form, and the parameters `u`, `t * u`, `t ^ 2 * u`, `t` are exactly the four
monomials `u ^ a (t u) ^ b (t ^ 2 u) ^ c t ^ q` into which `t ^ m u ^ n` factors.

## Main results

* `TauCeti.integralDividedPower_mul_integralDividedPower_of_root_string`: the straightening rule
  for the integral operators restricted to `M`.
* `TauCeti.isNilpotent_of_commutator_eq_two_nsmul`: the second element of the root string is
  nilpotent as soon as the first is.
* `TauCeti.baseChangeExp_mul_baseChangeExp_of_root_string`: the Chevalley commutator relation.
* `TauCeti.baseChangeExp_conj_of_root_string`: its conjugation form.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §4.2 and Theorem 5.2.2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§25--26.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti

open Finset TensorProduct

universe u v

variable {A : Type*} [Ring A] [Algebra ℚ A]
variable {V : Type u} [AddCommGroup V] [Module A V]
variable {S : Type*} [SetLike S V] [AddSubgroupClass S V]

/-! ## Straightening the restricted operators -/

/-- **Straightening restricted divided powers along a root string of length three.** If
`x * y = y * x + z` and `x * z = z * x + 2 • w` with `w` central for `x` and `y`, `z`, `w` pairwise
commuting, the integral operators obtained by restricting divided powers to a stable additive
subgroup satisfy the coefficient-one straightening rule. -/
theorem integralDividedPower_mul_integralDividedPower_of_root_string
    {x y z w : A} (M : S) (hxy : x * y = y * x + z) (hxz : x * z = z * x + 2 • w)
    (hxw : Commute x w) (hyz : Commute y z) (hzw : Commute z w)
    (hMx : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M)
    (hMy : ∀ n, ∀ v ∈ M, Associative.dividedPower n y • v ∈ M)
    (hMz : ∀ n, ∀ v ∈ M, Associative.dividedPower n z • v ∈ M)
    (hMw : ∀ n, ∀ v ∈ M, Associative.dividedPower n w • v ∈ M)
    (m n : ℕ) :
    integralDividedPower x M m (hMx m) * integralDividedPower y M n (hMy n) =
      ∑ p ∈ {p ∈ range (n + 1) ×ˢ range (n + 1) | p.1 + p.2 ≤ n ∧ p.1 + 2 * p.2 ≤ m},
        integralDividedPower y M (n - p.1 - p.2) (hMy (n - p.1 - p.2)) *
          integralDividedPower z M p.1 (hMz p.1) *
          integralDividedPower w M p.2 (hMw p.2) *
          integralDividedPower x M (m - p.1 - 2 * p.2) (hMx (m - p.1 - 2 * p.2)) := by
  ext v
  simp only [Module.End.mul_apply, LinearMap.sum_apply, AddSubmonoidClass.coe_finsetSum,
    coe_integralDividedPower_apply, ← mul_smul, ← Finset.sum_smul]
  congr 1
  simpa only [mul_assoc] using
    Associative.dividedPower_mul_dividedPower_of_root_string hxy hxz hxw hyz hzw m n

/-! ## Nilpotency of the far end of the root string -/

/-- The second element of a root string is nilpotent as soon as the first is: `2 • w` is the
commutator of `x` and `z`, and it commutes with both. -/
theorem isNilpotent_of_commutator_eq_two_nsmul {x z w : A} (hxz : x * z = z * x + 2 • w)
    (hxw : Commute x w) (hzw : Commute z w) (hx : IsNilpotent x) : IsNilpotent w := by
  have hxw2 : Commute x (2 • w) := by
    rw [two_smul]
    exact hxw.add_right hxw
  have hzw2 : Commute z (2 • w) := by
    rw [two_smul]
    exact hzw.add_right hzw
  obtain ⟨k, hk⟩ := Associative.isNilpotent_of_commutator_eq hxz hxw2 hzw2 hx
  refine ⟨k, ?_⟩
  rw [smul_pow] at hk
  have hk' : ((2 ^ k : ℕ) : ℚ) • w ^ k = 0 := by rwa [Nat.cast_smul_eq_nsmul]
  have h2 : ((2 ^ k : ℕ) : ℚ) ≠ 0 := by positivity
  calc w ^ k = ((2 ^ k : ℕ) : ℚ)⁻¹ • (((2 ^ k : ℕ) : ℚ) • w ^ k) := (inv_smul_smul₀ h2 _).symm
    _ = 0 := by rw [hk', smul_zero]

/-! ## The generating-function form of the straightening rule -/

-- The combinatorial core: a truncated left factor times a truncated right factor is the reordered
-- quadruple product, once the truncation is wide enough that the reindexed hypercube contains no
-- extra nonzero terms. The reindexing is `(m, n, b, c) ↦ (n - b - c, b, c, m - b - 2c)`, and the
-- monomial `t ^ m u ^ n` factors accordingly as `u ^ a (t u) ^ b (t ^ 2 u) ^ c t ^ q`. The proof
-- is the four-factor analogue of the class-two argument in
-- `TauCeti.RingTheory.Nilpotent.ChevalleyCommutator`, and follows it step for step.
private theorem sum_smul_mul_sum_smul_of_rootStringOrder {R : Type*} [CommRing R]
    {B : Type*} [Ring B] [Algebra R B] (Dx Dy Dz Dw : ℕ → B) (N : ℕ)
    (hno : ∀ m n, Dx m * Dy n =
      ∑ p ∈ {p ∈ range (n + 1) ×ˢ range (n + 1) | p.1 + p.2 ≤ n ∧ p.1 + 2 * p.2 ≤ m},
        Dy (n - p.1 - p.2) * Dz p.1 * Dw p.2 * Dx (m - p.1 - 2 * p.2))
    (hzero : ∀ a b c q : ℕ, N ≤ a + b + c ∨ N ≤ q + b + 2 * c →
      Dy a * Dz b * Dw c * Dx q = 0)
    (t u : R) :
    (∑ m ∈ range N, t ^ m • Dx m) * (∑ n ∈ range N, u ^ n • Dy n) =
      (∑ a ∈ range N, u ^ a • Dy a) * (∑ b ∈ range N, (t * u) ^ b • Dz b) *
        (∑ c ∈ range N, (t ^ 2 * u) ^ c • Dw c) * (∑ q ∈ range N, t ^ q • Dx q) := by
  classical
  set G : ℕ × ℕ × ℕ × ℕ → B := fun v =>
    (u ^ v.1 * (t * u) ^ v.2.1 * (t ^ 2 * u) ^ v.2.2.1 * t ^ v.2.2.2) •
      (Dy v.1 * Dz v.2.1 * Dw v.2.2.1 * Dx v.2.2.2) with hG
  -- Step 1: expand the reordered product over the full hypercube of indices.
  have hbox : ∑ v ∈ range N ×ˢ range N ×ˢ range N ×ˢ range N, G v =
      (∑ a ∈ range N, u ^ a • Dy a) * (∑ b ∈ range N, (t * u) ^ b • Dz b) *
        (∑ c ∈ range N, (t ^ 2 * u) ^ c • Dw c) * (∑ q ∈ range N, t ^ q • Dx q) := by
    rw [mul_assoc, mul_assoc, Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_mul_sum]
    simp only [hG, Finset.sum_product, Finset.mul_sum, smul_mul_smul_comm, mul_assoc]
  -- Step 2: expand the original product over the reindexing domain.
  have hsrc : ∑ v ∈ (range N ×ˢ range N).sigma
        (fun mn => {p ∈ range (mn.2 + 1) ×ˢ range (mn.2 + 1) |
          p.1 + p.2 ≤ mn.2 ∧ p.1 + 2 * p.2 ≤ mn.1}),
        (t ^ v.1.1 * u ^ v.1.2) •
          (Dy (v.1.2 - v.2.1 - v.2.2) * Dz v.2.1 * Dw v.2.2 *
            Dx (v.1.1 - v.2.1 - 2 * v.2.2)) =
      (∑ m ∈ range N, t ^ m • Dx m) * (∑ n ∈ range N, u ^ n • Dy n) := by
    rw [Finset.sum_sigma, Finset.sum_mul_sum]
    simp only [Finset.sum_product, smul_mul_smul_comm, hno, Finset.smul_sum]
  -- Step 3: the reindexing itself, onto the part of the hypercube it covers.
  have hbij : ∑ v ∈ (range N ×ˢ range N).sigma
        (fun mn => {p ∈ range (mn.2 + 1) ×ˢ range (mn.2 + 1) |
          p.1 + p.2 ≤ mn.2 ∧ p.1 + 2 * p.2 ≤ mn.1}),
        (t ^ v.1.1 * u ^ v.1.2) •
          (Dy (v.1.2 - v.2.1 - v.2.2) * Dz v.2.1 * Dw v.2.2 *
            Dx (v.1.1 - v.2.1 - 2 * v.2.2)) =
      ∑ v ∈ range N ×ˢ range N ×ˢ range N ×ˢ range N with
        v.1 + v.2.1 + v.2.2.1 < N ∧ v.2.2.2 + v.2.1 + 2 * v.2.2.1 < N, G v := by
    refine Finset.sum_nbij'
      (fun v => (v.1.2 - v.2.1 - v.2.2, v.2.1, v.2.2, v.1.1 - v.2.1 - 2 * v.2.2))
      (fun v => ⟨(v.2.2.2 + v.2.1 + 2 * v.2.2.1, v.1 + v.2.1 + v.2.2.1), (v.2.1, v.2.2.1)⟩)
      ?_ ?_ ?_ ?_ ?_
    · rintro ⟨⟨m, n⟩, b, c⟩ hv
      simp only [Finset.mem_sigma, Finset.mem_product, Finset.mem_range, Finset.mem_filter] at hv
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      omega
    · rintro ⟨a, b, c, q⟩ hv
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hv
      simp only [Finset.mem_sigma, Finset.mem_product, Finset.mem_range, Finset.mem_filter]
      omega
    · rintro ⟨⟨m, n⟩, b, c⟩ hv
      obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp (Finset.mem_sigma.mp hv).2).2
      have hbn : b + c ≤ n := h1
      have hbm : b + 2 * c ≤ m := h2
      have e1 : m - b - 2 * c + b + 2 * c = m := by omega
      have e2 : n - b - c + b + c = n := by omega
      simp [e1, e2]
    · rintro ⟨a, b, c, q⟩ _
      have e1 : a + b + c - b - c = a := by omega
      have e2 : q + b + 2 * c - b - 2 * c = q := by omega
      simp [e1, e2]
    · rintro ⟨⟨m, n⟩, b, c⟩ hv
      simp only [Finset.mem_sigma, Finset.mem_product, Finset.mem_range, Finset.mem_filter] at hv
      obtain ⟨a, rfl⟩ : ∃ a, n = a + (b + c) := ⟨n - b - c, by omega⟩
      obtain ⟨q, rfl⟩ : ∃ q, m = q + (b + 2 * c) := ⟨m - b - 2 * c, by omega⟩
      have h1 : a + (b + c) - b - c = a := by omega
      have h2 : q + (b + 2 * c) - b - 2 * c = q := by omega
      simp only [hG, h1, h2]
      congr 1
      simp only [mul_pow, pow_add, pow_mul]
      ring
  -- Step 4: the terms of the hypercube outside that part vanish.
  have hsub : ∑ v ∈ range N ×ˢ range N ×ˢ range N ×ˢ range N with
        v.1 + v.2.1 + v.2.2.1 < N ∧ v.2.2.2 + v.2.1 + 2 * v.2.2.1 < N, G v =
      ∑ v ∈ range N ×ˢ range N ×ˢ range N ×ˢ range N, G v := by
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    rintro ⟨a, b, c, q⟩ hmem hnot
    simp only [Finset.mem_product, Finset.mem_range] at hmem
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hnot
    have hor : N ≤ a + b + c ∨ N ≤ q + b + 2 * c := by omega
    simp [hG, hzero a b c q hor]
  rw [← hsrc, hbij, hsub, hbox]

/-! ## The Chevalley commutator relation -/

section Commutator

variable {R : Type v} [CommRing R] [Algebra ℤ R]

-- Match tensor products to the module structure carried by the explicit `ℤ`-algebra.
attribute [local instance high] Algebra.toModule

/-- **The Chevalley commutator relation along a root string of length three.** If
`x * y = y * x + z` and `x * z = z * x + 2 • w`, with `w` commuting with `x` and `y`, `z`, `w`
commuting with one another, then over every commutative ring `R` the integral divided-power
exponentials on `R ⊗[ℤ] M` satisfy

```text
E_x(t) E_y(u) = E_y(u) E_z(t * u) E_w(t ^ 2 * u) E_x(t).
```

No factorial is inverted in `R`: the relation holds in every characteristic. -/
theorem baseChangeExp_mul_baseChangeExp_of_root_string
    {x y z w : A} (M : S) (hxy : x * y = y * x + z) (hxz : x * z = z * x + 2 • w)
    (hxw : Commute x w) (hyz : Commute y z) (hzw : Commute z w)
    (hx : IsNilpotent x) (hy : IsNilpotent y) (hz : IsNilpotent z)
    (hMx : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M)
    (hMy : ∀ n, ∀ v ∈ M, Associative.dividedPower n y • v ∈ M)
    (hMz : ∀ n, ∀ v ∈ M, Associative.dividedPower n z • v ∈ M)
    (hMw : ∀ n, ∀ v ∈ M, Associative.dividedPower n w • v ∈ M)
    (t u : R) :
    baseChangeExp x M hMx t * baseChangeExp y M hMy u =
      baseChangeExp y M hMy u * baseChangeExp z M hMz (t * u) *
        baseChangeExp w M hMw (t ^ 2 * u) * baseChangeExp x M hMx t := by
  classical
  obtain ⟨kx, hkx⟩ := hx
  obtain ⟨ky, hky⟩ := hy
  obtain ⟨kz, hkz⟩ := hz
  obtain ⟨kw, hkw⟩ := isNilpotent_of_commutator_eq_two_nsmul hxz hxw hzw ⟨kx, hkx⟩
  set N := kx + ky + kz + 2 * kw with hNdef
  have hxN : x ^ N = 0 := pow_eq_zero_of_le (by omega) hkx
  have hyN : y ^ N = 0 := pow_eq_zero_of_le (by omega) hky
  have hzN : z ^ N = 0 := pow_eq_zero_of_le (by omega) hkz
  have hwN : w ^ N = 0 := pow_eq_zero_of_le (by omega) hkw
  rw [baseChangeExp_of_pow_eq_zero x M hMx hxN, baseChangeExp_of_pow_eq_zero y M hMy hyN,
    baseChangeExp_of_pow_eq_zero z M hMz hzN, baseChangeExp_of_pow_eq_zero w M hMw hwN]
  refine sum_smul_mul_sum_smul_of_rootStringOrder (R := R)
    (fun n => (integralDividedPower x M n (hMx n)).baseChange R)
    (fun n => (integralDividedPower y M n (hMy n)).baseChange R)
    (fun n => (integralDividedPower z M n (hMz n)).baseChange R)
    (fun n => (integralDividedPower w M n (hMw n)).baseChange R) N ?_ ?_ t u
  · intro m n
    have h := congrArg (fun f : Module.End ℤ M => (Module.End.baseChangeHom ℤ R M) f)
      (integralDividedPower_mul_integralDividedPower_of_root_string M hxy hxz hxw hyz hzw
        hMx hMy hMz hMw m n)
    simp only [map_mul, map_sum] at h
    exact h
  · -- Outside the truncation the reordered quadruple has a vanishing factor.
    have hvx : ∀ q, kx ≤ q → (integralDividedPower x M q (hMx q)).baseChange R = 0 := by
      intro q hq
      rw [integralDividedPower_eq_zero_of_le x M q (hMx q) hkx hq, LinearMap.baseChange_zero]
    have hvy : ∀ a, ky ≤ a → (integralDividedPower y M a (hMy a)).baseChange R = 0 := by
      intro a ha
      rw [integralDividedPower_eq_zero_of_le y M a (hMy a) hky ha, LinearMap.baseChange_zero]
    have hvz : ∀ b, kz ≤ b → (integralDividedPower z M b (hMz b)).baseChange R = 0 := by
      intro b hb
      rw [integralDividedPower_eq_zero_of_le z M b (hMz b) hkz hb, LinearMap.baseChange_zero]
    have hvw : ∀ c, kw ≤ c → (integralDividedPower w M c (hMw c)).baseChange R = 0 := by
      intro c hc
      rw [integralDividedPower_eq_zero_of_le w M c (hMw c) hkw hc, LinearMap.baseChange_zero]
    rintro a b c q (habc | hqbc)
    · rcases le_or_gt ky a with ha | ha
      · rw [hvy a ha, zero_mul, zero_mul, zero_mul]
      · rcases le_or_gt kz b with hb | hb
        · rw [hvz b hb, mul_zero, zero_mul, zero_mul]
        · rw [hvw c (by omega), mul_zero, zero_mul]
    · rcases le_or_gt kx q with hq | hq
      · rw [hvx q hq, mul_zero]
      · rcases le_or_gt kz b with hb | hb
        · rw [hvz b hb, mul_zero, zero_mul, zero_mul]
        · rw [hvw c (by omega), mul_zero, zero_mul]

/-- The conjugation form of the Chevalley commutator relation along a root string of length three:
conjugating the one-parameter subgroup of `y` by that of `x` multiplies it by the one-parameter
subgroups of `z` and of `w`, at the parameters `t * u` and `t ^ 2 * u`. -/
theorem baseChangeExp_conj_of_root_string
    {x y z w : A} (M : S) (hxy : x * y = y * x + z) (hxz : x * z = z * x + 2 • w)
    (hxw : Commute x w) (hyz : Commute y z) (hzw : Commute z w)
    (hx : IsNilpotent x) (hy : IsNilpotent y) (hz : IsNilpotent z)
    (hMx : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M)
    (hMy : ∀ n, ∀ v ∈ M, Associative.dividedPower n y • v ∈ M)
    (hMz : ∀ n, ∀ v ∈ M, Associative.dividedPower n z • v ∈ M)
    (hMw : ∀ n, ∀ v ∈ M, Associative.dividedPower n w • v ∈ M)
    (t u : R) :
    baseChangeExp x M hMx t * baseChangeExp y M hMy u * baseChangeExp x M hMx (-t) =
      baseChangeExp y M hMy u * baseChangeExp z M hMz (t * u) *
        baseChangeExp w M hMw (t ^ 2 * u) := by
  rw [baseChangeExp_mul_baseChangeExp_of_root_string M hxy hxz hxw hyz hzw hx hy hz
      hMx hMy hMz hMw t u,
    mul_assoc, ← baseChangeExp_add x M hMx hx t (-t), add_neg_cancel,
    baseChangeExp_zero x M hMx hx, mul_one]

end Commutator

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.RingTheory.DividedPowers.RootString.G2
public import TauCeti.RingTheory.Nilpotent.RootString.Basic

/-!
# The Chevalley commutator relation in type `G₂`

Let `V` be a module over a `ℚ`-algebra `A`, let `M ≤ V` be an additive subgroup, and let `x`, `y`,
`z`, `w`, `v`, `s` be elements of `A` with

```text
x * y = y * x + z,   x * z = z * x + 2 • w,   x * w = w * x + 3 • v,   w * z = z * w + 3 • s,
```

`v` and `s` commuting with `x`, `y` commuting with `z`, `w` commuting with `v`, and `s` commuting
with `z`, `w`, and `v`. The integral divided-power exponentials of the six elements act on
`R ⊗[ℤ] M` over every commutative ring `R`, by `TauCeti.baseChangeExp`. The main result below is the
**Chevalley commutator relation in type `G₂`**

```text
E_x(t) E_y(u) = E_y(u) E_z(t * u) E_w(t ^ 2 * u) E_v(t ^ 3 * u) E_s(t ^ 3 * u ^ 2) E_x(t).
```

This is the case of the Chevalley commutator formula in which the roots of the form `i α + j β`
with `i, j > 0` are `α + β`, `2α + β`, `3α + β`, and `3α + 2β`. It occurs for the two simple roots
of a root system of type `G₂`, `α` short and `β` long, and in no other type; it extends the chain
`β`, `α + β`, `2α + β` of
`TauCeti.baseChangeExp_mul_baseChangeExp_of_commutator_eq_two_nsmul`. The parameter of each factor
is `t ^ i * u ^ j` for the root `i α + j β` it belongs to; in particular the last factor has the
parameter `t ^ 3 * u ^ 2`, which is what makes this case not a chain in `ad x` alone. The one
remaining type-`G₂` configuration, the pair `α`, `α + β`, is not treated here; see
`TauCeti.RingTheory.DividedPowers.RootString.G2` for what it needs instead.

Nothing here divides by a factorial in `R`, so the relation holds over a ring of arbitrary
characteristic. The whole point is the coefficient-one straightening rule
`TauCeti.Associative.dividedPower_mul_dividedPower_of_commutator_eq_three_nsmul`; the exponential
identity is its generating-function form, and the parameters `u`, `t * u`, `t ^ 2 * u`, `t ^ 3 * u`,
`t ^ 3 * u ^ 2`, `t` are exactly the six monomials into which `t ^ m u ^ n` factors.

## Main results

* `TauCeti.integralDividedPower_mul_integralDividedPower_of_commutator_eq_three_nsmul`: the
  straightening rule for the integral operators restricted to `M`.
* `TauCeti.baseChangeExp_mul_baseChangeExp_of_commutator_eq_three_nsmul`: the Chevalley commutator
  relation in type `G₂`.
* `TauCeti.baseChangeExp_conj_of_commutator_eq_three_nsmul`: its conjugation form.

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

/-- **Straightening restricted divided powers in type `G₂`.** The type-`G₂` straightening rule
transported to the integral operators obtained by restricting divided powers to a stable additive
subgroup. -/
theorem integralDividedPower_mul_integralDividedPower_of_commutator_eq_three_nsmul
    {x y z w v s : A} (M : S) (hxy : x * y = y * x + z) (hxz : x * z = z * x + 2 • w)
    (hxw : x * w = w * x + 3 • v) (hwz : w * z = z * w + 3 • s) (hxv : Commute x v)
    (hxs : Commute x s) (hyz : Commute y z) (hwv : Commute w v) (hzs : Commute z s)
    (hws : Commute w s) (hvs : Commute v s)
    (hMx : ∀ n, ∀ a ∈ M, Associative.dividedPower n x • a ∈ M)
    (hMy : ∀ n, ∀ a ∈ M, Associative.dividedPower n y • a ∈ M)
    (hMz : ∀ n, ∀ a ∈ M, Associative.dividedPower n z • a ∈ M)
    (hMw : ∀ n, ∀ a ∈ M, Associative.dividedPower n w • a ∈ M)
    (hMv : ∀ n, ∀ a ∈ M, Associative.dividedPower n v • a ∈ M)
    (hMs : ∀ n, ∀ a ∈ M, Associative.dividedPower n s • a ∈ M)
    (m n : ℕ) :
    integralDividedPower x M m (hMx m) * integralDividedPower y M n (hMy n) =
      ∑ p ∈ Associative.chainG2Index m n,
        integralDividedPower y M (n - p.1 - p.2.1 - p.2.2.1 - 2 * p.2.2.2)
            (hMy (n - p.1 - p.2.1 - p.2.2.1 - 2 * p.2.2.2)) *
          integralDividedPower z M p.1 (hMz p.1) *
          integralDividedPower w M p.2.1 (hMw p.2.1) *
          integralDividedPower v M p.2.2.1 (hMv p.2.2.1) *
          integralDividedPower s M p.2.2.2 (hMs p.2.2.2) *
          integralDividedPower x M (m - p.1 - 2 * p.2.1 - 3 * p.2.2.1 - 3 * p.2.2.2)
            (hMx (m - p.1 - 2 * p.2.1 - 3 * p.2.2.1 - 3 * p.2.2.2)) := by
  ext a
  simp only [Module.End.mul_apply, LinearMap.sum_apply, AddSubmonoidClass.coe_finsetSum,
    coe_integralDividedPower_apply, ← mul_smul, ← Finset.sum_smul]
  congr 1
  simpa only [mul_assoc] using
    Associative.dividedPower_mul_dividedPower_of_commutator_eq_three_nsmul
      hxy hxz hxw hwz hxv hxs hyz hwv hzs hws hvs m n

/-! ## The generating-function form of the straightening rule -/

-- The combinatorial core: a truncated left factor times a truncated right factor is the reordered
-- sextuple product, once the truncation is wide enough that the reindexed hypercube contains no
-- extra nonzero terms. The reindexing is
-- `(m, n, b, c, d, e) ↦ (n - b - c - d - 2e, b, c, d, e, m - b - 2c - 3d - 3e)`, and the monomial
-- `t ^ m u ^ n` factors accordingly as
-- `u ^ a (t u) ^ b (t ^ 2 u) ^ c (t ^ 3 u) ^ d (t ^ 3 u ^ 2) ^ e t ^ q`.
-- The proof is the six-factor analogue of the argument in
-- `TauCeti.RingTheory.Nilpotent.RootString.Basic`, and follows it step for step.
private theorem sum_smul_mul_sum_smul_of_chainG2Order {R : Type*} [CommRing R]
    {B : Type*} [Ring B] [Algebra R B] (Dx Dy Dz Dw Dv Ds : ℕ → B) (N : ℕ)
    (hno : ∀ m n, Dx m * Dy n =
      ∑ p ∈ Associative.chainG2Index m n,
        Dy (n - p.1 - p.2.1 - p.2.2.1 - 2 * p.2.2.2) * Dz p.1 * Dw p.2.1 * Dv p.2.2.1 *
          Ds p.2.2.2 * Dx (m - p.1 - 2 * p.2.1 - 3 * p.2.2.1 - 3 * p.2.2.2))
    (hzero : ∀ a b c d e q : ℕ,
      N ≤ a + b + c + d + 2 * e ∨ N ≤ q + b + 2 * c + 3 * d + 3 * e →
      Dy a * Dz b * Dw c * Dv d * Ds e * Dx q = 0)
    (t u : R) :
    (∑ m ∈ range N, t ^ m • Dx m) * (∑ n ∈ range N, u ^ n • Dy n) =
      (∑ a ∈ range N, u ^ a • Dy a) * (∑ b ∈ range N, (t * u) ^ b • Dz b) *
        (∑ c ∈ range N, (t ^ 2 * u) ^ c • Dw c) * (∑ d ∈ range N, (t ^ 3 * u) ^ d • Dv d) *
        (∑ e ∈ range N, (t ^ 3 * u ^ 2) ^ e • Ds e) * (∑ q ∈ range N, t ^ q • Dx q) := by
  classical
  set G : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ → B := fun w =>
    (u ^ w.1 * (t * u) ^ w.2.1 * (t ^ 2 * u) ^ w.2.2.1 * (t ^ 3 * u) ^ w.2.2.2.1 *
        (t ^ 3 * u ^ 2) ^ w.2.2.2.2.1 * t ^ w.2.2.2.2.2) •
      (Dy w.1 * Dz w.2.1 * Dw w.2.2.1 * Dv w.2.2.2.1 * Ds w.2.2.2.2.1 * Dx w.2.2.2.2.2) with hG
  -- Step 1: expand the reordered product over the full hypercube of indices.
  have hbox : ∑ w ∈ range N ×ˢ range N ×ˢ range N ×ˢ range N ×ˢ range N ×ˢ range N, G w =
      (∑ a ∈ range N, u ^ a • Dy a) * (∑ b ∈ range N, (t * u) ^ b • Dz b) *
        (∑ c ∈ range N, (t ^ 2 * u) ^ c • Dw c) * (∑ d ∈ range N, (t ^ 3 * u) ^ d • Dv d) *
        (∑ e ∈ range N, (t ^ 3 * u ^ 2) ^ e • Ds e) * (∑ q ∈ range N, t ^ q • Dx q) := by
    rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc, Finset.sum_mul_sum, Finset.sum_mul_sum,
      Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_mul_sum]
    simp only [hG, Finset.sum_product, Finset.mul_sum, smul_mul_smul_comm, mul_assoc]
  -- Step 2: expand the original product over the reindexing domain.
  have hsrc : ∑ w ∈ (range N ×ˢ range N).sigma
        (fun mn => Associative.chainG2Index mn.1 mn.2),
        (t ^ w.1.1 * u ^ w.1.2) •
          (Dy (w.1.2 - w.2.1 - w.2.2.1 - w.2.2.2.1 - 2 * w.2.2.2.2) * Dz w.2.1 * Dw w.2.2.1 *
            Dv w.2.2.2.1 * Ds w.2.2.2.2 *
            Dx (w.1.1 - w.2.1 - 2 * w.2.2.1 - 3 * w.2.2.2.1 - 3 * w.2.2.2.2)) =
      (∑ m ∈ range N, t ^ m • Dx m) * (∑ n ∈ range N, u ^ n • Dy n) := by
    rw [Finset.sum_sigma, Finset.sum_mul_sum]
    simp only [Finset.sum_product, smul_mul_smul_comm, hno, Finset.smul_sum]
  -- Step 3: the reindexing itself, onto the part of the hypercube it covers.
  have hbij : ∑ w ∈ (range N ×ˢ range N).sigma
        (fun mn => Associative.chainG2Index mn.1 mn.2),
        (t ^ w.1.1 * u ^ w.1.2) •
          (Dy (w.1.2 - w.2.1 - w.2.2.1 - w.2.2.2.1 - 2 * w.2.2.2.2) * Dz w.2.1 * Dw w.2.2.1 *
            Dv w.2.2.2.1 * Ds w.2.2.2.2 *
            Dx (w.1.1 - w.2.1 - 2 * w.2.2.1 - 3 * w.2.2.2.1 - 3 * w.2.2.2.2)) =
      ∑ w ∈ range N ×ˢ range N ×ˢ range N ×ˢ range N ×ˢ range N ×ˢ range N with
        w.1 + w.2.1 + w.2.2.1 + w.2.2.2.1 + 2 * w.2.2.2.2.1 < N ∧
          w.2.2.2.2.2 + w.2.1 + 2 * w.2.2.1 + 3 * w.2.2.2.1 + 3 * w.2.2.2.2.1 < N, G w := by
    refine Finset.sum_nbij'
      (fun w => (w.1.2 - w.2.1 - w.2.2.1 - w.2.2.2.1 - 2 * w.2.2.2.2, w.2.1, w.2.2.1, w.2.2.2.1,
        w.2.2.2.2, w.1.1 - w.2.1 - 2 * w.2.2.1 - 3 * w.2.2.2.1 - 3 * w.2.2.2.2))
      (fun w => ⟨(w.2.2.2.2.2 + w.2.1 + 2 * w.2.2.1 + 3 * w.2.2.2.1 + 3 * w.2.2.2.2.1,
        w.1 + w.2.1 + w.2.2.1 + w.2.2.2.1 + 2 * w.2.2.2.2.1),
        (w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2.1)⟩) ?_ ?_ ?_ ?_ ?_
    · rintro ⟨⟨m, n⟩, b, c, d, e⟩ hw
      simp only [Finset.mem_sigma, Finset.mem_product, Finset.mem_range,
        Associative.mem_chainG2Index] at hw
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      omega
    · rintro ⟨a, b, c, d, e, q⟩ hw
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hw
      simp only [Finset.mem_sigma, Finset.mem_product, Finset.mem_range,
        Associative.mem_chainG2Index]
      omega
    · rintro ⟨⟨m, n⟩, b, c, d, e⟩ hw
      obtain ⟨h1, h2⟩ := Associative.mem_chainG2Index.mp (Finset.mem_sigma.mp hw).2
      have hbn : b + c + d + 2 * e ≤ n := h1
      have hbm : b + 2 * c + 3 * d + 3 * e ≤ m := h2
      have e1 : m - b - 2 * c - 3 * d - 3 * e + b + 2 * c + 3 * d + 3 * e = m := by omega
      have e2 : n - b - c - d - 2 * e + b + c + d + 2 * e = n := by omega
      simp [e1, e2]
    · rintro ⟨a, b, c, d, e, q⟩ _
      have e1 : a + b + c + d + 2 * e - b - c - d - 2 * e = a := by omega
      have e2 : q + b + 2 * c + 3 * d + 3 * e - b - 2 * c - 3 * d - 3 * e = q := by omega
      simp [e1, e2]
    · rintro ⟨⟨m, n⟩, b, c, d, e⟩ hw
      simp only [Finset.mem_sigma, Finset.mem_product, Finset.mem_range,
        Associative.mem_chainG2Index] at hw
      obtain ⟨a, rfl⟩ : ∃ a, n = a + (b + c + d + 2 * e) := ⟨n - b - c - d - 2 * e, by omega⟩
      obtain ⟨q, rfl⟩ : ∃ q, m = q + (b + 2 * c + 3 * d + 3 * e) :=
        ⟨m - b - 2 * c - 3 * d - 3 * e, by omega⟩
      have h1 : a + (b + c + d + 2 * e) - b - c - d - 2 * e = a := by omega
      have h2 : q + (b + 2 * c + 3 * d + 3 * e) - b - 2 * c - 3 * d - 3 * e = q := by omega
      simp only [hG, h1, h2]
      congr 1
      simp only [mul_pow, pow_add, pow_mul]
      ring
  -- Step 4: the terms of the hypercube outside that part vanish.
  have hsub : ∑ w ∈ range N ×ˢ range N ×ˢ range N ×ˢ range N ×ˢ range N ×ˢ range N with
        w.1 + w.2.1 + w.2.2.1 + w.2.2.2.1 + 2 * w.2.2.2.2.1 < N ∧
          w.2.2.2.2.2 + w.2.1 + 2 * w.2.2.1 + 3 * w.2.2.2.1 + 3 * w.2.2.2.2.1 < N, G w =
      ∑ w ∈ range N ×ˢ range N ×ˢ range N ×ˢ range N ×ˢ range N ×ˢ range N, G w := by
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    rintro ⟨a, b, c, d, e, q⟩ hmem hnot
    simp only [Finset.mem_product, Finset.mem_range] at hmem
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hnot
    have hor : N ≤ a + b + c + d + 2 * e ∨ N ≤ q + b + 2 * c + 3 * d + 3 * e := by omega
    simp [hG, hzero a b c d e q hor]
  rw [← hsrc, hbij, hsub, hbox]

/-! ## The Chevalley commutator relation -/

section Commutator

variable {R : Type v} [CommRing R] [Algebra ℤ R]

-- Match tensor products to the module structure carried by the explicit `ℤ`-algebra.
attribute [local instance high] Algebra.toModule

/-- **The Chevalley commutator relation in type `G₂`.** If

```text
x * y = y * x + z,   x * z = z * x + 2 • w,   x * w = w * x + 3 • v,   w * z = z * w + 3 • s,
```

with `v` and `s` commuting with `x`, `y` commuting with `z`, `w` commuting with `v`, and `s`
commuting with `z`, `w`, and `v`, then over every commutative ring `R` the integral divided-power
exponentials on `R ⊗[ℤ] M` satisfy

```text
E_x(t) E_y(u) = E_y(u) E_z(t * u) E_w(t ^ 2 * u) E_v(t ^ 3 * u) E_s(t ^ 3 * u ^ 2) E_x(t).
```

No factorial is inverted in `R`: the relation holds in every characteristic. -/
theorem baseChangeExp_mul_baseChangeExp_of_commutator_eq_three_nsmul
    {x y z w v s : A} (M : S) (hxy : x * y = y * x + z) (hxz : x * z = z * x + 2 • w)
    (hxw : x * w = w * x + 3 • v) (hwz : w * z = z * w + 3 • s) (hxv : Commute x v)
    (hxs : Commute x s) (hyz : Commute y z) (hwv : Commute w v) (hzs : Commute z s)
    (hws : Commute w s) (hvs : Commute v s)
    (hx : IsNilpotent x) (hy : IsNilpotent y) (hz : IsNilpotent z) (hw : IsNilpotent w)
    (hMx : ∀ n, ∀ a ∈ M, Associative.dividedPower n x • a ∈ M)
    (hMy : ∀ n, ∀ a ∈ M, Associative.dividedPower n y • a ∈ M)
    (hMz : ∀ n, ∀ a ∈ M, Associative.dividedPower n z • a ∈ M)
    (hMw : ∀ n, ∀ a ∈ M, Associative.dividedPower n w • a ∈ M)
    (hMv : ∀ n, ∀ a ∈ M, Associative.dividedPower n v • a ∈ M)
    (hMs : ∀ n, ∀ a ∈ M, Associative.dividedPower n s • a ∈ M)
    (t u : R) :
    baseChangeExp x M hMx t * baseChangeExp y M hMy u =
      baseChangeExp y M hMy u * baseChangeExp z M hMz (t * u) *
        baseChangeExp w M hMw (t ^ 2 * u) * baseChangeExp v M hMv (t ^ 3 * u) *
        baseChangeExp s M hMs (t ^ 3 * u ^ 2) * baseChangeExp x M hMx t := by
  classical
  obtain ⟨kx, hkx⟩ := hx
  obtain ⟨ky, hky⟩ := hy
  obtain ⟨kz, hkz⟩ := hz
  obtain ⟨kw, hkw⟩ := hw
  obtain ⟨kv, hkv⟩ := Associative.isNilpotent_of_commutator_eq_nsmul (by decide)
    hxw hxv hwv ⟨kx, hkx⟩
  obtain ⟨ks, hks⟩ := Associative.isNilpotent_of_commutator_eq_nsmul (by decide)
    hwz hws hzs ⟨kw, hkw⟩
  set N := kx + ky + kz + 2 * kw + 3 * kv + 3 * ks with hNdef
  have hxN : x ^ N = 0 := pow_eq_zero_of_le (by omega) hkx
  have hyN : y ^ N = 0 := pow_eq_zero_of_le (by omega) hky
  have hzN : z ^ N = 0 := pow_eq_zero_of_le (by omega) hkz
  have hwN : w ^ N = 0 := pow_eq_zero_of_le (by omega) hkw
  have hvN : v ^ N = 0 := pow_eq_zero_of_le (by omega) hkv
  have hsN : s ^ N = 0 := pow_eq_zero_of_le (by omega) hks
  rw [baseChangeExp_of_pow_eq_zero x M hMx hxN, baseChangeExp_of_pow_eq_zero y M hMy hyN,
    baseChangeExp_of_pow_eq_zero z M hMz hzN, baseChangeExp_of_pow_eq_zero w M hMw hwN,
    baseChangeExp_of_pow_eq_zero v M hMv hvN, baseChangeExp_of_pow_eq_zero s M hMs hsN]
  refine sum_smul_mul_sum_smul_of_chainG2Order (R := R)
    (fun n => (integralDividedPower x M n (hMx n)).baseChange R)
    (fun n => (integralDividedPower y M n (hMy n)).baseChange R)
    (fun n => (integralDividedPower z M n (hMz n)).baseChange R)
    (fun n => (integralDividedPower w M n (hMw n)).baseChange R)
    (fun n => (integralDividedPower v M n (hMv n)).baseChange R)
    (fun n => (integralDividedPower s M n (hMs n)).baseChange R) N ?_ ?_ t u
  · intro m n
    have h := congrArg (fun f : Module.End ℤ M => (Module.End.baseChangeHom ℤ R M) f)
      (integralDividedPower_mul_integralDividedPower_of_commutator_eq_three_nsmul
        M hxy hxz hxw hwz hxv hxs hyz hwv hzs hws hvs hMx hMy hMz hMw hMv hMs m n)
    simp only [map_mul, map_sum] at h
    exact h
  · -- Outside the truncation the reordered sextuple has a vanishing factor.
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
    have hvv : ∀ d, kv ≤ d → (integralDividedPower v M d (hMv d)).baseChange R = 0 := by
      intro d hd
      rw [integralDividedPower_eq_zero_of_le v M d (hMv d) hkv hd, LinearMap.baseChange_zero]
    have hvs' : ∀ e, ks ≤ e → (integralDividedPower s M e (hMs e)).baseChange R = 0 := by
      intro e he
      rw [integralDividedPower_eq_zero_of_le s M e (hMs e) hks he, LinearMap.baseChange_zero]
    rintro a b c d e q (habc | hqbc)
    · rcases le_or_gt ky a with ha | ha
      · simp [hvy a ha]
      · rcases le_or_gt kz b with hb | hb
        · simp [hvz b hb]
        · rcases le_or_gt kw c with hc | hc
          · simp [hvw c hc]
          · rcases le_or_gt kv d with hd | hd
            · simp [hvv d hd]
            · simp [hvs' e (by omega)]
    · rcases le_or_gt kx q with hq | hq
      · simp [hvx q hq]
      · rcases le_or_gt kz b with hb | hb
        · simp [hvz b hb]
        · rcases le_or_gt kw c with hc | hc
          · simp [hvw c hc]
          · rcases le_or_gt kv d with hd | hd
            · simp [hvv d hd]
            · simp [hvs' e (by omega)]

/-- The conjugation form of the Chevalley commutator relation in type `G₂`: conjugating the
one-parameter subgroup of `y` by that of `x` multiplies it by the one-parameter subgroups of `z`,
`w`, `v`, and `s`, at the parameters `t * u`, `t ^ 2 * u`, `t ^ 3 * u`, and `t ^ 3 * u ^ 2`. -/
theorem baseChangeExp_conj_of_commutator_eq_three_nsmul
    {x y z w v s : A} (M : S) (hxy : x * y = y * x + z) (hxz : x * z = z * x + 2 • w)
    (hxw : x * w = w * x + 3 • v) (hwz : w * z = z * w + 3 • s) (hxv : Commute x v)
    (hxs : Commute x s) (hyz : Commute y z) (hwv : Commute w v) (hzs : Commute z s)
    (hws : Commute w s) (hvs : Commute v s)
    (hx : IsNilpotent x) (hy : IsNilpotent y) (hz : IsNilpotent z) (hw : IsNilpotent w)
    (hMx : ∀ n, ∀ a ∈ M, Associative.dividedPower n x • a ∈ M)
    (hMy : ∀ n, ∀ a ∈ M, Associative.dividedPower n y • a ∈ M)
    (hMz : ∀ n, ∀ a ∈ M, Associative.dividedPower n z • a ∈ M)
    (hMw : ∀ n, ∀ a ∈ M, Associative.dividedPower n w • a ∈ M)
    (hMv : ∀ n, ∀ a ∈ M, Associative.dividedPower n v • a ∈ M)
    (hMs : ∀ n, ∀ a ∈ M, Associative.dividedPower n s • a ∈ M)
    (t u : R) :
    baseChangeExp x M hMx t * baseChangeExp y M hMy u * baseChangeExp x M hMx (-t) =
      baseChangeExp y M hMy u * baseChangeExp z M hMz (t * u) *
        baseChangeExp w M hMw (t ^ 2 * u) * baseChangeExp v M hMv (t ^ 3 * u) *
        baseChangeExp s M hMs (t ^ 3 * u ^ 2) := by
  rw [baseChangeExp_mul_baseChangeExp_of_commutator_eq_three_nsmul M hxy hxz hxw hwz hxv hxs hyz
      hwv hzs hws hvs hx hy hz hw hMx hMy hMz hMw hMv hMs t u,
    mul_assoc, ← baseChangeExp_add x M hMx hx t (-t), add_neg_cancel,
    baseChangeExp_zero x M hMx hx, mul_one]

end Commutator

end TauCeti

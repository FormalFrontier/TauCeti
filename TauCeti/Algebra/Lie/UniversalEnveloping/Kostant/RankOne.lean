/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Lie.Sl2
public import TauCeti.Algebra.Lie.UniversalEnveloping.Commutation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing

/-!
# Rank-one straightening in a universal enveloping algebra

This file proves the first divided-power straightening laws for an `sl₂` triple `(h, e, f)`.
Inside its universal enveloping algebra they read

```text
e⁽ⁿ⁺¹⁾ f = f e⁽ⁿ⁺¹⁾ + e⁽ⁿ⁾ (h + n),
e f⁽ⁿ⁺¹⁾ = f⁽ⁿ⁺¹⁾ e + f⁽ⁿ⁾ (h - n).
```

These are the one-sided cases of the rank-one Kostant straightening formula.  Unlike the
central-commutator formula, the commutator here is `h`, which does not commute with either root
vector.  The integral coefficients are the point: after passing from powers to divided powers no
denominators remain.

The full formula for `e⁽ᵐ⁾ f⁽ⁿ⁾` is obtained by iterating these identities and combining adjacent
Cartan binomial coefficients.  It is a prerequisite for the integral PBW theorem for the Kostant
form used in the Chevalley--Demazure construction.

## Main results

* `IsSl2Triple.dividedPower_e_mul_f`: move `f` to the left of a divided power of `e`.
* `IsSl2Triple.dividedPower_e_mul_f_cartan_left`: the same formula with its Cartan factor before
  the remaining `e`-power.
* `IsSl2Triple.e_mul_dividedPower_f`: move `e` to the right of a divided power of `f`.
* `IsSl2Triple.e_mul_dividedPower_f_cartan_left`: the corresponding Cartan-left form.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.2.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

universe u

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]

local notation "U" => _root_.UniversalEnvelopingAlgebra ℚ L
local notation "ι" => _root_.UniversalEnvelopingAlgebra.ι ℚ

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] TauCeti.moduleNNRat

private theorem ι_mul_ι_eq_ι_mul_ι_add_of_lie_eq {x y z : L} (hxy : ⁅x, y⁆ = z) :
    ι x * ι y = ι y * ι x + ι z := by
  have hmap := LieHom.map_lie ι x y
  rw [hxy, LieRing.of_associative_ring_bracket] at hmap
  simpa [add_comm] using (sub_eq_iff_eq_add.mp hmap.symm)

private theorem pow_succ_e_mul_f {h e f : L} (t : IsSl2Triple h e f) (n : ℕ) :
    ι e ^ (n + 1) * ι f =
      ι f * ι e ^ (n + 1) +
        (n + 1) • (ι e ^ n * (ι h + n • (1 : U))) := by
  induction n with
  | zero => simpa using ι_mul_ι_eq_ι_mul_ι_add_of_lie_eq t.lie_e_f
  | succ n ih =>
      have hhe : ι h * ι e = ι e * (ι h + 2 • (1 : U)) :=
        ι_mul_ι_eq_ι_mul_ι_add_zsmul_one (z := 2) (by
          exact_mod_cast t.lie_h_e_nsmul)
      have hcomm : ι h * ι e - ι e * ι h = (2 : ℤ) • ι e := by
        noncomm_ring [hhe]
      have hhePow := Associative.mul_pow_eq_pow_mul_add_zsmul hcomm (n + 1)
      have hhePowNat :
          ι h * ι e ^ (n + 1) =
            ι e ^ (n + 1) * ι h + (2 * (n + 1)) • ι e ^ (n + 1) := by
        convert hhePow using 1
        norm_num [mul_comm]
      have hp : ι e ^ (n + 1 + 1) = ι e * ι e ^ (n + 1) := by rw [pow_succ']
      rw [hp, mul_assoc, ih, mul_add,
        ← mul_assoc (ι e) (ι f), ι_mul_ι_eq_ι_mul_ι_add_of_lie_eq t.lie_e_f, add_mul]
      simp only [pow_succ'] at hhePowNat ⊢
      rw [hhePowNat]
      simp only [mul_assoc, mul_add, mul_one]
      simp_rw [← Nat.cast_smul_eq_nsmul ℚ]
      simp only [mul_smul_comm, mul_add, mul_one]
      module

/-- Moving the lowering vector across a divided power of the raising vector in an `sl₂` triple:
`e⁽ⁿ⁺¹⁾ f = f e⁽ⁿ⁺¹⁾ + e⁽ⁿ⁾ (h + n)`. -/
theorem IsSl2Triple.dividedPower_e_mul_f {h e f : L} (t : IsSl2Triple h e f) (n : ℕ) :
    Associative.dividedPower (n + 1) (ι e) * ι f =
      ι f * Associative.dividedPower (n + 1) (ι e) +
        Associative.dividedPower n (ι e) * (ι h + n • (1 : U)) := by
  rw [Associative.dividedPower_def, Associative.dividedPower_def, smul_mul_assoc,
    mul_smul_comm, pow_succ_e_mul_f t n, smul_add]
  congr 1
  simp_rw [← Nat.cast_smul_eq_nsmul ℚ]
  rw [smul_smul, smul_mul_assoc]
  congr 1
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp

/-- The Cartan-left normal form of `IsSl2Triple.dividedPower_e_mul_f`:
`e⁽ⁿ⁺¹⁾ f = f e⁽ⁿ⁺¹⁾ + (h - n) e⁽ⁿ⁾`.  This is the orientation that occurs as the
one-lowering-vector case of the full Kostant straightening formula. -/
theorem IsSl2Triple.dividedPower_e_mul_f_cartan_left {h e f : L}
    (t : IsSl2Triple h e f) (n : ℕ) :
    Associative.dividedPower (n + 1) (ι e) * ι f =
      ι f * Associative.dividedPower (n + 1) (ι e) +
        (ι h - n • (1 : U)) * Associative.dividedPower n (ι e) := by
  rw [dividedPower_e_mul_f t n]
  have hhe : ι h * ι e = ι e * (ι h + 2 • (1 : U)) :=
    ι_mul_ι_eq_ι_mul_ι_add_zsmul_one (z := 2) (by
      exact_mod_cast t.lie_h_e_nsmul)
  have hcomm : ι h * ι e - ι e * ι h = (2 : ℤ) • ι e := by
    noncomm_ring [hhe]
  have hmove := Associative.mul_dividedPower_eq_dividedPower_mul_add_zsmul hcomm n
  have hmoveNat :
      ι h * Associative.dividedPower n (ι e) =
        Associative.dividedPower n (ι e) * ι h +
          (2 * n) • Associative.dividedPower n (ι e) := by
    convert hmove using 1
    norm_num [mul_comm]
  simp only [sub_mul, mul_add]
  rw [hmoveNat]
  simp_rw [← Nat.cast_smul_eq_nsmul ℚ]
  simp only [smul_mul_assoc, mul_smul_comm, one_mul]
  simp only [mul_one]
  module

/-- Moving the raising vector across a divided power of the lowering vector in an `sl₂` triple:
`e f⁽ⁿ⁺¹⁾ = f⁽ⁿ⁺¹⁾ e + f⁽ⁿ⁾ (h - n)`. -/
theorem IsSl2Triple.e_mul_dividedPower_f {h e f : L} (t : IsSl2Triple h e f) (n : ℕ) :
    ι e * Associative.dividedPower (n + 1) (ι f) =
      Associative.dividedPower (n + 1) (ι f) * ι e +
        Associative.dividedPower n (ι f) * (ι h - n • (1 : U)) := by
  have hs := dividedPower_e_mul_f t.symm n
  rw [map_neg] at hs
  noncomm_ring [hs]

/-- The Cartan-left companion of `IsSl2Triple.e_mul_dividedPower_f`:
`e f⁽ⁿ⁺¹⁾ = f⁽ⁿ⁺¹⁾ e + (h + n) f⁽ⁿ⁾`. -/
theorem IsSl2Triple.e_mul_dividedPower_f_cartan_left {h e f : L}
    (t : IsSl2Triple h e f) (n : ℕ) :
    ι e * Associative.dividedPower (n + 1) (ι f) =
      Associative.dividedPower (n + 1) (ι f) * ι e +
        (ι h + n • (1 : U)) * Associative.dividedPower n (ι f) := by
  have hs := dividedPower_e_mul_f_cartan_left t.symm n
  rw [map_neg] at hs
  noncomm_ring [hs]

end TauCeti.UniversalEnvelopingAlgebra

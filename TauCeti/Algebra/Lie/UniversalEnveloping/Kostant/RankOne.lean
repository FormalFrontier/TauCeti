/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Lie.Sl2
public import TauCeti.Algebra.Lie.Sl2.Associative
import Mathlib.Tactic.NoncommRing

/-!
# Rank-one straightening in a universal enveloping algebra

This file gives Cartan-left forms of the first divided-power straightening laws for an `sl₂`
triple `(h, e, f)`. Inside its universal enveloping algebra they read

```text
e⁽ⁿ⁺¹⁾ f = f e⁽ⁿ⁺¹⁾ + (h - n) e⁽ⁿ⁾,
e f⁽ⁿ⁺¹⁾ = f⁽ⁿ⁺¹⁾ e + (h + n) f⁽ⁿ⁾.
```

The corresponding forms with the Cartan factor on the right are proved in
`TauCeti.Algebra.Lie.Sl2.Associative`. These are the one-sided cases of the rank-one Kostant
straightening formula. The integral coefficients are the point: after passing from powers to
divided powers no denominators remain.

The full formula for `e⁽ᵐ⁾ f⁽ⁿ⁾` is obtained by iterating these identities and combining adjacent
Cartan binomial coefficients.  It is a prerequisite for the integral PBW theorem for the Kostant
form used in the Chevalley--Demazure construction.

## Main results

* `IsSl2Triple.dividedPower_e_mul_f_cartan_left`: the same formula with its Cartan factor before
  the remaining `e`-power.
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

/-- The Cartan-left normal form of `TauCeti.Sl2.ι_f_mul_dividedPower_succ_ι_e`:
`e⁽ⁿ⁺¹⁾ f = f e⁽ⁿ⁺¹⁾ + (h - n) e⁽ⁿ⁾`.  This is the orientation that occurs as the
one-lowering-vector case of the full Kostant straightening formula. -/
theorem IsSl2Triple.dividedPower_e_mul_f_cartan_left {h e f : L}
    (t : IsSl2Triple h e f) (n : ℕ) :
    Associative.dividedPower (n + 1) (ι e) * ι f =
      ι f * Associative.dividedPower (n + 1) (ι e) +
        (ι h - n • (1 : U)) * Associative.dividedPower n (ι e) := by
  have hs :=
    TauCeti.Sl2.ι_f_mul_dividedPower_succ_ι_e t.lie_e_f t.lie_h_e_nsmul n
  have hright := (eq_sub_iff_add_eq.mp hs).symm
  rw [hright]
  congr 1
  have hhe : ι h * ι e - ι e * ι h = (2 : ℤ) • ι e := by
    simpa only [LieRing.of_associative_ring_bracket, t.lie_h_e_nsmul, map_nsmul,
      ofNat_zsmul] using (LieHom.map_lie ι h e).symm
  have hmove := Associative.mul_dividedPower_eq_dividedPower_mul_add_zsmul hhe n
  have hmoveNat :
      ι h * Associative.dividedPower n (ι e) =
        Associative.dividedPower n (ι e) * ι h +
          (2 * n) • Associative.dividedPower n (ι e) := by
    convert hmove using 1
    norm_num [mul_comm]
  simp only [sub_mul, mul_add]
  rw [hmoveNat]
  simp_rw [← Nat.cast_smul_eq_nsmul ℚ]
  simp only [smul_mul_assoc, one_mul]
  rw [← (Nat.cast_commute n (Associative.dividedPower n (ι e))).eq]
  simp only [Algebra.smul_def, map_natCast]
  push_cast
  noncomm_ring

/-- The Cartan-left normal form of `TauCeti.Sl2.ι_e_mul_dividedPower_succ_ι_f`:
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

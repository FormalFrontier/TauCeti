/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Form
public import TauCeti.RingTheory.DividedPowers.Commutation

/-!
# Cartan and root-vector commutation in a Kostant form

Let `h` and `x` be elements of a Lie algebra over `ℚ` satisfying

```text
[h, x] = z x,     z : ℤ.
```

Inside the universal enveloping algebra this becomes `h x = x (h + z)`.  The generic
binomial/divided-power reordering identities therefore give

```text
(h choose m) x⁽ⁿ⁾ = x⁽ⁿ⁾ (h + n z choose m),
x⁽ⁿ⁾ (h choose m) = (h - n z choose m) x⁽ⁿ⁾.
```

Here an integer such as `n z` denotes that integer times the unit of the enveloping algebra.
For the Chevalley generators, `z` is the integral Cartan integer pairing a simple coroot with a
root.  These formulas are the Cartan/root-vector part of normal ordering the generators of the
Kostant integral form; the root/root part requires the separate root-string formulas.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.ringChoose_ι_mul_dividedPower_ι`: move a Cartan binomial
  coefficient to the right of a root-vector divided power.
* `TauCeti.UniversalEnvelopingAlgebra.dividedPower_ι_mul_ringChoose_ι`: the reverse reordering.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.2.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

universe u

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]

local notation "U" => _root_.UniversalEnvelopingAlgebra ℚ L

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The nonnegative-rational scalar action supplying the `BinomialRing` instance for
`Ring.choose` on the universal enveloping algebra. -/
noncomputable local instance moduleNNRatCommutation : Module ℚ≥0 U :=
  Module.compHom _ (algebraMap ℚ≥0 ℚ)

/-- The associative-ring form of an integral weight relation in a Lie algebra. -/
private theorem mul_ι_eq_ι_mul_add_zsmul_one {h x : L} {z : ℤ} (hz : ⁅h, x⁆ = z • x) :
    _root_.UniversalEnvelopingAlgebra.ι ℚ h *
        _root_.UniversalEnvelopingAlgebra.ι ℚ x =
      _root_.UniversalEnvelopingAlgebra.ι ℚ x *
        (_root_.UniversalEnvelopingAlgebra.ι ℚ h + z • (1 : U)) := by
  have hmap := LieHom.map_lie (_root_.UniversalEnvelopingAlgebra.ι ℚ) h x
  rw [hz, map_zsmul, LieRing.of_associative_ring_bracket] at hmap
  have hzmul : z • _root_.UniversalEnvelopingAlgebra.ι ℚ x =
      _root_.UniversalEnvelopingAlgebra.ι ℚ x * (z • (1 : U)) := by
    simp only [zsmul_eq_mul, mul_one]
    exact (Int.cast_commute z (_root_.UniversalEnvelopingAlgebra.ι ℚ x)).eq
  calc
    _root_.UniversalEnvelopingAlgebra.ι ℚ h *
        _root_.UniversalEnvelopingAlgebra.ι ℚ x =
        z • _root_.UniversalEnvelopingAlgebra.ι ℚ x +
          _root_.UniversalEnvelopingAlgebra.ι ℚ x *
            _root_.UniversalEnvelopingAlgebra.ι ℚ h :=
      eq_add_of_sub_eq hmap.symm
    _ = _root_.UniversalEnvelopingAlgebra.ι ℚ x *
          _root_.UniversalEnvelopingAlgebra.ι ℚ h +
        _root_.UniversalEnvelopingAlgebra.ι ℚ x * (z • (1 : U)) := by
      rw [hzmul, add_comm]
    _ = _root_.UniversalEnvelopingAlgebra.ι ℚ x *
        (_root_.UniversalEnvelopingAlgebra.ι ℚ h + z • (1 : U)) :=
      (mul_add _ _ _).symm

/-- A Cartan binomial coefficient moves to the right of a root-vector divided power by adding
`n` copies of the integral weight to its argument. -/
theorem ringChoose_ι_mul_dividedPower_ι {h x : L} {z : ℤ} (hz : ⁅h, x⁆ = z • x)
    (m n : ℕ) :
    Ring.choose (_root_.UniversalEnvelopingAlgebra.ι ℚ h) m *
        Associative.dividedPower n (_root_.UniversalEnvelopingAlgebra.ι ℚ x) =
      Associative.dividedPower n (_root_.UniversalEnvelopingAlgebra.ι ℚ x) *
        Ring.choose
          (_root_.UniversalEnvelopingAlgebra.ι ℚ h + n • (z • (1 : U))) m :=
  ringChoose_mul_dividedPower_eq m (mul_ι_eq_ι_mul_add_zsmul_one hz)
    ((Commute.one_left _).smul_left z) n

/-- A Cartan binomial coefficient moves to the left of a root-vector divided power by subtracting
`n` copies of the integral weight from its argument. -/
theorem dividedPower_ι_mul_ringChoose_ι {h x : L} {z : ℤ} (hz : ⁅h, x⁆ = z • x)
    (m n : ℕ) :
    Associative.dividedPower n (_root_.UniversalEnvelopingAlgebra.ι ℚ x) *
        Ring.choose (_root_.UniversalEnvelopingAlgebra.ι ℚ h) m =
      Ring.choose
          (_root_.UniversalEnvelopingAlgebra.ι ℚ h - n • (z • (1 : U))) m *
        Associative.dividedPower n (_root_.UniversalEnvelopingAlgebra.ι ℚ x) :=
  dividedPower_mul_ringChoose_eq m (mul_ι_eq_ι_mul_add_zsmul_one hz)
    ((Commute.one_left _).smul_left z) n

end TauCeti.UniversalEnvelopingAlgebra

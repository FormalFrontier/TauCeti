/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.UniversalEnveloping
public import TauCeti.Algebra.Module.Rat
public import TauCeti.RingTheory.DividedPowers.Commutation

/-!
# Cartan and root-vector commutation in a universal enveloping algebra

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

* `TauCeti.UniversalEnvelopingAlgebra.ι_mul_ι_eq_ι_mul_ι_add_zsmul_one`: the associative-ring
  form of an integral weight relation.
* `TauCeti.UniversalEnvelopingAlgebra.map_ι_lie`: an algebra representation maps a Lie bracket to
  the commutator of the images.
* `TauCeti.UniversalEnvelopingAlgebra.ringChoose_ι_mul_dividedPower_ι`: move a Cartan binomial
  coefficient to the right of a root-vector divided power.
* `TauCeti.UniversalEnvelopingAlgebra.dividedPower_ι_mul_ringChoose_ι`: the reverse reordering.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.2.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v

variable {L : Type u} [LieRing L]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The associative-ring form of an integral weight relation in a Lie algebra. -/
theorem ι_mul_ι_eq_ι_mul_ι_add_zsmul_one {R : Type*} [CommRing R] [LieAlgebra R L]
    {h x : L} {z : ℤ} (hz : ⁅h, x⁆ = z • x) :
    _root_.UniversalEnvelopingAlgebra.ι R h *
        _root_.UniversalEnvelopingAlgebra.ι R x =
      _root_.UniversalEnvelopingAlgebra.ι R x *
        (_root_.UniversalEnvelopingAlgebra.ι R h +
          z • (1 : _root_.UniversalEnvelopingAlgebra R L)) := by
  have hmap := LieHom.map_lie (_root_.UniversalEnvelopingAlgebra.ι R) h x
  rw [hz, map_zsmul, LieRing.of_associative_ring_bracket] at hmap
  rw [mul_add, zsmul_one, ← zsmul_eq_mul', add_comm]
  exact eq_add_of_sub_eq hmap.symm

variable [LieAlgebra ℚ L]

local notation "U" => _root_.UniversalEnvelopingAlgebra ℚ L

attribute [local instance] TauCeti.moduleNNRat

/-! ## Brackets in representations -/

/-- An algebra representation of the universal enveloping algebra maps the Lie bracket to the
commutator in its target algebra. -/
theorem map_ι_lie {A : Type v} [Ring A] [Algebra ℚ A]
    (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] A) (x y : L) :
    ⁅ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x), ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)⁆ =
      ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ ⁅x, y⁆) := by
  have hlie := LieHom.map_lie (_root_.UniversalEnvelopingAlgebra.ι ℚ) x y
  rw [LieRing.of_associative_ring_bracket] at hlie
  rw [LieRing.of_associative_ring_bracket, hlie, map_sub, map_mul, map_mul]

/-- A Lie-bracket eigenvector remains one under an algebra representation of the universal
enveloping algebra. -/
theorem map_ι_lie_eq_smul {A : Type v} [Ring A] [Algebra ℚ A]
    (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] A) {x y : L} {a : ℚ}
    (hxy : ⁅x, y⁆ = a • y) :
    ⁅ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x), ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)⁆ =
      a • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y) := by
  rw [map_ι_lie ρ, hxy, map_smul, map_smul]

/-- A Cartan binomial coefficient moves to the right of a root-vector divided power by adding
`n` copies of the integral weight to its argument. -/
theorem ringChoose_ι_mul_dividedPower_ι {h x : L} {z : ℤ} (hz : ⁅h, x⁆ = z • x)
    (m n : ℕ) :
    Ring.choose (_root_.UniversalEnvelopingAlgebra.ι ℚ h) m *
        Associative.dividedPower n (_root_.UniversalEnvelopingAlgebra.ι ℚ x) =
      Associative.dividedPower n (_root_.UniversalEnvelopingAlgebra.ι ℚ x) *
        Ring.choose
          (_root_.UniversalEnvelopingAlgebra.ι ℚ h + ((n * z : ℤ) : U)) m := by
  simpa only [nsmul_eq_mul, zsmul_eq_mul, mul_one, Int.cast_natCast, Int.cast_mul] using
    Associative.ringChoose_mul_dividedPower m
      (ι_mul_ι_eq_ι_mul_ι_add_zsmul_one hz) ((Commute.one_left _).smul_left z) n

/-- A Cartan binomial coefficient moves to the left of a root-vector divided power by subtracting
`n` copies of the integral weight from its argument. -/
theorem dividedPower_ι_mul_ringChoose_ι {h x : L} {z : ℤ} (hz : ⁅h, x⁆ = z • x)
    (m n : ℕ) :
    Associative.dividedPower n (_root_.UniversalEnvelopingAlgebra.ι ℚ x) *
        Ring.choose (_root_.UniversalEnvelopingAlgebra.ι ℚ h) m =
      Ring.choose
          (_root_.UniversalEnvelopingAlgebra.ι ℚ h - ((n * z : ℤ) : U)) m *
        Associative.dividedPower n (_root_.UniversalEnvelopingAlgebra.ι ℚ x) := by
  simpa only [nsmul_eq_mul, zsmul_eq_mul, mul_one, Int.cast_natCast, Int.cast_mul] using
    Associative.dividedPower_mul_ringChoose m
      (ι_mul_ι_eq_ι_mul_ι_add_zsmul_one hz) ((Commute.one_left _).smul_left z) n

end TauCeti.UniversalEnvelopingAlgebra

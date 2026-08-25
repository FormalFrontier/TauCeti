/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.FieldTheory.Separable

/-!
# Separability and splitting criteria for quadratic polynomials

Mathlib's `Mathlib/Algebra/QuadraticDiscriminant.lean` works with the *equation*
`a x² + b x + c = 0` and relates its solutions to `discrim a b c = b² - 4 a c`. This file reads
those facts back as statements about the *polynomial* `C a * X ^ 2 + C b * X + C c`. Wherever a
statement mentions the discriminant it uses Mathlib's `discrim` rather than its expansion, so
that Mathlib's discriminant API applies to it directly; the two criteria phrased by a root or by
an Artin-Schreier condition mention no discriminant at all.

Over a field, with `a ≠ 0`:

* `Polynomial.separable_quadratic_iff_discrim_ne_zero`: separable exactly when `discrim a b c ≠ 0`;
* `Polynomial.splits_quadratic_iff_exists_root`: splits exactly when it has a root — the
  characteristic-free core the other two are read off from;
* `Polynomial.splits_quadratic_iff_isSquare`: away from characteristic two, splits exactly when
  `discrim a b c` is a square;
* `Polynomial.splits_quadratic_iff_exists_artinSchreier_of_two_eq_zero`: in characteristic two,
  where the discriminant degenerates to `b²` (`discrim_eq_sq_of_two_eq_zero`) and the square-class
  criterion says nothing, splits exactly when the
  Artin-Schreier invariant `a c / b²` lies in the image of `z ↦ z² + z`, written division-free.
  Here `b ≠ 0` is also required, which by `separable_quadratic_iff_discrim_ne_zero` is separability.

Two auxiliary identities need neither a field nor `a ≠ 0`, and are stated over a commutative
(semi)ring: `Polynomial.derivative_quadratic`, computing the derivative as `2 a X + b`, and the
Bézout-type `Polynomial.sq_derivative_quadratic_sub_mul_eq_C_discrim`,
`(P')² - 4 a P = C (discrim a b c)`, which is what exhibits a nonzero discriminant as a
coprimality witness in every characteristic.

The two splitting criteria are consumed by the node-polynomial criteria of
`TauCeti/AlgebraicGeometry/EllipticCurve/NodePolynomial.lean`, which advance
`TauCetiRoadmap/EllipticCurves/README.md` §Layer 5 (twists): whether the node polynomial of a
multiplicative reduction splits over the residue field is exactly whether that reduction is split.

Adapted from the FLT project (`ImperialCollegeLondon/FLT`,
`FLT/Mathlib/Algebra/Polynomial/QuadraticDiscriminant.lean` at the roadmap's pin `bc2fe8ff7396`,
FLT PR #1088, Apache 2.0). That file's own header reads `Authors: Kevin Buzzard, Claude`;
following this repository's convention for adapted material, the upstream authorship is credited
here rather than in the copyright header. Ported with the source's `@[expose]` dropped, and
without its companion `FLT/Mathlib/Algebra/Polynomial/Splits.lean`: that file's
`Splits.of_natDegree_le_two_of_isRoot` is superseded here by Mathlib's own
`Polynomial.Splits.of_natDegree_eq_two`, which the one consumer can use directly since it knows
the degree is exactly two.
-/

public section

/-- In characteristic two the discriminant degenerates to `b²`, since `4 = 0` kills the `a c`
term. This is why `splits_quadratic_iff_isSquare` says nothing there: `discrim a b c` is
automatically a square. -/
theorem discrim_eq_sq_of_two_eq_zero {R : Type*} [CommRing R] (h2 : (2 : R) = 0) (a b c : R) :
    discrim a b c = b ^ 2 := by
  have h4 : (4 : R) = 0 := by linear_combination (2 : R) * h2
  rw [discrim]
  linear_combination -(a * c) * h4

namespace Polynomial

/-- The derivative of the quadratic `a X² + b X + c` is `2 a X + b`. -/
-- Deliberately not `@[simp]`: Mathlib's simp set already rewrites this left-hand side to
-- `C a * ((1 + 1) * X) + C b`, so the lemma is not in simp normal form and `simpNF` rejects it.
theorem derivative_quadratic {R : Type*} [CommSemiring R] (a b c : R) :
    derivative (C a * X ^ 2 + C b * X + C c) = 2 * C a * X + C b := by
  simp only [derivative_add, derivative_mul, derivative_C, derivative_X_pow, derivative_X,
    zero_mul, zero_add, mul_one, add_zero, Nat.cast_ofNat, Nat.reduceSub, pow_one, map_ofNat]
  ring

/-- The Bézout-type identity `(P')² - 4 a · P = C (discrim a b c)` for the quadratic
`P = a X² + b X + c`: the discriminant is an explicit `R[X]`-combination of `P` and its
derivative, which is what makes it a coprimality witness in
`separable_quadratic_iff_discrim_ne_zero`. -/
theorem sq_derivative_quadratic_sub_mul_eq_C_discrim {R : Type*} [CommRing R] (a b c : R) :
    derivative (C a * X ^ 2 + C b * X + C c) ^ 2
      - 4 * C a * (C a * X ^ 2 + C b * X + C c) = C (discrim a b c) := by
  rw [derivative_quadratic, discrim]
  simp only [map_sub, map_mul, map_pow, map_ofNat]
  ring

/-- A quadratic polynomial `a X² + b X + c` (with `a ≠ 0`) over a field is separable exactly when
`discrim a b c` is nonzero. This holds in every characteristic; contrast
`splits_quadratic_iff_isSquare`, which asks for the discriminant to be a square rather than
nonzero, and only away from characteristic two. -/
theorem separable_quadratic_iff_discrim_ne_zero {k : Type*} [Field k] {a b c : k} (ha : a ≠ 0) :
    (C a * X ^ 2 + C b * X + C c).Separable ↔ discrim a b c ≠ 0 := by
  set P := C a * X ^ 2 + C b * X + C c with hP
  have hid : derivative P ^ 2 - 4 * C a * P = C (discrim a b c) :=
    sq_derivative_quadratic_sub_mul_eq_C_discrim a b c
  constructor
  · intro hsep hdisc
    rw [hdisc, map_zero] at hid
    have hdvd : P ∣ derivative P ^ 2 := ⟨4 * C a, by linear_combination hid⟩
    exact not_isUnit_of_natDegree_pos P (by rw [hP, natDegree_quadratic ha]; norm_num)
      (((separable_def P).mp hsep).pow_right.isUnit_of_dvd' dvd_rfl hdvd)
  · intro hdisc
    rw [separable_def]
    have hdinv : C (discrim a b c)⁻¹ * C (discrim a b c) = 1 := by
      rw [← C_mul, inv_mul_cancel₀ hdisc, C_1]
    exact ⟨-(C (discrim a b c)⁻¹ * 4 * C a), C (discrim a b c)⁻¹ * derivative P,
      by linear_combination C (discrim a b c)⁻¹ * hid + hdinv⟩

/-- A quadratic `a X² + b X + c` (`a ≠ 0`) over a field splits exactly when it has a root. This is
the characteristic-free core of the two split criteria below, which only restate "has a root":
`splits_quadratic_iff_isSquare` in terms of the discriminant, and
`splits_quadratic_iff_exists_artinSchreier_of_two_eq_zero` in terms of the Artin-Schreier
invariant `a c / b²`. -/
theorem splits_quadratic_iff_exists_root {k : Type*} [Field k] {a b c : k} (ha : a ≠ 0) :
    (C a * X ^ 2 + C b * X + C c).Splits ↔ ∃ x, a * x ^ 2 + b * x + c = 0 := by
  set p := C a * X ^ 2 + C b * X + C c with hp
  have hdeg : p.natDegree = 2 := natDegree_quadratic ha
  constructor
  · intro hs
    obtain ⟨x, hx⟩ := hs.exists_eval_eq_zero (degree_ne_of_natDegree_ne (by rw [hdeg]; norm_num))
    refine ⟨x, ?_⟩
    simp only [hp, eval_add, eval_mul, eval_pow, eval_C, eval_X] at hx
    linear_combination hx
  · rintro ⟨x, hx⟩
    refine Splits.of_natDegree_eq_two hdeg (x := x) ?_
    simp only [hp, eval_add, eval_mul, eval_pow, eval_C, eval_X]
    linear_combination hx

/-- Over a field of characteristic `≠ 2`, a quadratic `a X² + b X + c` (with `a ≠ 0`) *splits*
exactly when `discrim a b c` is a square. Compare `separable_quadratic_iff_discrim_ne_zero`,
which asks for the discriminant to be nonzero rather than square, and holds in every
characteristic. -/
theorem splits_quadratic_iff_isSquare {k : Type*} [Field k] [NeZero (2 : k)] {a b c : k}
    (ha : a ≠ 0) :
    (C a * X ^ 2 + C b * X + C c).Splits ↔ IsSquare (discrim a b c) := by
  rw [splits_quadratic_iff_exists_root ha]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨2 * a * x + b, by rw [discrim_eq_sq_of_quadratic_eq_zero (a := a) (b := b) (c := c)
      (x := x) (by linear_combination hx)]; ring⟩
  · rintro ⟨s, hs⟩
    obtain ⟨x, hx⟩ := exists_quadratic_eq_zero ha ⟨s, by rw [hs]⟩
    exact ⟨x, by linear_combination hx⟩

/-- Over a field of characteristic `2`, a quadratic `a X² + b X + c` with `a, b ≠ 0` splits
exactly when its Artin-Schreier invariant `a c / b²` lies in the image of `z ↦ z² + z`, written
division-free as `∃ z, b² (z² + z) = a c`. Here the square-class criterion
`splits_quadratic_iff_isSquare` says nothing, since `discrim a b c = b²` is automatically a
square; the hypothesis `b ≠ 0` is
exactly separability, by `separable_quadratic_iff_discrim_ne_zero`. -/
theorem splits_quadratic_iff_exists_artinSchreier_of_two_eq_zero {k : Type*} [Field k]
    (h2 : (2 : k) = 0) {a b c : k} (ha : a ≠ 0) (hb : b ≠ 0) :
    (C a * X ^ 2 + C b * X + C c).Splits ↔ ∃ z, b ^ 2 * (z ^ 2 + z) = a * c := by
  rw [splits_quadratic_iff_exists_root ha]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨a * x / b, ?_⟩
    field_simp
    linear_combination hx - c * h2
  · rintro ⟨z, hz⟩
    refine ⟨b * z / a, ?_⟩
    field_simp
    linear_combination hz + a * c * h2

end Polynomial

end

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Data.Rat.Floor

/-!
# Non-negativity of a binary quadratic form and its discriminant

Mathlib's `discrim_le_zero` shows that a quadratic polynomial over a linearly ordered field which
is non-negative at every point of the field has non-positive discriminant. This file supplies two
facts about the homogeneous two-variable form `a * x ^ 2 + b * x * y + c * y ^ 2` that it does not
give: the reverse implication, and an integral version whose hypothesis is much weaker.

The integral version is the substantial one, and it is worth being precise about what makes it
substantial. Over a *field*, non-negativity along a single line `y = y₀ ≠ 0` already forces
`discrim a b c ≤ 0`: the restriction is a quadratic in `x`, so `discrim_le_zero` applies and the
resulting `y₀ ^ 2 * discrim a b c ≤ 0` may be divided by `y₀ ^ 2`. Over `ℤ` the same hypothesis
with `x` ranging over the *integers* is strictly weaker, and is genuinely not enough: the map
`x ↦ x ^ 2 - x` is non-negative at every integer, yet `discrim 1 (-1) 0 = 1 > 0`, which is
`forall_int_nonneg_and_discrim_pos` below. `Int.discrim_le_zero_of_nonneg_of_lt_abs` says that one
extra condition — that `|y₀|` exceed the leading coefficient — repairs this, with no further
quantification needed.

Together with the reverse implication this gives the upgrade that motivates the file: a form known
to be non-negative only on some sparse subset of `ℤ ⨯ ℤ` — for instance the locus where a
fixed prime does not divide `y`, which is all that the degree form on an elliptic curve is
directly known to satisfy — is non-negative everywhere. Any single `y₀` from that subset with
`|y₀|` large enough feeds `Int.discrim_le_zero_of_nonneg_of_lt_abs`, and then
`nonneg_of_discrim_le_zero` propagates the conclusion to every `(x, y)`.

## Main results

* `nonneg_of_discrim_le_zero`: `0 < a` and `discrim a b c ≤ 0` give `0 ≤ a x² + b x y + c y²`.
* `Int.discrim_le_zero_of_nonneg_of_lt_abs`: for `a < |y|`, and with no sign condition on `a`,
  non-negativity of `a x² + b x y + c y²` in `x` alone forces `discrim a b c ≤ 0`.
* `Int.discrim_le_zero_of_nonneg_of_not_dvd`: the same conclusion from non-negativity on
  `{(x, y) : d ∤ y}`, for any non-unit `d`.

## Provenance

Ported from the AINTLIB `HasseWeil` project (Apache-2.0), revision `513e83879e2f`, file
`HasseWeil/WeilPairing/Discriminant.lean`, declarations `exists_int_balanced`,
`qf_nonneg_of_nonneg_on_coprime` and `qf_nonneg_of_nonneg_on_coprime_both`. The statements here
are strictly stronger: the form is arbitrary rather than `q r² − t r s + s²`, no primality is
assumed, and a single `y` replaces an infinite family of prime powers.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, V.1.2 — the Cauchy–Schwarz step that turns
  positivity of the degree form on a rank-two lattice into the Hasse inequality of V.1.1.
-/

public section

/-- A binary quadratic form with positive leading coefficient and non-positive discriminant is
non-negative. This is the implication opposite to Mathlib's `discrim_le_zero`, stated for the
homogeneous two-variable form and over a linearly ordered commutative ring rather than a field.
The hypothesis `0 < a` cannot be dropped: `discrim 0 0 (-1) = 0`, while `- y ^ 2` is negative. -/
theorem nonneg_of_discrim_le_zero {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] {a b c : R} (ha : 0 < a) (hd : discrim a b c ≤ 0) (x y : R) :
    0 ≤ a * x ^ 2 + b * x * y + c * y ^ 2 := by
  -- The completed square `4a·Q = (2ax + by)² + (4ac − b²)y²` uses no division.
  have hb : 0 ≤ 4 * a * c - b ^ 2 := by rw [discrim] at hd; linarith
  nlinarith [sq_nonneg (2 * a * x + b * y), mul_nonneg hb (sq_nonneg y)]

/-- **A single line of large enough height pins the discriminant.** If a binary quadratic form
over `ℤ` with positive leading coefficient `a` is non-negative at `(x, y)` for a fixed `y` with
`a < |y|` and every integer `x`, then `discrim a b c ≤ 0`, that is `b ^ 2 ≤ 4 * a * c`.

The height hypothesis `a < |y|` is necessary, not an artefact of the proof: without it the
integer-valued hypothesis is strictly weaker than its field counterpart, as
`forall_int_nonneg_and_discrim_pos` witnesses. -/
private theorem discrim_le_zero_of_pos_of_nonneg_of_lt_abs {a b c y : ℤ} (ha : 0 < a)
    (hy : a < |y|) (h : ∀ x : ℤ, 0 ≤ a * x ^ 2 + b * x * y + c * y ^ 2) :
    discrim a b c ≤ 0 := by
  by_contra! hcon
  rw [discrim] at hcon
  have ha0 : (0 : ℚ) < 2 * (a : ℚ) := by
    have : (0 : ℚ) < (a : ℚ) := by exact_mod_cast ha
    linarith
  -- Evaluate at `x = -r`, where `r` is the integer nearest to `b * y / (2 * a)`; this is the
  -- integer closest to the minimum of the restricted form, and gives `|2ax + by| ≤ a`.
  set t : ℚ := ((b * y : ℤ) : ℚ) / (2 * (a : ℚ)) with htdef
  set r : ℤ := round t with hrdef
  have hxa : |2 * a * (-r) + b * y| ≤ a := by
    have hcast : ((2 * a * (-r) + b * y : ℤ) : ℚ) = 2 * (a : ℚ) * (t - (r : ℚ)) := by
      rw [htdef]
      field_simp
      push_cast
      ring
    have hq : |((2 * a * (-r) + b * y : ℤ) : ℚ)| ≤ ((a : ℤ) : ℚ) := by
      rw [hcast, abs_mul, abs_of_pos ha0]
      nlinarith [abs_sub_round t, abs_nonneg (t - (r : ℚ))]
    exact_mod_cast hq
  have hsq : (2 * a * (-r) + b * y) ^ 2 ≤ a ^ 2 := by
    have habs := abs_le.mp hxa
    nlinarith [habs.1, habs.2]
  -- `a < |y|` makes the `(4ac − b²)y²` term outweigh it, so the form is negative at `(-r, y)`.
  have hy2 : a ^ 2 < y ^ 2 := by nlinarith [sq_abs y, abs_nonneg y]
  have hkey : 4 * a * (a * (-r) ^ 2 + b * (-r) * y + c * y ^ 2)
      = (2 * a * (-r) + b * y) ^ 2 + (4 * a * c - b ^ 2) * y ^ 2 := by ring
  nlinarith [h (-r), hsq, hy2, hkey]

/-- A form with negative leading coefficient is eventually negative along any line, so the
non-negativity hypothesis is unsatisfiable. Evaluating at `x = |b * y| + |c * y ^ 2| + 1` is
already enough. -/
private theorem not_forall_nonneg_of_neg {a b c y : ℤ} (ha : a < 0) :
    ¬ ∀ x : ℤ, 0 ≤ a * x ^ 2 + b * x * y + c * y ^ 2 := fun h => by
  have hA0 : 0 ≤ |b * y| := abs_nonneg _
  have hB0 : 0 ≤ |c * y ^ 2| := abs_nonneg _
  set M : ℤ := |b * y| + |c * y ^ 2| + 1 with hM
  have hM1 : 1 ≤ M := by omega
  -- Bound each term of the form at `x = M` from above; the square dominates the rest.
  have h1 : a * M ^ 2 ≤ -(M ^ 2) := by nlinarith [sq_nonneg M]
  have h2 : b * M * y ≤ |b * y| * M := by
    nlinarith [mul_nonneg (sub_nonneg.mpr (le_abs_self (b * y))) (by linarith : (0 : ℤ) ≤ M)]
  have h3 : c * y ^ 2 ≤ |c * y ^ 2| := le_abs_self _
  have h4 : |b * y| * M + |c * y ^ 2| + 1 ≤ M ^ 2 := by nlinarith
  linarith [h M]

/-- A form with zero leading coefficient is linear in `x`, so non-negativity for every integer
`x` forces the linear coefficient `b * y` to vanish; with `y ≠ 0` that makes `b = 0`. -/
private theorem eq_zero_of_forall_nonneg_of_ne {b c y : ℤ} (hy : y ≠ 0)
    (h : ∀ x : ℤ, 0 ≤ 0 * x ^ 2 + b * x * y + c * y ^ 2) : b = 0 := by
  by_contra hb
  have hB0 : 0 ≤ |c * y ^ 2| := abs_nonneg _
  have hpos : 0 < (b * y) ^ 2 := by positivity
  have hs1 : 1 ≤ (b * y) ^ 2 := by omega
  have hcb : c * y ^ 2 ≤ |c * y ^ 2| := le_abs_self _
  -- At this `x` the linear term is `-(|c y²| + 1) * (b y)²`, which the constant cannot offset.
  have hx := h (-((|c * y ^ 2| + 1) * (b * y)))
  nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ |c * y ^ 2| + 1)
    (by linarith : (0 : ℤ) ≤ (b * y) ^ 2 - 1)]

/-- **A single line of large enough height pins the discriminant.** If a binary quadratic form
over `ℤ` is non-negative at `(x, y)` for a fixed `y` with `a < |y|` and every integer `x`, then
`discrim a b c ≤ 0`, that is `b ^ 2 ≤ 4 * a * c`.

No sign hypothesis on `a` is needed. A negative leading coefficient makes the hypothesis
unsatisfiable, and a zero one collapses the form to a linear function of `x`, forcing `b = 0`.

The height hypothesis `a < |y|` is necessary, not an artefact of the proof: without it the
integer-valued hypothesis is strictly weaker than its field counterpart, as
`forall_int_nonneg_and_discrim_pos` witnesses. -/
theorem Int.discrim_le_zero_of_nonneg_of_lt_abs {a b c y : ℤ} (hy : a < |y|)
    (h : ∀ x : ℤ, 0 ≤ a * x ^ 2 + b * x * y + c * y ^ 2) : discrim a b c ≤ 0 := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · exact absurd h (not_forall_nonneg_of_neg ha)
  · subst ha
    have hy0 : y ≠ 0 := by rintro rfl; simp at hy
    rw [discrim, eq_zero_of_forall_nonneg_of_ne hy0 h]
    simp
  · exact discrim_le_zero_of_pos_of_nonneg_of_lt_abs ha hy h

/-- The height hypothesis of `Int.discrim_le_zero_of_nonneg_of_lt_abs` cannot be dropped:
`x ↦ x ^ 2 - x` is non-negative at every integer, yet its discriminant is positive. Here the
leading coefficient and `|y|` are both `1`, so `a < |y|` fails by exactly one. -/
private theorem forall_int_nonneg_and_discrim_pos :
    (∀ x : ℤ, 0 ≤ 1 * x ^ 2 + (-1) * x * 1 + 0 * 1 ^ 2) ∧ 0 < discrim (1 : ℤ) (-1) 0 := by
  refine ⟨fun x => ?_, by norm_num [discrim]⟩
  rcases le_or_gt x 0 with hx | hx
  · nlinarith
  · nlinarith [Int.add_one_le_iff.mpr hx]

/-- **The locus `d ∤ y` pins the discriminant.** If a binary quadratic form over `ℤ` is
non-negative at every `(x, y)` whose second coordinate avoids the multiples of a non-unit `d` —
in the intended application `d` is a prime, and the locus is the sublattice complement
`{(x, y) : d ∤ y}` — then `discrim a b c ≤ 0`.

`d = 0` is allowed, the hypothesis then being non-negativity at every `y ≠ 0`. -/
theorem Int.discrim_le_zero_of_nonneg_of_not_dvd {a b c d : ℤ} (hd : ¬ IsUnit d)
    (h : ∀ x y : ℤ, ¬ d ∣ y → 0 ≤ a * x ^ 2 + b * x * y + c * y ^ 2) : discrim a b c ≤ 0 := by
  have hA : 0 ≤ |a| := abs_nonneg a
  have haA : a ≤ |a| := le_abs_self a
  rcases eq_or_ne d 0 with rfl | hd0
  · -- Only `y = 0` is excluded, so `y = |a| + 1` is available.
    refine Int.discrim_le_zero_of_nonneg_of_lt_abs (y := |a| + 1) ?_
      fun x => h x _ fun hc => by simp only [zero_dvd_iff] at hc; omega
    rw [abs_of_pos (by omega)]
    omega
  · -- Otherwise `1 < |d|`, and `y = |a| * d ^ 2 + 1` avoids `d` while exceeding `a`.
    have hd2 : 1 < |d| := by
      have h1 : d.natAbs ≠ 1 := fun hh => hd (Int.isUnit_iff_natAbs_eq.mpr hh)
      have h0 : d.natAbs ≠ 0 := fun hh => hd0 (Int.natAbs_eq_zero.mp hh)
      have : (1 : ℤ) < (d.natAbs : ℤ) := by
        exact_mod_cast Nat.lt_of_le_of_ne (by omega) (by omega)
      rwa [Int.abs_eq_natAbs]
    have hnd : ¬ d ∣ |a| * d ^ 2 + 1 := fun hc => by
      have hd1 : d ∣ (1 : ℤ) := (dvd_add_right (Dvd.intro (|a| * d) (by ring))).mp hc
      exact absurd (Int.le_of_dvd one_pos ((abs_dvd d 1).mpr hd1)) (by omega)
    refine Int.discrim_le_zero_of_nonneg_of_lt_abs (y := |a| * d ^ 2 + 1) ?_ fun x => h x _ hnd
    have hsq : 1 ≤ d ^ 2 := by nlinarith [sq_abs d, abs_nonneg d]
    rw [abs_of_pos (by nlinarith)]
    nlinarith

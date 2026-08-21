/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
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
to be non-negative only on some sparse subset of `ℤ ⨯ ℤ` — the locus where a fixed prime divides
neither coordinate, which is all that the degree form on an elliptic curve is directly known to
satisfy — is non-negative everywhere. `Int.discrim_le_zero_of_nonneg_of_not_dvd_of_not_dvd` pins
the discriminant from that locus alone, and `nonneg_of_discrim_le_zero` then propagates the
conclusion to every `(x, y)`.

## Main results

* `nonneg_of_discrim_le_zero`: `0 < a` and `discrim a b c ≤ 0` give `0 ≤ a x² + b x y + c y²`.
* `Int.discrim_le_zero_of_nonneg_of_lt_abs`: for `a < |y|`, and with no sign condition on `a`,
  non-negativity of `a x² + b x y + c y²` in `x` alone forces `discrim a b c ≤ 0`.
* `Int.discrim_le_zero_of_nonneg_of_not_dvd_of_not_dvd`: the same conclusion from non-negativity
  on `{(x, y) : d ∤ x ∧ d ∤ y}`, for any non-unit `d`.

Both are proved from a common lemma in which `x` runs over an arithmetic progression rather than
all of `ℤ`. Only one `x` is ever used — the member of the progression nearest the minimum of the
restricted form — so thinning the line to gap `m` costs exactly a factor `m` in the height
hypothesis, which the choice of `y` absorbs; `m = 1` is the full line.

The weaker hypothesis constraining only `y` is not stated separately: it is strictly stronger
than the one above, so a caller holding it applies the same theorem through
`fun x y _ hy => h x y hy`.

## Provenance

Ported from the AINTLIB `HasseWeil` project (Apache-2.0), revision `513e83879e2f`, file
`HasseWeil/WeilPairing/Discriminant.lean`, declarations `exists_int_balanced`,
`qf_nonneg_of_nonneg_on_coprime` and `qf_nonneg_of_nonneg_on_coprime_both`. The statements here
are strictly stronger: the form is arbitrary rather than `q r² − t r s + s²`, no primality is
assumed, and a single `y` replaces an infinite family of prime powers.

The source proves its two locus results independently, the `d ∤ y` one by an infinite family of
prime powers together with a balanced-remainder lemma. Neither is reproduced. The `d ∤ y`
statement is not carried at all: it follows from the `d ∤ x ∧ d ∤ y` one in a line, its hypothesis
being the stronger of the two. The balanced remainder it needed is Mathlib's `round`.

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

/-- Some member of the progression `x₀ + m * ℤ` puts `2 a x + z` within `a * m` of zero, for any
constant `z`.

This is the point-selection step of `discrim_le_zero_of_pos_of_nonneg_on_progression`, and the
source of the factor `m` in that theorem's height hypothesis. There `z` is the form's `b * y`,
which enters only as a constant. -/
private theorem exists_abs_two_mul_add_le {a m x₀ z : ℤ} (ha : 0 < a) (hm : 0 < m) :
    ∃ k : ℤ, |2 * a * (x₀ + m * k) + z| ≤ a * m := by
  -- take the member nearest the value that would make `2 a x + z` vanish: the rounding error is
  -- at most a half, and the progression's gap scales it by `2 a m`
  have ham : (0 : ℚ) < 2 * (a : ℚ) * (m : ℚ) := by
    have h1 : (0 : ℚ) < (a : ℚ) := by exact_mod_cast ha
    have h2 : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm
    positivity
  set t : ℚ := (-(z : ℚ) - 2 * (a : ℚ) * (x₀ : ℚ)) / (2 * (a : ℚ) * (m : ℚ)) with htdef
  refine ⟨round t, ?_⟩
  have hcast : ((2 * a * (x₀ + m * round t) + z : ℤ) : ℚ)
      = 2 * (a : ℚ) * (m : ℚ) * ((round t : ℚ) - t) := by
    rw [htdef]; field_simp; push_cast; ring
  have hq : |((2 * a * (x₀ + m * round t) + z : ℤ) : ℚ)| ≤ ((a * m : ℤ) : ℚ) := by
    rw [hcast, abs_mul, abs_of_pos ham]
    push_cast
    nlinarith [abs_sub_round t, abs_nonneg ((round t : ℚ) - t), abs_sub_comm (round t : ℚ) t]
  exact_mod_cast hq

/-- **An arithmetic progression of large enough height pins the discriminant.** If a binary
quadratic form over `ℤ` with positive leading coefficient `a` is non-negative at `(x, y)` for a
fixed `y` and every `x` in the progression `x₀ + m * ℤ`, and `a * m < |y|`, then
`discrim a b c ≤ 0`.

The height hypothesis carries a factor `m` that the single-line version does not; `m = 1` is the
full line. -/
private theorem discrim_le_zero_of_pos_of_nonneg_on_progression {a b c m x₀ y : ℤ} (ha : 0 < a)
    (hm : 0 < m) (hy : a * m < |y|)
    (h : ∀ k : ℤ, 0 ≤ a * (x₀ + m * k) ^ 2 + b * (x₀ + m * k) * y + c * y ^ 2) :
    discrim a b c ≤ 0 := by
  -- Only one `x` is used: the member of the progression nearest the minimum of the restricted
  -- form, which satisfies `|2 a x + b y| ≤ a * m`. That is why thinning the line to gap `m` costs
  -- exactly a factor `m` in the height.
  by_contra! hcon
  rw [discrim] at hcon
  obtain ⟨k, hxa⟩ := exists_abs_two_mul_add_le (x₀ := x₀) (z := b * y) ha hm
  set x : ℤ := x₀ + m * k with hxdef
  have hsq : (2 * a * x + b * y) ^ 2 ≤ (a * m) ^ 2 := by
    have habs := abs_le.mp hxa
    nlinarith [habs.1, habs.2]
  -- `a * m < |y|` makes the `(4ac − b²)y²` term outweigh it, so the form is negative at `(x, y)`.
  have ham0 : 0 < a * m := by positivity
  have hy2 : (a * m) ^ 2 < y ^ 2 := by nlinarith [sq_abs y, abs_nonneg y]
  have hkey : 4 * a * (a * x ^ 2 + b * x * y + c * y ^ 2)
      = (2 * a * x + b * y) ^ 2 + (4 * a * c - b ^ 2) * y ^ 2 := by ring
  nlinarith [h k, hsq, hy2, hkey]

/-- A form with negative leading coefficient is eventually negative along any progression, so the
non-negativity hypothesis is unsatisfiable. -/
private theorem not_forall_nonneg_on_progression_of_neg {a b c m x₀ y : ℤ} (ha : a < 0)
    (hm : 0 < m) :
    ¬ ∀ k : ℤ, 0 ≤ a * (x₀ + m * k) ^ 2 + b * (x₀ + m * k) * y + c * y ^ 2 := fun h => by
  have hA0 : 0 ≤ |b * y| := abs_nonneg _
  have hB0 : 0 ≤ |c * y ^ 2| := abs_nonneg _
  set M : ℤ := |b * y| + |c * y ^ 2| + 1 with hM
  have hM1 : 1 ≤ M := by omega
  -- The progression reaches past `M`, and there the square already dominates the rest.
  set k : ℤ := M + |x₀| with hk
  have hk0 : 0 ≤ k := by have := abs_nonneg x₀; omega
  set x : ℤ := x₀ + m * k with hx
  have hxM : M ≤ x := by
    have h1 : k ≤ m * k := le_mul_of_one_le_left hk0 hm
    have h2 : -|x₀| ≤ x₀ := neg_abs_le x₀
    rw [hx, hk] at *
    linarith
  have h1 : a * x ^ 2 ≤ -(x ^ 2) := by nlinarith [sq_nonneg x]
  have h2 : b * x * y ≤ |b * y| * x := by
    nlinarith [mul_nonneg (sub_nonneg.mpr (le_abs_self (b * y))) (by linarith : (0 : ℤ) ≤ x)]
  have h3 : c * y ^ 2 ≤ |c * y ^ 2| := le_abs_self _
  have h4 : |b * y| * x + |c * y ^ 2| + 1 ≤ x ^ 2 := by nlinarith
  linarith [h k]

/-- A form with zero leading coefficient is linear along a progression, so non-negativity there
forces the slope `b * y * m` to vanish; with `y ≠ 0` and `0 < m` that makes `b = 0`. -/
private theorem eq_zero_of_forall_nonneg_on_progression_of_ne {b c m x₀ y : ℤ} (hy : y ≠ 0)
    (hm : 0 < m)
    (h : ∀ k : ℤ, 0 ≤ 0 * (x₀ + m * k) ^ 2 + b * (x₀ + m * k) * y + c * y ^ 2) : b = 0 := by
  by_contra hb
  set C : ℤ := b * y * x₀ + c * y ^ 2 with hC
  have hid : ∀ k : ℤ, 0 * (x₀ + m * k) ^ 2 + b * (x₀ + m * k) * y + c * y ^ 2
      = b * y * m * k + C := fun k => by rw [hC]; ring
  have hC0 : 0 ≤ |C| := abs_nonneg _
  have hCle : C ≤ |C| := le_abs_self _
  have hpos : 0 < (b * y * m) ^ 2 := by positivity
  have hs1 : 1 ≤ (b * y * m) ^ 2 := by omega
  -- At this `k` the linear term is `-(|C| + 1) * (b y m)²`, which the constant cannot offset.
  have hx := h (-((|C| + 1) * (b * y * m)))
  rw [hid] at hx
  nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ |C| + 1)
    (by linarith : (0 : ℤ) ≤ (b * y * m) ^ 2 - 1)]

/-- **A progression of large enough height pins the discriminant, whatever the sign of `a`.** No
sign hypothesis on `a` is needed; this is the form both public theorems specialise. -/
private theorem discrim_le_zero_of_nonneg_on_progression {a b c m x₀ y : ℤ} (hm : 0 < m)
    (hy : a * m < |y|)
    (h : ∀ k : ℤ, 0 ≤ a * (x₀ + m * k) ^ 2 + b * (x₀ + m * k) * y + c * y ^ 2) :
    discrim a b c ≤ 0 := by
  -- A negative leading coefficient makes the hypothesis unsatisfiable; a zero one collapses the
  -- form to a linear function, forcing `b = 0`; a positive one is the case that does the work.
  rcases lt_trichotomy a 0 with ha | ha | ha
  · exact absurd h (not_forall_nonneg_on_progression_of_neg ha hm)
  · subst ha
    have hy0 : y ≠ 0 := by rintro rfl; simp at hy
    rw [discrim, eq_zero_of_forall_nonneg_on_progression_of_ne hy0 hm h]
    simp
  · exact discrim_le_zero_of_pos_of_nonneg_on_progression ha hm hy h

/-- **A single line of large enough height pins the discriminant.** If a binary quadratic form
over `ℤ` is non-negative at `(x, y)` for a fixed `y` with `a < |y|` and every integer `x`, then
`discrim a b c ≤ 0`, that is `b ^ 2 ≤ 4 * a * c`.

No sign hypothesis on `a` is needed. A negative leading coefficient makes the hypothesis
unsatisfiable, and a zero one collapses the form to a linear function of `x`, forcing `b = 0`.

The height hypothesis `a < |y|` is necessary, not an artefact of the proof: without it the
integer-valued hypothesis is strictly weaker than its field counterpart, as
`forall_int_nonneg_and_discrim_pos` witnesses. -/
theorem Int.discrim_le_zero_of_nonneg_of_lt_abs {a b c y : ℤ} (hy : a < |y|)
    (h : ∀ x : ℤ, 0 ≤ a * x ^ 2 + b * x * y + c * y ^ 2) : discrim a b c ≤ 0 :=
  -- The whole line is the progression of gap `1` through `0`.
  discrim_le_zero_of_nonneg_on_progression (x₀ := 0) one_pos (by simpa using hy)
    fun k => by simpa using h k

/-- The height hypothesis of `Int.discrim_le_zero_of_nonneg_of_lt_abs` cannot be dropped:
`x ↦ x ^ 2 - x` is non-negative at every integer, yet its discriminant is positive. Here the
leading coefficient and `|y|` are both `1`, so `a < |y|` fails by exactly one. -/
private theorem forall_int_nonneg_and_discrim_pos :
    (∀ x : ℤ, 0 ≤ 1 * x ^ 2 + (-1) * x * 1 + 0 * 1 ^ 2) ∧ 0 < discrim (1 : ℤ) (-1) 0 := by
  refine ⟨fun x => ?_, by norm_num [discrim]⟩
  rcases le_or_gt x 0 with hx | hx
  · nlinarith
  · nlinarith [Int.add_one_le_iff.mpr hx]

/-- Every member of the progression `1 + max |d| 2 * ℤ` avoids the multiples of a non-unit `d`.

The modulus is `|d|` in the intended case, `2` being needed only for `d = 0`: there the multiples
of `d` are `{0}` alone, and what has to be said is that `1 + 2 * k` is odd, hence nonzero. -/
private theorem not_dvd_one_add_max_mul {d : ℤ} (hd : ¬ IsUnit d) (k : ℤ) :
    ¬ d ∣ 1 + max |d| 2 * k := by
  intro hdvd
  rcases eq_or_ne d 0 with rfl | hd0
  · rw [zero_dvd_iff] at hdvd
    rw [abs_zero, max_eq_right (by norm_num)] at hdvd
    omega
  · have hd2 : 1 < |d| := by
      have h1 : d.natAbs ≠ 1 := fun hh => hd (Int.isUnit_iff_natAbs_eq.mpr hh)
      have h0 : d.natAbs ≠ 0 := fun hh => hd0 (Int.natAbs_eq_zero.mp hh)
      have : (1 : ℤ) < (d.natAbs : ℤ) := by
        exact_mod_cast Nat.lt_of_le_of_ne (by omega) (by omega)
      rwa [Int.abs_eq_natAbs]
    rw [max_eq_left (by omega), add_comm] at hdvd
    have hd1 : d ∣ (1 : ℤ) :=
      (dvd_add_right (((dvd_abs d d).mpr dvd_rfl).mul_right k)).mp hdvd
    exact absurd (Int.le_of_dvd one_pos ((abs_dvd d 1).mpr hd1)) (by omega)

/-- **The locus where `d` divides neither coordinate pins the discriminant.** If a binary
quadratic form over `ℤ` is non-negative at every `(x, y)` with `d ∤ x` and `d ∤ y`, for a non-unit
`d`, then `discrim a b c ≤ 0`.

The one-coordinate variant, constraining only `y`, is not stated separately: its hypothesis holds
on a strictly larger set of points, so it is the stronger of the two and a caller holding it
applies this theorem through `fun x y _ hy => h x y hy`. The implication does not run the other
way, and it is this form that an elliptic curve supplies, the pencil `r π − s` being known to be
an isogeny only away from both coordinates.

`d = 0` is allowed, the hypothesis then being non-negativity at every `(x, y)` with `x ≠ 0` and
`y ≠ 0`. -/
theorem Int.discrim_le_zero_of_nonneg_of_not_dvd_of_not_dvd {a b c d : ℤ} (hd : ¬ IsUnit d)
    (h : ∀ x y : ℤ, ¬ d ∣ x → ¬ d ∣ y → 0 ≤ a * x ^ 2 + b * x * y + c * y ^ 2) :
    discrim a b c ≤ 0 := by
  -- Both coordinates run over `1 + max |d| 2 * ℤ`, every member of which avoids the multiples of
  -- `d`; the widened gap costs a factor `max |d| 2` in the height, which the choice of `y` absorbs.
  set m : ℤ := max |d| 2 with hmdef
  have hm2 : 2 ≤ m := le_max_right _ _
  have hm0 : 0 < m := by omega
  have hdm : ∀ k : ℤ, ¬ d ∣ 1 + m * k := fun k => by rw [hmdef]; exact not_dvd_one_add_max_mul hd k
  -- One second coordinate serves every case: it avoids `d` and clears the widened height bound.
  have hA : 0 ≤ |a| := abs_nonneg a
  have haA : a ≤ |a| := le_abs_self a
  have hAm : 0 ≤ |a| * m := mul_nonneg hA hm0.le
  set y : ℤ := 1 + m * (|a| * m) with hy
  have hmm : 0 ≤ m * (|a| * m) := mul_nonneg hm0.le hAm
  have hy0 : 0 < y := by rw [hy]; linarith
  have hheight : a * m < |y| := by
    rw [abs_of_pos hy0, hy]
    have h1 : a * m ≤ |a| * m := mul_le_mul_of_nonneg_right haA hm0.le
    have h2 : |a| * m ≤ m * (|a| * m) := by nlinarith
    linarith
  have hyd : ¬ d ∣ y := hdm _
  exact discrim_le_zero_of_nonneg_on_progression hm0 hheight fun k => h _ y (hdm k) hyd

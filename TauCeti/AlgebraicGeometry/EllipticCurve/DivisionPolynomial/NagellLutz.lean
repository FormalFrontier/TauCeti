/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Descent
public import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Torsion
public import TauCeti.RingTheory.Localization.NumDen

/-!
# Nagell–Lutz integrality

Over `ℤ`, a nonzero torsion point of a Weierstrass curve has integral coordinates — unless it has
order exactly two, where the honest bound is that `4x` and `8y` are integral. Over the fraction
field `K` of a general unique factorisation domain `R` the same holds **given squarefreeness of
the right factor**: `Squarefree (2 : R)` when `4` divides the order, or squarefreeness of an odd
prime divisor of it. An arbitrary squarefree factor will not do — at order `6`, `Squarefree 2`
supplies neither branch. That hypothesis is what the `ℤ` statement discharges for free, and it is
not removable in general. This file is the assembly: `Torsion.lean` proves the cases a squarefree
hypothesis makes accessible, `Descent.lean` pulls a conclusion back from a multiple of a point to
the point itself, and what remains is the case analysis that connects them.

The split is on the order `m` of the point, and `m ≠ 1`, `m ≠ 2` put it in the range where
Mathlib's `Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt` applies: either `4 ∣ m`, or `m` has
an odd prime factor `p`. In the first case `(m / 4) • P` is killed by `4` but not by `2` and the
order-four theorem applies; in the second `(m / p) • P` is nonzero and killed by `p`, so the
odd-index theorem does. Descent along `m / 4` resp. `m / p` returns the conclusion at `P`. The
excluded case `m = 2` **need not** be integral; there `den_dvd_four_of_order_two` bounds the
denominator of `x` instead, and `ψ₂` vanishing bounds `y`.

Squarefreeness is a hypothesis rather than a typeclass, and it is **guarded by `m ≠ 2`**. The
order-two disjunct needs none of it, and an unguarded hypothesis would be unsatisfiable *for
two-torsion points* over any `R` in which `2` ramifies — `Squarefree (2 : ℤ[i])` is false, since
`2 = -i(1 + i)²`. Points of odd order over such an `R` are unaffected, since the hypothesis only
ever concerns primes dividing that point's own order; the guard is what keeps the order-two case
usable rather than what rescues the theorem. Over `ℤ` it costs nothing, which is why the
specialisation below carries no arithmetic hypothesis at all.

## Main results

* `WeierstrassCurve.isInteger_or_order_two_of_torsion`: the statement over a UFD `R`. Its
  squarefreeness hypothesis is **guarded** by `addOrderOf P ≠ 2` and asks only for the *one branch*
  the proof consumes, not for every prime factor.
* `WeierstrassCurve.isInteger_or_order_two_of_torsion_of_squarefree`: the same conclusion from a
  *uniform* hypothesis — squarefreeness at **every** prime factor of the order. That is strictly
  stronger, and therefore not weaker to prove; it is simply the form a caller usually already has,
  because it needs no knowledge of which branch the order falls into.
* `WeierstrassCurve.isInteger_or_order_two_of_torsion_rat`: the `ℤ`/`ℚ` specialisation, assuming
  only that the point is torsion.
* `WeierstrassCurve.isInteger_four_mul_x_and_eight_mul_y_of_order_two`: the order-two bound on its
  own, from a Jacobian two-torsion hypothesis and needing no squarefreeness at all.

## Roadmap

New mathematics: `TauCetiRoadmap/EllipticCurves/README.md:821` — "**The torsion subgroup and
Nagell–Lutz**", route "division polynomials" (`:830`–`:831`). Lines `:823`–`:827` state this
theorem for an integral **long** Weierstrass model: over `ℚ`, "a nonzero torsion point has
`x, y ∈ ℤ` unless it has order exactly `2`, where the honest bound is `4x, 8y ∈ ℤ`". The
discriminant companion and the short-model form (`:828`–`:830`) are separate targets.

## Provenance

Ported from J. Xu and D. K. Angdinata's AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0,
`main @ 1c1c74664e40071c2c2165bc55ca2616a67ccd6b`), from **two** files of
`projects/NagellLutz/LutzNagell/LutzNagellTheorem/`, both byte-identical at `9fec8eba7652` — the
revision the roadmap pins for this project (`README:1072`) — verified by blob hash, so the
citations hold at either.

`PIDMain.lean` supplies the statement shape: `nsmul_eq_zero_affine_to_jac` (`:48`),
`exists_some_of_ne_zero` (`:60`), `integrality_of_odd_prime_factor` (`:83`),
`integrality_of_four_dvd_order` (`:110`) and `lutz_nagell_integrality_pid` (`:145`), which is
already stated over a general base in `IsLocalization.IsInteger` terms.

`GeneralMain.lean` supplies the order-two conclusion. Its `lutz_nagell_integrality_general`
(`:112`) ends in `4x, 8y` integral, which is the form the roadmap asks for, where the `PID`
theorem ends in the weaker denominator bound `den(x) ∣ 4`. That file states the theorem over `ℚ`
only, so `isInteger_or_order_two_of_torsion_rat` is *its* statement and
`isInteger_or_order_two_of_torsion` generalises it.

Three adaptations. The base ring is a **UFD** rather than the source's principal ideal domain of
characteristic zero, matching `Torsion.lean` — no ideal is ever formed here, and `CharZero` is
unused. The squarefreeness hypothesis is **guarded by `addOrderOf P ≠ 2`**, which the source
leaves unguarded; see the note above on why an unguarded form is unsatisfiable over a ramifying
base — for two-torsion points, that is; a point of odd order never invokes `Squarefree (2 : R)`.
And the arithmetic of the case split is **not ported at all**: both sources derive
`4 ∣ m` from "no odd prime factor" by hand, roughly a dozen lines each, but that is exactly
Mathlib's `Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt`, so the split is one `rcases`.
-/

public section

open Polynomial

namespace WeierstrassCurve

open TauCeti.WeierstrassCurve

variable {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
variable {K : Type*} [Field K] [DecidableEq K] [Algebra R K] [IsFractionRing R K]
variable (W : WeierstrassCurve R)

/-- **A nonzero affine point is `.some`.** `Affine.Point` has two constructors, so this is the
`rcases` that names the coordinates and their nonsingularity certificate. Local proof plumbing:
the case split needs no field structure and has no Nagell–Lutz content. -/
private lemma exists_eq_some_of_ne_zero {F : Type*} [CommRing F] {E : WeierstrassCurve F}
    {P : Affine.Point E.toAffine} (hP : P ≠ 0) :
    ∃ x y, ∃ hns : E.toAffine.Nonsingular x y, P = .some _ _ hns := by
  rcases P with _ | ⟨_, _, hns⟩
  · exact absurd rfl hP
  · exact ⟨_, _, hns, rfl⟩

/-- **The odd branch.** If some odd prime `p` divides the order of a torsion point, both its
coordinates are integral.

Set `k = ord / p`; then `k • P` is nonzero of order exactly `p`, so the odd-index theorem applies
there, and integrality descends along `k`. -/
-- Only `x'`-integrality is extracted at `k • P`: `isInteger_of_zsmul_isInteger` returns *both*
-- coordinates at `P` from the `x`-coordinate alone, so the source's `hy'_int` is not needed.
private lemma isInteger_of_odd_prime_factor {x y : K}
    (hns : (W.baseChange K).toAffine.Nonsingular x y)
    {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hpm : p ∣ addOrderOf (Affine.Point.some _ _ hns))
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hns))
    (hsf : Squarefree ((p : ℤ) : R)) :
    IsLocalization.IsInteger R x ∧ IsLocalization.IsInteger R y := by
  set P := Affine.Point.some _ _ hns
  -- `(m / p) • P` has order exactly `p`, by Mathlib's order-of-a-multiple lemma. Both facts the
  -- descent needs — nonvanishing, and being killed by `p` — read off that one equality.
  have hord : addOrderOf ((addOrderOf P / p) • P) = p :=
    addOrderOf_nsmul_addOrderOf_sub htor.addOrderOf_pos.ne' hpm
  have hQ_ne : (addOrderOf P / p) • P ≠ 0 := fun h ↦ by
    rw [h, addOrderOf_zero] at hord; exact hp.ne_one hord.symm
  have hpQ : p • ((addOrderOf P / p) • P) = 0 :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mp hord.dvd
  obtain ⟨x', y', hns', hQ_eq⟩ := exists_eq_some_of_ne_zero hQ_ne
  have hx' : IsLocalization.IsInteger R x' :=
    isInteger_x_of_odd_torsion_of_squarefree W hns'
      (Int.not_even_iff_odd.mpr ((Int.odd_coe_nat p).mpr (hp.odd_of_ne_two hodd)))
      (zsmul_fromAffine_eq_zero_iff.mpr (hQ_eq ▸ hpQ)) hsf
  exact isInteger_of_zsmul_isInteger W hns hns'
    (by rw [natCast_zsmul]; exact hQ_eq) hx'

/-- **The 2-primary branch.** If `4` divides the order of a torsion point, both its coordinates
are integral.

Set `k = ord / 4`; then `k • P` is killed by `4` but not by `2`, so the order-four theorem applies
there, and integrality descends along `k`. The hypothesis is exactly `4 ∣ addOrderOf P`; the order
need not be a power of two, and `12` is an admissible case. -/
private lemma isInteger_of_four_dvd_order {x y : K}
    (hns : (W.baseChange K).toAffine.Nonsingular x y)
    (h4 : 4 ∣ addOrderOf (Affine.Point.some _ _ hns))
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hns))
    (hsf : Squarefree (2 : R)) :
    IsLocalization.IsInteger R x ∧ IsLocalization.IsInteger R y := by
  set P := Affine.Point.some _ _ hns
  -- As in the odd branch, one order equality from Mathlib supplies everything: `(m / 4) • P` has
  -- order exactly `4`, hence is nonzero, is killed by `4`, and is *not* killed by `2`.
  set Q := (addOrderOf P / 4) • P with hQ
  have hord : addOrderOf Q = 4 := addOrderOf_nsmul_addOrderOf_sub htor.addOrderOf_pos.ne' h4
  have hQ_ne : Q ≠ 0 := fun h ↦ by rw [h, addOrderOf_zero] at hord; omega
  have h4Q : (4 : ℕ) • Q = 0 := addOrderOf_dvd_iff_nsmul_eq_zero.mp hord.dvd
  have h2Q_ne : (2 : ℕ) • Q ≠ 0 := fun h ↦ by
    have := Nat.le_of_dvd (by norm_num) (addOrderOf_dvd_of_nsmul_eq_zero h)
    omega
  obtain ⟨x', y', hns', hQ_eq⟩ := exists_eq_some_of_ne_zero hQ_ne
  have hx' : IsLocalization.IsInteger R x' :=
    isInteger_x_of_order_four_of_squarefree W hns'
      (by exact_mod_cast zsmul_fromAffine_eq_zero_iff.mpr (hQ_eq ▸ h4Q))
      (fun h ↦ (hQ_eq ▸ h2Q_ne) (zsmul_fromAffine_eq_zero_iff.mp (by exact_mod_cast h))) hsf
  exact isInteger_of_zsmul_isInteger W hns hns'
    (by rw [natCast_zsmul]; exact hQ_eq) hx'

omit [DecidableEq K] in
/-- **The order-two exception.** A two-torsion point need not have integral coordinates, but
`4x` and `8y` are always integral. No squarefreeness is needed: the bound is a denominator
estimate, not a factorisation argument. -/
-- Three steps, none of which is a single existing lemma: `den_dvd_four_of_order_two` bounds the
-- denominator, `IsFractionRing.den_dvd_iff_isInteger_mul` turns that bound into integrality of
-- `algebraMap R K 4 * x` — note it is an **iff**, so `.mp` — and `map_ofNat` identifies that with
-- the numeral `4 * x`. The `y` half then needs `polynomialY` to vanish, which is `ψ₂` vanishing
-- rephrased through `ψ_two`.
-- The `omit` above: unlike the odd and order-four branches, this one never forms `n • P` in the
-- affine group, so it does not need the `DecidableEq K` they do — matching `Torsion.lean`, which
-- omits it on all four of its theorems.
theorem isInteger_four_mul_x_and_eight_mul_y_of_order_two {x y : K}
    (hns : (W.baseChange K).toAffine.Nonsingular x y)
    (h2 : (2 : ℤ) • Jacobian.Point.fromAffine (Affine.Point.some _ _ hns) = 0) :
    IsLocalization.IsInteger R (4 * x) ∧ IsLocalization.IsInteger R (8 * y) := by
  have hx : IsLocalization.IsInteger R (4 * x) := by
    have := IsFractionRing.den_dvd_iff_isInteger_mul.mp (den_dvd_four_of_order_two W hns h2)
    rwa [map_ofNat] at this
  refine ⟨hx, isInteger_eight_mul_y_of_evalEval_polynomialY_eq_zero W ?_ hx⟩
  -- `2 • P = 0` makes `ψ₂` vanish at `(x, y)`, and `ψ₂` *is* `polynomialY` for the base-changed
  -- curve — the rephrasing belongs here, in the consumer, not inside the `y`-bound lemma.
  have hψ := evalEval_ψ_eq_zero_of_zsmul_eq_zero (W.baseChange K) hns 2 h2
  rwa [WeierstrassCurve.ψ_two, WeierstrassCurve.ψ₂] at hψ

omit [IsDomain R] [UniqueFactorizationMonoid R] [IsFractionRing R K] in
/-- **The uniform squarefreeness hypothesis implies the sharp one.** Asking for squarefreeness at
*every* prime factor of the order is stronger than the theorem below needs — it consumes exactly
one branch — but it is what a caller can usually establish without first deciding the branch.
This is the bridge between the two forms, and where the case dichotomy actually happens, via
Mathlib's `Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt`. -/
private theorem four_dvd_or_exists_odd_prime_and_dvd_of_squarefree {x y : K}
    (hns : (W.baseChange K).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hns))
    (hsf : ∀ p : ℕ, p.Prime → p ∣ addOrderOf (Affine.Point.some _ _ hns) →
      Squarefree ((p : ℤ) : R))
    (hord2 : addOrderOf (Affine.Point.some _ _ hns) ≠ 2) :
    (4 ∣ addOrderOf (Affine.Point.some _ _ hns) ∧ Squarefree (2 : R)) ∨
      ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ addOrderOf (Affine.Point.some _ _ hns) ∧
        Squarefree ((p : ℤ) : R) := by
  set P := Affine.Point.some _ _ hns
  have hm_ne_one : addOrderOf P ≠ 1 := fun h ↦
    Affine.Point.some_ne_zero hns (AddMonoid.addOrderOf_eq_one_iff.mp h)
  have hm_pos : 0 < addOrderOf P := htor.addOrderOf_pos
  have hm_gt_two : 2 < addOrderOf P := by omega
  rcases Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt hm_gt_two with
    h4_dvd | ⟨p, hp, hpm, hodd⟩
  · exact Or.inl ⟨h4_dvd, by
      simpa using hsf 2 Nat.prime_two (dvd_trans ⟨2, rfl⟩ h4_dvd)⟩
  · have hp_ne_two : p ≠ 2 := by rintro rfl; rw [Nat.odd_iff] at hodd; omega
    exact Or.inr ⟨p, hp, hp_ne_two, hpm, hsf p hp hpm⟩

/-- **Nagell–Lutz integrality.** A nonzero torsion point either has integral coordinates, or has
order exactly two, in which case `4x` and `8y` are integral.

The squarefreeness hypothesis is **guarded by `addOrderOf P ≠ 2`**: the order-two disjunct is
proved by a denominator bound that needs no squarefreeness at all, and demanding it there would
make *the order-two case* unusable over any `R` in which `2` ramifies — `ℤ[i]` has `2 = -i(1+i)²`,
so `Squarefree (2 : ℤ[i])` is false and no two-torsion point could meet an unguarded hypothesis.
Odd-order points over the same `R` are unaffected. Over `ℤ` the guard costs nothing, since a
rational prime is squarefree there. -/
-- Case split on the order `m`, delegated to `Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt`:
-- past `m = 1` and `m = 2` it gives `4 ∣ m` or an odd prime factor, which are exactly the two
-- branches above. Both sources derive that dichotomy by hand instead.
theorem isInteger_or_order_two_of_torsion {x y : K}
    (hns : (W.baseChange K).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hns))
    (hsf : addOrderOf (Affine.Point.some _ _ hns) ≠ 2 →
      (4 ∣ addOrderOf (Affine.Point.some _ _ hns) ∧ Squarefree (2 : R)) ∨
        ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ addOrderOf (Affine.Point.some _ _ hns) ∧
          Squarefree ((p : ℤ) : R)) :
    (IsLocalization.IsInteger R x ∧ IsLocalization.IsInteger R y)
    ∨ (addOrderOf (Affine.Point.some _ _ hns) = 2 ∧
        IsLocalization.IsInteger R (4 * x) ∧ IsLocalization.IsInteger R (8 * y)) := by
  set P := Affine.Point.some _ _ hns
  by_cases hord2 : addOrderOf P = 2
  · have h2P : (2 : ℕ) • P = 0 := by rw [← hord2]; exact addOrderOf_nsmul_eq_zero P
    exact Or.inr ⟨hord2, isInteger_four_mul_x_and_eight_mul_y_of_order_two W hns
      (zsmul_fromAffine_eq_zero_iff.mpr h2P)⟩
  rcases hsf hord2 with ⟨h4_dvd, hs2⟩ | ⟨p, hp, hp_ne_two, hpm, hsp⟩
  · exact Or.inl (isInteger_of_four_dvd_order W hns h4_dvd htor hs2)
  · exact Or.inl (isInteger_of_odd_prime_factor W hns hp hp_ne_two hpm htor hsp)

/-- **Nagell–Lutz integrality, in the form most callers want.** Same conclusion as
`isInteger_or_order_two_of_torsion`, but asking for squarefreeness at *every* prime factor of the
order rather than at the one branch the proof consumes.

That hypothesis is strictly stronger — only one branch is ever used — so it is not a weaker thing
to prove. It is exported because it is usually the one a caller already has: establishing it needs
no knowledge of which branch the order falls into, whereas the sharp form does. Both are exported
for that reason, bridged by `four_dvd_or_exists_odd_prime_and_dvd_of_squarefree`. The guard
`addOrderOf P ≠ 2` is on both: the order-two disjunct is proved without squarefreeness, and
requiring it there would make the statement vacuous over a base in which `2` ramifies. -/
theorem isInteger_or_order_two_of_torsion_of_squarefree {x y : K}
    (hns : (W.baseChange K).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hns))
    (hsf : addOrderOf (Affine.Point.some _ _ hns) ≠ 2 →
      ∀ p : ℕ, p.Prime → p ∣ addOrderOf (Affine.Point.some _ _ hns) →
        Squarefree ((p : ℤ) : R)) :
    (IsLocalization.IsInteger R x ∧ IsLocalization.IsInteger R y)
    ∨ (addOrderOf (Affine.Point.some _ _ hns) = 2 ∧
        IsLocalization.IsInteger R (4 * x) ∧ IsLocalization.IsInteger R (8 * y)) :=
  isInteger_or_order_two_of_torsion W hns htor fun hord2 ↦
    four_dvd_or_exists_odd_prime_and_dvd_of_squarefree W hns htor (hsf hord2) hord2

/-- **Nagell–Lutz over `ℚ`**, the form the roadmap asks for: for an integral long Weierstrass
model, a nonzero torsion point has integral coordinates unless it has order exactly `2`, where the
honest bound is `4x, 8y ∈ ℤ`.

No squarefreeness hypothesis survives here. Over `ℤ` a rational prime **is** squarefree, so the
guard in the general statement discharges outright — which is why that statement carries the
hypothesis rather than a `CharZero`/unramified typeclass: the generality is free at `ℤ` and only
costs something over rings where a rational prime ramifies. -/
theorem isInteger_or_order_two_of_torsion_rat {W : WeierstrassCurve ℤ} {x y : ℚ}
    (hns : (W.baseChange ℚ).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hns)) :
    (IsLocalization.IsInteger ℤ x ∧ IsLocalization.IsInteger ℤ y)
    ∨ (addOrderOf (Affine.Point.some _ _ hns) = 2 ∧
        IsLocalization.IsInteger ℤ (4 * x) ∧ IsLocalization.IsInteger ℤ (8 * y)) :=
  -- Over `ℤ` every rational prime is squarefree, so the convenient form is free; the sharp form
  -- the theorem takes then follows by `four_dvd_or_exists_odd_prime_and_dvd_of_squarefree`.
  isInteger_or_order_two_of_torsion_of_squarefree W hns htor fun _ p hp _ ↦ by
    simpa using (Nat.prime_iff_prime_int.mp hp).squarefree

end WeierstrassCurve

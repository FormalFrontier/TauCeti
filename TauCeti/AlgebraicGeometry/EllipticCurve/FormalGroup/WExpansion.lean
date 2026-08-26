/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import TauCeti.RingTheory.PowerSeries.SelfConvolution

/-!
# The `w`-expansion of a Weierstrass curve

Substituting `x = z / w` and `y = -1 / w` into the Weierstrass equation of `W` and clearing
denominators turns it into

`w = z ^ 3 + a₁ z w + a₂ z ^ 2 w + a₃ w ^ 2 + a₄ z w ^ 2 + a₆ w ^ 3`,

which determines a unique power series `w(z) ∈ R⟦z⟧` with no terms below `z ^ 3`. This file
constructs that series, proves it satisfies the equation, and proves it is the only series with
vanishing constant coefficient that does.

## Main definitions

* `WeierstrassCurve.formalWCoeff`: the coefficients of `w(z)`, by strong recursion.
* `WeierstrassCurve.formalW`: the series `w(z)` itself.
* `WeierstrassCurve.formalUCoeff`, `WeierstrassCurve.formalU`: the coefficients, and the series
  itself, of `u(z) = w(z) / z ^ 3`.

## Main results

* `WeierstrassCurve.formalW_wEquation`: **Silverman AEC IV.1.1(a), existence** — `w(z)`
  satisfies the displayed equation, as an identity of power series.
* `WeierstrassCurve.eq_formalW_of_wEquation`: **Silverman AEC IV.1.1(a), uniqueness** — any
  power series with vanishing constant coefficient satisfying that equation equals `w(z)`. The
  two together are the full statement, that `w(z)` is *the* such series.
* `WeierstrassCurve.formalWCoeff_recurrence`: the coefficientwise recurrence — each coefficient
  of `w(z)` above the leading one, from the strictly earlier ones. This is the form to compute
  with; the strong recursion behind `formalWCoeff` is an implementation detail.
* `WeierstrassCurve.formalWCoeff_zero`, `_one`, `_two`, `_three` and
  `WeierstrassCurve.formalWCoeff_eq_zero_of_lt`: the series begins `w(z) = z ^ 3 + ⋯`.
* `WeierstrassCurve.formalW_eq_X_pow_mul_formalU`: `w(z) = z ^ 3 * u(z)`, where
  `WeierstrassCurve.constantCoeff_formalU` gives `u(0) = 1`. Over a `CommRing` that makes `u(z)`
  a unit; at the `CommSemiring` generality of this file it does not.

## Scope

This is the `w`-expansion only, the foundation of the formal group of `W`; the group law
`F(z₁, z₂)` is not here. Mathlib's `FormalGroup` (`Mathlib/RingTheory/FormalGroup/Basic.lean`)
bundles an associativity proof, and associativity of the Weierstrass group law is a separate
theorem of real depth, so a `FormalGroup` term cannot be produced from the `w`-expansion alone.
The directory anticipates that later work.

## Provenance

Adapted from the AINTLIB `HasseWeil` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0, pinned
by `TauCetiRoadmap/EllipticCurves/README.md` at `dev/hasse-weil @ 513e83879e2f`),
`HasseWeil/FormalGroup.lean`, declarations `formalW_step`, `formalW_coeff`, `formalW`,
`formalU_coeff`, the `formalW_coeff_*` lemmas and `formalW_recurrence`.

Changes from the source. The source's convolution helpers `conv₂` and `conv₃`, and its
coefficient and truncation lemmas for them, are stated only for `formalW`, although none of
those proofs uses anything about that series. Generalised to an arbitrary series — and to a
`Semiring`, which is all they need — they are not elliptic-curve material at all, and live in
`TauCeti.RingTheory.PowerSeries.SelfConvolution`, which this file imports and which carries
their attribution.

The source works over a commutative ring. Nothing here needs additive inverses — the equation,
the recursion and both halves of IV.1.1(a) use only sums and products — so everything is stated
over a `CommSemiring`.

The source does **not** prove uniqueness: its closing note records that the factoring step is
blocked by a `PowerSeries` typeclass gap (`RightDistribClass` and `IsRightCancelAdd` failing to
synthesize), and names coefficient induction as the untried alternative. That is the route
`eq_formalW_of_wEquation` takes here, so this file proves a result the source leaves open.

The source's own generic formal-group scaffolding (`FormalGroupLaw`,
`bmul`, `binv`, `bpow`, `bcomp`) is deliberately not ported: it predates and duplicates Mathlib's
`Mathlib/RingTheory/FormalGroup/Basic.lean`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1.
-/

public section

namespace WeierstrassCurve

variable {R : Type*} [CommSemiring R]

/-! ### The series `w(z)` -/

/-- One step of the recursion defining `formalWCoeff`: the coefficient of `z ^ n` in
`z ^ 3 + a₁ z w + a₂ z ^ 2 w + a₃ w ^ 2 + a₄ z w ^ 2 + a₆ w ^ 3`, given the earlier
coefficients `ih` of `w`.

This is the implementation of the strong recursion and is deliberately not part of the API;
`formalWCoeff_recurrence` is the recurrence to use downstream. -/
private def formalWStep (W : WeierstrassCurve R) (n : ℕ) (ih : ∀ m, m < n → R) : R :=
  if n < 3 then 0 else if n = 3 then 1 else
  let w : ℕ → R := fun m => if h : m < n then ih m h else 0
  W.a₁ * w (n - 1) + W.a₂ * w (n - 2) + W.a₃ * PowerSeries.selfConvTwo w n +
    W.a₄ * PowerSeries.selfConvTwo w (n - 1) + W.a₆ * PowerSeries.selfConvThree w n

/-- The coefficients of the `w`-expansion of `W`. -/
noncomputable def formalWCoeff (W : WeierstrassCurve R) : ℕ → R :=
  WellFoundedRelation.wf.fix (formalWStep W)

/-- The `w`-expansion `w(z)` of `W`, as a power series. -/
noncomputable def formalW (W : WeierstrassCurve R) : PowerSeries R :=
  PowerSeries.mk (formalWCoeff W)

/-- The coefficients of the unit part `u(z) = w(z) / z ^ 3` of the `w`-expansion. -/
noncomputable def formalUCoeff (W : WeierstrassCurve R) : ℕ → R :=
  fun n => formalWCoeff W (n + 3)

/-- The unit part `u(z) = w(z) / z ^ 3` of the `w`-expansion, as a power series. -/
noncomputable def formalU (W : WeierstrassCurve R) : PowerSeries R :=
  PowerSeries.mk (formalUCoeff W)

variable (W : WeierstrassCurve R)

/-- Unfolding `formalWCoeff` through its defining recursion. -/
private theorem formalWCoeff_eq_step (n : ℕ) :
    formalWCoeff W n = formalWStep W n fun m _ => formalWCoeff W m := by
  unfold formalWCoeff
  rw [WellFoundedRelation.wf.fix_eq]
  rfl

@[simp]
theorem formalWCoeff_zero : formalWCoeff W 0 = 0 := by
  rw [formalWCoeff_eq_step]; rfl

@[simp]
theorem formalWCoeff_one : formalWCoeff W 1 = 0 := by
  rw [formalWCoeff_eq_step]; rfl

@[simp]
theorem formalWCoeff_two : formalWCoeff W 2 = 0 := by
  rw [formalWCoeff_eq_step]; rfl

@[simp]
theorem formalWCoeff_three : formalWCoeff W 3 = 1 := by
  rw [formalWCoeff_eq_step]; rfl

/-- The `w`-expansion has no terms below degree `3`. -/
theorem formalWCoeff_eq_zero_of_lt {n : ℕ} (hn : n < 3) : formalWCoeff W n = 0 := by
  interval_cases n
  exacts [formalWCoeff_zero W, formalWCoeff_one W, formalWCoeff_two W]

/-- The recurrence characterising the coefficients of `w(z)` above the leading term: each is
determined by the strictly earlier ones. This is the coefficientwise form of
`formalW_wEquation`, and the intended way to compute with `formalWCoeff`. -/
theorem formalWCoeff_recurrence {n : ℕ} (hn : 3 < n) :
    formalWCoeff W n =
      W.a₁ * formalWCoeff W (n - 1) + W.a₂ * formalWCoeff W (n - 2) +
        W.a₃ * PowerSeries.selfConvTwo (formalWCoeff W) n +
        W.a₄ * PowerSeries.selfConvTwo (formalWCoeff W) (n - 1) +
        W.a₆ * PowerSeries.selfConvThree (formalWCoeff W) n := by
  have h1 : ¬ n < 3 := by omega
  have h2 : ¬ n = 3 := by omega
  have h5 : n - 1 < n := by omega
  have h6 : n - 2 < n := by omega
  rw [formalWCoeff_eq_step]
  unfold formalWStep
  dsimp only
  simp only [h1, h2, h5, h6, ite_true, ite_false, dite_eq_ite]
  rw [PowerSeries.selfConvTwo_truncate _ (formalWCoeff_zero W) n,
    PowerSeries.selfConvTwo_truncate_of_lt _ h5,
    PowerSeries.selfConvThree_truncate _ (formalWCoeff_zero W) n]

/-- The unit-part coefficients are the coefficients of `w(z)` shifted down by three. -/
@[simp]
theorem formalUCoeff_apply (n : ℕ) : formalUCoeff W n = formalWCoeff W (n + 3) := (rfl)

@[simp]
theorem coeff_formalW (n : ℕ) : PowerSeries.coeff n (formalW W) = formalWCoeff W n :=
  PowerSeries.coeff_mk n _

@[simp]
theorem coeff_formalU (n : ℕ) : PowerSeries.coeff n (formalU W) = formalUCoeff W n :=
  PowerSeries.coeff_mk n _

@[simp]
theorem constantCoeff_formalW : PowerSeries.constantCoeff (formalW W) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_formalW, formalWCoeff_zero]

@[simp]
theorem constantCoeff_formalU : PowerSeries.constantCoeff (formalU W) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_formalU]
  exact formalWCoeff_three W

/-- The `w`-expansion factors through its unit part: `w(z) = z ^ 3 * u(z)`, where
`constantCoeff_formalU` gives `u(0) = 1`. -/
theorem formalW_eq_X_pow_mul_formalU : formalW W = PowerSeries.X ^ 3 * formalU W := by
  ext n
  rw [coeff_formalW, PowerSeries.coeff_X_pow_mul']
  split_ifs with h
  · rw [coeff_formalU, formalUCoeff_apply, Nat.sub_add_cancel h]
  · exact formalWCoeff_eq_zero_of_lt W (by omega)

/-- The `n`-th coefficient of the right-hand side of the `w`-equation, for an arbitrary series
`w`, expressed through the coefficients of `w` itself. Every occurrence of `w` on the right is
multiplied by `X` or appears in a square or a cube. -/
private theorem coeff_wEquationRhs (w : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n
      (PowerSeries.X ^ 3 +
        PowerSeries.C W.a₁ * PowerSeries.X * w +
        PowerSeries.C W.a₂ * PowerSeries.X ^ 2 * w +
        PowerSeries.C W.a₃ * w ^ 2 +
        PowerSeries.C W.a₄ * PowerSeries.X * w ^ 2 +
        PowerSeries.C W.a₆ * w ^ 3) =
      (if n = 3 then 1 else 0) +
        W.a₁ * (if 1 ≤ n then PowerSeries.coeff (n - 1) w else 0) +
        W.a₂ * (if 2 ≤ n then PowerSeries.coeff (n - 2) w else 0) +
        W.a₃ * PowerSeries.selfConvTwo (fun k => PowerSeries.coeff k w) n +
        W.a₄ * (if 1 ≤ n then
            PowerSeries.selfConvTwo (fun k => PowerSeries.coeff k w) (n - 1)
          else 0) +
        W.a₆ * PowerSeries.selfConvThree (fun k => PowerSeries.coeff k w) n := by
  -- `PowerSeries.coeff_C_mul` and `PowerSeries.coeff_X_pow_mul'` each need their argument in the
  -- shape `C a * (X ^ d * f)`, so first reassociate the three products and write the bare `X` as
  -- `X ^ 1`. Rewriting `← pow_one` directly is not an option: it would also fire inside `X ^ 3`.
  have hX1 : ∀ (a : R) (f : PowerSeries R),
      PowerSeries.C a * PowerSeries.X * f = PowerSeries.C a * (PowerSeries.X ^ 1 * f) := by
    intro a f
    rw [pow_one, mul_assoc]
  have hX2 : ∀ (a : R) (f : PowerSeries R),
      PowerSeries.C a * PowerSeries.X ^ 2 * f = PowerSeries.C a * (PowerSeries.X ^ 2 * f) :=
    fun a f => mul_assoc _ _ _
  rw [hX1 W.a₁ w, hX2 W.a₂ w, hX1 W.a₄ (w ^ 2)]
  -- Two passes, and the order is load-bearing: `coeff_pow_three_eq_selfConvThree` also matches
  -- the leading `X ^ 3`, so that term must be resolved by `coeff_X_pow` before the convolution
  -- lemmas run.
  simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_X_pow]
  simp only [PowerSeries.coeff_pow_two_eq_selfConvTwo,
    PowerSeries.coeff_pow_three_eq_selfConvThree]

/-- **Silverman AEC IV.1.1(a), existence.** The `w`-expansion satisfies the equation obtained
from the Weierstrass equation of `W` by the substitution `x = z / w`, `y = -1 / w`. -/
theorem formalW_wEquation :
    formalW W =
      PowerSeries.X ^ 3 +
        PowerSeries.C W.a₁ * PowerSeries.X * formalW W +
        PowerSeries.C W.a₂ * PowerSeries.X ^ 2 * formalW W +
        PowerSeries.C W.a₃ * formalW W ^ 2 +
        PowerSeries.C W.a₄ * PowerSeries.X * formalW W ^ 2 +
        PowerSeries.C W.a₆ * formalW W ^ 3 := by
  have hlow : ∀ k, k < 3 → formalWCoeff W k = 0 := fun _ hk => formalWCoeff_eq_zero_of_lt W hk
  have hc2 : ∀ m, m < 6 → PowerSeries.selfConvTwo (formalWCoeff W) m = 0 :=
    fun _ hm => PowerSeries.selfConvTwo_eq_zero hlow hm
  have hc3 : ∀ m, m < 9 → PowerSeries.selfConvThree (formalWCoeff W) m = 0 :=
    fun _ hm => PowerSeries.selfConvThree_eq_zero hlow hm
  ext n
  rw [coeff_wEquationRhs]
  simp only [coeff_formalW]
  rcases lt_trichotomy n 3 with h | h | h
  · interval_cases n <;> simp [hc2, hc3]
  · subst h
    simp [hc2, hc3]
  · have h2 : ¬ n = 3 := by omega
    have h3 : 1 ≤ n := by omega
    have h4 : 2 ≤ n := by omega
    rw [formalWCoeff_recurrence W h]
    simp only [h2, h3, h4, ite_true, ite_false]
    ring

/-- **Silverman AEC IV.1.1(a), uniqueness.** A power series with vanishing constant coefficient
that satisfies the `w`-equation is `formalW W`. Together with `formalW_wEquation` this is the
full statement of Silverman AEC IV.1.1(a): `formalW W` is *the* such series.

Only `constantCoeff w = 0` is assumed: the equation at degrees `1` and `2` then forces those two
coefficients to vanish as well, because every occurrence of `w` on its right-hand side is
multiplied by `X` or sits in a square or a cube. -/
theorem eq_formalW_of_wEquation (w : PowerSeries R)
    (h0 : PowerSeries.constantCoeff w = 0)
    (hw : w =
      PowerSeries.X ^ 3 +
        PowerSeries.C W.a₁ * PowerSeries.X * w +
        PowerSeries.C W.a₂ * PowerSeries.X ^ 2 * w +
        PowerSeries.C W.a₃ * w ^ 2 +
        PowerSeries.C W.a₄ * PowerSeries.X * w ^ 2 +
        PowerSeries.C W.a₆ * w ^ 3) :
    w = formalW W := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply] at h0
  -- Degrees `1` and `2` are forced, so the induction below can still start from degree `3`.
  have hv0 : ∀ k, k < 1 → PowerSeries.coeff k w = 0 := by
    intro k hk; interval_cases k; exact h0
  have h1 : PowerSeries.coeff 1 w = 0 := by
    have hL := congrArg (PowerSeries.coeff 1) hw
    rw [coeff_wEquationRhs,
      PowerSeries.selfConvTwo_eq_zero hv0 (show (1 : ℕ) < 2 * 1 by omega),
      PowerSeries.selfConvTwo_eq_zero hv0 (show (1 : ℕ) - 1 < 2 * 1 by omega),
      PowerSeries.selfConvThree_eq_zero hv0 (show (1 : ℕ) < 3 * 1 by omega)] at hL
    simpa [h0] using hL
  have hv1 : ∀ k, k < 2 → PowerSeries.coeff k w = 0 := by
    intro k hk; interval_cases k; exacts [h0, h1]
  have h2 : PowerSeries.coeff 2 w = 0 := by
    have hL := congrArg (PowerSeries.coeff 2) hw
    rw [coeff_wEquationRhs,
      PowerSeries.selfConvTwo_eq_zero hv1 (show (2 : ℕ) < 2 * 2 by omega),
      PowerSeries.selfConvTwo_eq_zero hv1 (show (2 : ℕ) - 1 < 2 * 2 by omega),
      PowerSeries.selfConvThree_eq_zero hv1 (show (2 : ℕ) < 3 * 2 by omega)] at hL
    simpa [h0, h1] using hL
  have hlow : ∀ k, k < 3 → PowerSeries.coeff k w = 0 := by
    intro k hk; interval_cases k; exacts [h0, h1, h2]
  have hc2 : ∀ m, m < 6 → PowerSeries.selfConvTwo (fun k => PowerSeries.coeff k w) m = 0 :=
    fun _ hm => PowerSeries.selfConvTwo_eq_zero hlow hm
  have hc3 : ∀ m, m < 9 → PowerSeries.selfConvThree (fun k => PowerSeries.coeff k w) m = 0 :=
    fun _ hm => PowerSeries.selfConvThree_eq_zero hlow hm
  ext n
  -- The equation determines each coefficient from the strictly earlier ones, so this is a
  -- strong induction: at index `n` the right-hand side involves `w` only below `n`, by
  -- `coeff_wEquationRhs` together with `PowerSeries.selfConvTwo_congr` and
  -- `PowerSeries.selfConvThree_congr`.
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases lt_trichotomy n 3 with h | h | h
    · rw [hlow n h, coeff_formalW, formalWCoeff_eq_zero_of_lt W h]
    · subst h
      have hL := congrArg (PowerSeries.coeff 3) hw
      rw [coeff_wEquationRhs] at hL
      rw [hL, coeff_formalW, formalWCoeff_three]
      simp [hlow 1 (by omega), hlow 2 (by omega), hc2, hc3]
    · have hL := congrArg (PowerSeries.coeff n) hw
      rw [coeff_wEquationRhs] at hL
      have hw0 : (fun k => PowerSeries.coeff k w) 0 = 0 := hlow 0 (by omega)
      have hf0 : (fun k => formalWCoeff W k) 0 = 0 := formalWCoeff_zero W
      have hagree : ∀ m, m < n → PowerSeries.coeff m w = formalWCoeff W m := fun m hm => by
        rw [ih m hm, coeff_formalW]
      have h2' : ¬ n = 3 := by omega
      have h3 : 1 ≤ n := by omega
      have h4 : 2 ≤ n := by omega
      rw [hL, coeff_formalW, formalWCoeff_recurrence W h,
        PowerSeries.selfConvTwo_congr hw0 hf0 hagree,
        PowerSeries.selfConvTwo_congr (n := n - 1) hw0 hf0 (fun m hm => hagree m (by omega)),
        PowerSeries.selfConvThree_congr hw0 hf0 hagree,
        hagree (n - 1) (by omega), hagree (n - 2) (by omega)]
      simp only [h2', h3, h4, ite_true, ite_false]
      ring

end WeierstrassCurve

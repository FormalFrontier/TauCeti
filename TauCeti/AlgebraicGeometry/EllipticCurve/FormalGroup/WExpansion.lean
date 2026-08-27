/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.RingTheory.PowerSeries.Substitution
public import TauCeti.RingTheory.PowerSeries.SelfConvolution

/-!
# The `w`-expansion of a Weierstrass curve

Substituting `x = z / w` and `y = -1 / w` into the Weierstrass equation of `W` and clearing
denominators turns it into

`w = z ^ 3 + a₁ z w + a₂ z ^ 2 w + a₃ w ^ 2 + a₄ z w ^ 2 + a₆ w ^ 3`,

which determines a unique power series `w(z) ∈ R⟦z⟧` with no terms below `z ^ 3`. This file
constructs that series, proves it satisfies the equation, and proves it is the only series with
vanishing constant coefficient that does.

The equation is also recorded with its parameter left free, as `WeierstrassCurve.wEquationRHS`,
and its solution shown unique at every parameter with vanishing constant coefficient: the formal
group obtains the inverse and the group law by substitution, and a substituted series solves the
equation at the substituted parameter rather than at `z`.

## Main definitions

* `WeierstrassCurve.formalWCoeff`: the coefficients of `w(z)`, by strong recursion.
* `WeierstrassCurve.formalW`: the series `w(z)` itself.
* `WeierstrassCurve.formalUCoeff`, `WeierstrassCurve.formalU`: the coefficients, and the series
  itself, of `u(z) = w(z) / z ^ 3`.
* `WeierstrassCurve.wEquationRHS`: the right-hand side of the displayed equation, with both the
  parameter and the unknown left free.

## Main results

* `WeierstrassCurve.formalW_wEquation`: **Silverman AEC IV.1.1(a), existence** — `w(z)`
  satisfies the displayed equation, as an identity of power series.
* `WeierstrassCurve.eq_formalW_of_wEquation`: **Silverman AEC IV.1.1(a), uniqueness** — any
  power series with vanishing constant coefficient satisfying that equation equals `w(z)`. The
  two together are the full statement, that `w(z)` is *the* such series.
* `WeierstrassCurve.eq_of_wEquation`: uniqueness at any parameter that itself has vanishing
  constant coefficient — two series with vanishing constant coefficient solving the equation at
  that parameter are equal.
* `WeierstrassCurve.subst_wEquationRHS` and `WeierstrassCurve.subst_formalW_wEquation`:
  substituting a series `q` into the equation gives the equation at `q`, so `w(q)` solves it
  there. When moreover `constantCoeff q = 0`, `eq_subst_formalW_of_wEquation` combines this with
  `eq_of_wEquation` to identify `w(q)` as the only such solution.
* `WeierstrassCurve.formalWCoeff_recurrence`: the coefficientwise recurrence — each coefficient
  of `w(z)` above the leading one, from the strictly earlier ones. This is the form to compute
  with; the strong recursion behind `formalWCoeff` is an implementation detail.
* `WeierstrassCurve.formalWCoeff_zero`, `_one`, `_two`, `_three` and
  `WeierstrassCurve.formalWCoeff_eq_zero_of_lt`: the series begins `w(z) = z ^ 3 + ⋯`.
* `WeierstrassCurve.formalW_eq_X_pow_mul_formalU`: `w(z) = z ^ 3 * u(z)`, where
  `WeierstrassCurve.constantCoeff_formalU` gives `u(0) = 1`. Over a `CommRing` that makes `u(z)`
  a unit; at the `CommSemiring` generality of that section it does not.

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

The statement of uniqueness at an arbitrary parameter is adapted from Michael Stoll's
`EllipticCurves` project (`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, pinned by
`TauCetiRoadmap/EllipticCurves/README.md` at `66889eada51a`),
`EllipticCurves/WeierstrassFormalGroup/Chord.lean`, declarations `wStepAt` and
`eq_of_wStepAt_fixed`. There the equation is a `def` used only internally; here it is the public
`wEquationRHS`, so the existing statements in this file are phrased through it too. The proof is
not Stoll's: that argues by contraction for the `z`-adic filtration, which needs subtraction,
whereas the coefficient induction used here works at the `CommSemiring` generality of everything
in this file except the substitution lemmas, which are `CommRing` only because Mathlib's
`PowerSeries.subst` is.

Changes from the AINTLIB source. Its convolution helpers `conv₂` and `conv₃`, and its
coefficient and truncation lemmas for them, are stated only for `formalW`, although none of
those proofs uses anything about that series. Generalised to an arbitrary series — and to a
`Semiring`, which is all they need — they are not elliptic-curve material at all, and live in
`TauCeti.RingTheory.PowerSeries.SelfConvolution`, which this file imports and which carries
their attribution.

The AINTLIB source works over a commutative ring. Nothing there needs additive inverses — the
equation, the recursion and both halves of IV.1.1(a) use only sums and products — so everything
here is stated over a `CommSemiring`, with the single exception of the substitution lemmas, which
need Mathlib's `PowerSeries.subst` and so a `CommRing`.

The AINTLIB source does **not** prove uniqueness: its closing note records that the factoring
step is blocked by a `PowerSeries` typeclass gap (`RightDistribClass` and `IsRightCancelAdd`
failing to synthesize), and names coefficient induction as the untried alternative. That is the
route `eq_formalW_of_wEquation` takes here. Stoll's project does prove uniqueness, by the
contraction route recorded above rather than by the coefficient induction used here.

The AINTLIB source's own generic formal-group scaffolding (`FormalGroupLaw`,
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

/-! ### The `w`-equation -/

/-- The right-hand side of the `w`-equation, with the parameter series `q` in place of `z` and
the unknown `v` in place of `w`:

`q ^ 3 + a₁ q v + a₂ q ^ 2 v + a₃ v ^ 2 + a₄ q v ^ 2 + a₆ v ^ 3`.

The `w`-expansion is the solution at the parameter `q = z`, but the formal group needs solutions
at other parameters — substituting a series into `w(z)` solves the equation at that series — so
the parameter is left free. Every occurrence of the unknown is multiplied by `q` or sits in a
square or a cube, which is what makes the solution unique (`eq_of_wEquation`).

Rewrite with `wEquationRHS_def` rather than unfolding this definition. -/
noncomputable def wEquationRHS {A : Type*} [CommSemiring A] [Algebra R A]
    (W : WeierstrassCurve R) (q v : A) : A :=
  q ^ 3 + algebraMap R A W.a₁ * q * v + algebraMap R A W.a₂ * q ^ 2 * v +
    algebraMap R A W.a₃ * v ^ 2 + algebraMap R A W.a₄ * q * v ^ 2 + algebraMap R A W.a₆ * v ^ 3

/-- The defining formula for `wEquationRHS`. -/
theorem wEquationRHS_def {A : Type*} [CommSemiring A] [Algebra R A] (W : WeierstrassCurve R)
    (q v : A) :
    wEquationRHS W q v =
      q ^ 3 + algebraMap R A W.a₁ * q * v + algebraMap R A W.a₂ * q ^ 2 * v +
        algebraMap R A W.a₃ * v ^ 2 + algebraMap R A W.a₄ * q * v ^ 2 +
        algebraMap R A W.a₆ * v ^ 3 :=
  (rfl)

/-- The `w`-equation in `R⟦z⟧` itself, where the structure map is `PowerSeries.C`. This is the
spelling the coefficient lemmas below match against. -/
theorem wEquationRHS_powerSeries (W : WeierstrassCurve R) (q v : PowerSeries R) :
    wEquationRHS W q v =
      q ^ 3 + PowerSeries.C W.a₁ * q * v + PowerSeries.C W.a₂ * q ^ 2 * v +
        PowerSeries.C W.a₃ * v ^ 2 + PowerSeries.C W.a₄ * q * v ^ 2 +
        PowerSeries.C W.a₆ * v ^ 3 :=
  (rfl)

/-- The `n`-th coefficient of the right-hand side of the `w`-equation, for an arbitrary series
`w`, expressed through the coefficients of `w` itself. Every occurrence of `w` on the right is
multiplied by `X` or appears in a square or a cube. -/
private theorem coeff_wEquationRHS (w : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (wEquationRHS W PowerSeries.X w) =
      (if n = 3 then 1 else 0) +
        W.a₁ * (if 1 ≤ n then PowerSeries.coeff (n - 1) w else 0) +
        W.a₂ * (if 2 ≤ n then PowerSeries.coeff (n - 2) w else 0) +
        W.a₃ * PowerSeries.selfConvTwo (fun k => PowerSeries.coeff k w) n +
        W.a₄ * (if 1 ≤ n then
            PowerSeries.selfConvTwo (fun k => PowerSeries.coeff k w) (n - 1)
          else 0) +
        W.a₆ * PowerSeries.selfConvThree (fun k => PowerSeries.coeff k w) n := by
  rw [wEquationRHS_powerSeries]
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
      wEquationRHS W PowerSeries.X (formalW W) := by
  have hlow : ∀ k, k < 3 → formalWCoeff W k = 0 := fun _ hk => formalWCoeff_eq_zero_of_lt W hk
  have hc2 : ∀ m, m < 6 → PowerSeries.selfConvTwo (formalWCoeff W) m = 0 :=
    fun _ hm => PowerSeries.selfConvTwo_eq_zero hlow hm
  have hc3 : ∀ m, m < 9 → PowerSeries.selfConvThree (formalWCoeff W) m = 0 :=
    fun _ hm => PowerSeries.selfConvThree_eq_zero hlow hm
  ext n
  rw [coeff_wEquationRHS]
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

/-! ### Uniqueness at a parameter with vanishing constant coefficient

The formal group needs uniqueness not only at the parameter `z` but at any parameter series
with vanishing constant coefficient, because the inverse and the group law are obtained by
substituting one series into another, and such a substitution solves the equation at the
substituted parameter rather than at `z`. Vanishing of the constant coefficient is exactly what
makes the equation determine its solution: it is what forces the `n`-th coefficient of the
right-hand side to depend only on the earlier coefficients of the unknown.
-/

/-- The `n`-th coefficient of the right-hand side of the `w`-equation depends only on the
coefficients of the unknown strictly below `n`. This is the whole content of uniqueness: every
occurrence of the unknown is multiplied by the parameter, which has vanishing constant
coefficient, or sits in a square or a cube of a series with vanishing constant coefficient. -/
private theorem coeff_wEquationRHS_congr {q v v' : PowerSeries R}
    (hq : PowerSeries.constantCoeff q = 0) (hv : PowerSeries.constantCoeff v = 0)
    (hv' : PowerSeries.constantCoeff v' = 0) {n : ℕ}
    (h : ∀ m, m < n → PowerSeries.coeff m v = PowerSeries.coeff m v') :
    PowerSeries.coeff n (wEquationRHS W q v) = PowerSeries.coeff n (wEquationRHS W q v') := by
  have hv0 : (fun k => PowerSeries.coeff k v) 0 = 0 := by
    simpa using hv
  have hv'0 : (fun k => PowerSeries.coeff k v') 0 = 0 := by
    simpa using hv'
  have hsq : ∀ m, m ≤ n → PowerSeries.coeff m (v ^ 2) = PowerSeries.coeff m (v' ^ 2) := by
    intro m hm
    rw [PowerSeries.coeff_pow_two_eq_selfConvTwo, PowerSeries.coeff_pow_two_eq_selfConvTwo]
    exact PowerSeries.selfConvTwo_congr hv0 hv'0 fun k hk => h k (by omega)
  have hcb : PowerSeries.coeff n (v ^ 3) = PowerSeries.coeff n (v' ^ 3) := by
    rw [PowerSeries.coeff_pow_three_eq_selfConvThree,
      PowerSeries.coeff_pow_three_eq_selfConvThree]
    exact PowerSeries.selfConvThree_congr hv0 hv'0 h
  have hq2 : PowerSeries.constantCoeff (q ^ 2) = 0 := by
    rw [map_pow, hq]
    simp
  rw [wEquationRHS_powerSeries, wEquationRHS_powerSeries]
  simp only [map_add, mul_assoc, PowerSeries.coeff_C_mul]
  rw [PowerSeries.coeff_mul_congr hq h, PowerSeries.coeff_mul_congr hq2 h, hsq n le_rfl,
    PowerSeries.coeff_mul_congr hq fun m hm => hsq m hm.le, hcb]

/-- **Uniqueness of the solution of the `w`-equation.** Two power series with vanishing constant
coefficient that satisfy the `w`-equation at the same parameter series `q` are equal, provided
`q` too has vanishing constant coefficient.

The hypothesis on `q` is what drives the induction: it is exactly what makes the `n`-th
coefficient of the right-hand side depend only on the coefficients of the unknown strictly below
`n`, so that the equation determines its solution one coefficient at a time.

`eq_formalW_of_wEquation` is the case `q = z`, where the solution is moreover identified as
`formalW W`. -/
theorem eq_of_wEquation {q v v' : PowerSeries R} (hq : PowerSeries.constantCoeff q = 0)
    (hv : PowerSeries.constantCoeff v = 0) (hv' : PowerSeries.constantCoeff v' = 0)
    (h : v = wEquationRHS W q v) (h' : v' = wEquationRHS W q v') : v = v' := by
  ext n
  -- Each coefficient is determined by the strictly earlier ones, by `coeff_wEquationRHS_congr`.
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hL := congrArg (PowerSeries.coeff n) h
    have hR := congrArg (PowerSeries.coeff n) h'
    rw [hL, hR]
    exact coeff_wEquationRHS_congr W hq hv hv' ih

/-- **Silverman AEC IV.1.1(a), uniqueness.** A power series with vanishing constant coefficient
that satisfies the `w`-equation is `formalW W`. Together with `formalW_wEquation` this is the
full statement of Silverman AEC IV.1.1(a): `formalW W` is *the* such series.

Only `constantCoeff w = 0` is assumed: the equation at degrees `1` and `2` then forces those two
coefficients to vanish as well, because every occurrence of `w` on its right-hand side is
multiplied by `X` or sits in a square or a cube. -/
theorem eq_formalW_of_wEquation (w : PowerSeries R)
    (h0 : PowerSeries.constantCoeff w = 0)
    (hw : w = wEquationRHS W PowerSeries.X w) :
    w = formalW W :=
  eq_of_wEquation W (by simp) h0 (by simp) hw (formalW_wEquation W)

/-! ### Substituting into the equation

Substituting a series into the `w`-equation gives the equation at the substituted parameters. The
`w`-equation makes sense in any commutative `R`-algebra, and substitution is an `R`-algebra map, so
this is just the statement that `wEquationRHS` is built from `+`, `*`, `^` and the structure map.

With `constantCoeff q = 0` — strictly stronger than `PowerSeries.HasSubst q`, which asks only that
the constant coefficient be nilpotent — this combines with `eq_of_wEquation` to identify the
substituted solution, which is `eq_subst_formalW_of_wEquation`.

Mathlib's `PowerSeries.subst` is defined only over a `CommRing`, so this section is stated there;
everything above needs no such hypothesis and keeps the `CommSemiring` of the rest of this file.
-/

section CommRing

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- Substitution passes through the `w`-equation, carrying both the parameter and the unknown with
it. Both sides are read in the target algebra, which is why `wEquationRHS` is stated for an
arbitrary `R`-algebra: substituting a one-variable series into it lands in `MvPowerSeries τ S`. -/
theorem subst_wEquationRHS {τ S : Type*} [CommRing S] [Algebra R S] {a : MvPowerSeries τ S}
    (ha : PowerSeries.HasSubst a) (q v : PowerSeries R) :
    PowerSeries.subst a (wEquationRHS W q v) =
      wEquationRHS W (PowerSeries.subst a q) (PowerSeries.subst a v) := by
  rw [wEquationRHS_def, wEquationRHS_def, ← PowerSeries.coe_substAlgHom ha]
  simp only [map_add, map_mul, map_pow, AlgHom.commutes]

/-- The `w`-expansion composed with a substitutable series `a` solves the `w`-equation at `a`. -/
theorem subst_formalW_wEquation {τ S : Type*} [CommRing S] [Algebra R S] {a : MvPowerSeries τ S}
    (ha : PowerSeries.HasSubst a) :
    PowerSeries.subst a (formalW W) = wEquationRHS W a (PowerSeries.subst a (formalW W)) := by
  conv_lhs => rw [formalW_wEquation W]
  rw [subst_wEquationRHS W ha, PowerSeries.subst_X ha]

/-- **The substituted `w`-expansion is the unique solution at the substituted parameter.** For a
parameter `q` with vanishing constant coefficient, any series with vanishing constant coefficient
solving the `w`-equation at `q` is `w(q)`.

This is the composite the formal group consumes: `subst_formalW_wEquation` supplies a solution and
`eq_of_wEquation` says there is only one. Note the hypothesis is `constantCoeff q = 0` rather than
`PowerSeries.HasSubst q`; the latter asks only for a nilpotent constant coefficient, which is not
enough for uniqueness. -/
theorem eq_subst_formalW_of_wEquation {q v : PowerSeries R}
    (hq : PowerSeries.constantCoeff q = 0) (hv : PowerSeries.constantCoeff v = 0)
    (h : v = wEquationRHS W q v) : v = PowerSeries.subst q (formalW W) := by
  have ha : PowerSeries.HasSubst q := PowerSeries.HasSubst.of_constantCoeff_zero' hq
  refine eq_of_wEquation W hq hv ?_ h (subst_formalW_wEquation W ha)
  exact PowerSeries.constantCoeff_subst_eq_zero hq (formalW W) (constantCoeff_formalW W)

end CommRing

end WeierstrassCurve

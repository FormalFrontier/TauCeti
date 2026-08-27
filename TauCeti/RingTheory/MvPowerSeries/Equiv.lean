/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Equiv

/-!
# Coefficients of a one-variable power series viewed in one variable of a family

`PowerSeries.toMvPowerSeries i` views a one-variable power series as a multivariate one in the
single variable `i`. Mathlib records that it is an algebra map, how it acts on `C` and `X`, that
it is injective, and that its coefficients vanish off the powers of `i`
(`PowerSeries.toMvPowerSeries_coeff_eq_zero`); this file adds the remaining half, the value of
the coefficients that do not vanish.

## Main results

* `PowerSeries.coeff_toMvPowerSeries`: the coefficients of `w.toMvPowerSeries i`.

## Provenance

Adapted from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, pinned by
`TauCetiRoadmap/EllipticCurves/README.md` at `66889eada51a`),
`EllipticCurves/WeierstrassFormalGroup/Chord.lean`, the private lemma `coeff_rename_single`.
There it is stated for `MvPowerSeries.rename (fun _ => s)` and only where it is used; here it is
stated for the `PowerSeries.toMvPowerSeries` spelling of that map, which is Mathlib's, and it
carries no elliptic content so it is recorded on its own.
-/

public section

namespace PowerSeries

variable {σ R : Type*} [CommSemiring R] [DecidableEq σ]

/-- The coefficients of a one-variable power series viewed in the single variable `i`: the
coefficient of a monomial `d` is the `d i`-th coefficient of the original series if `d` is a
power of `i`, and `0` otherwise. -/
@[simp]
theorem coeff_toMvPowerSeries (i : σ) (w : PowerSeries R) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (w.toMvPowerSeries i) =
      if d = Finsupp.single i (d i) then coeff (d i) w else 0 := by
  rw [toMvPowerSeries_apply]
  split_ifs with h
  · have hd : d = Finsupp.embDomain (⟨fun _ => i, fun _ _ _ => rfl⟩ : Unit ↪ σ)
        (Finsupp.single () (d i)) := by
      rw [Finsupp.embDomain_single]
      exact h
    have h1 := MvPowerSeries.coeff_embDomain_rename
      (⟨fun _ => i, fun _ _ _ => rfl⟩ : Unit ↪ σ) w (Finsupp.single () (d i))
    rw [← hd] at h1
    exact h1
  · refine MvPowerSeries.coeff_rename_eq_zero _ _ fun ⟨y, hy⟩ => h ?_
    rw [← hy, Finsupp.unique_single y, Finsupp.mapDomain_single]
    simp

end PowerSeries

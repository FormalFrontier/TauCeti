/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Ring homomorphisms and `invOfUnit`

`MvPowerSeries.invOfUnit D u` inverts a power series whose constant coefficient is the unit `u`.
This file records that a ring homomorphism between power series rings carries it to the
`invOfUnit` of the image.

## Main results

* `MvPowerSeries.ringHom_invOfUnit`: for a ring homomorphism `φ` between multivariate power
  series rings, `φ (invOfUnit D u) = invOfUnit (φ D) v`, given `constantCoeff D = u` and
  `constantCoeff (φ D) = v`.
* `PowerSeries.ringHom_invOfUnit`: the same statement in the one-variable spelling.

## Implementation notes

The homomorphism is taken as a `RingHomClass` rather than a bundled `RingHom`, and the two index
types are independent. Both are needed by the consumers: `MvPowerSeries.rename` changes the index
type and is an `AlgHom`, not a `RingHom`, and so is `PowerSeries.substAlgHom`; `MvPowerSeries.map`
is the only consumer a bundled same-index statement would cover.

The source and target units are independent parameters, each with its own hypothesis. The target
unit is not obtained by transporting `u` along `φ`: `invOfUnit` needs only *some* unit equal to
the constant coefficient, and the second hypothesis supplies it. Fixing either to `1` would make
the lemma unusable for a series whose constant coefficient is a non-trivial unit.

`PowerSeries.ringHom_invOfUnit` is a definitional specialisation, but it is worth stating: without
it every one-variable consumer has to cross the `PowerSeries`/`MvPowerSeries` wrapper itself, by
unfolding `PowerSeries.invOfUnit` or by type ascription. Stating it once puts that bridge in one
place.

## Provenance

Adapted from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, pinned by
`TauCetiRoadmap/EllipticCurves/README.md` at `66889eada51a`),
`EllipticCurves/WeierstrassFormalGroup/Chord.lean`, the private `ringHom_invOfUnit` — whose name
is kept here — and its specialisation `rename_swap_invOfUnit`. The source fixes the unit to `1`
and works over a `CommRing`; both hypotheses are weakened here, and the proof is Mathlib's
`left_inv_eq_right_inv` rather than the source's `calc`.
-/

public section

variable {σ τ R S : Type*} [Ring R] [Ring S]

namespace MvPowerSeries

/-- A ring homomorphism between multivariate power series rings carries `invOfUnit` to the
`invOfUnit` of the image. -/
theorem ringHom_invOfUnit {F : Type*} [FunLike F (MvPowerSeries σ R) (MvPowerSeries τ S)]
    [RingHomClass F (MvPowerSeries σ R) (MvPowerSeries τ S)] (φ : F) {D : MvPowerSeries σ R}
    {u : Rˣ} {v : Sˣ} (hD : constantCoeff D = u) (hD' : constantCoeff (φ D) = v) :
    φ (invOfUnit D u) = invOfUnit (φ D) v :=
  left_inv_eq_right_inv
    (by rw [← map_mul, invOfUnit_mul D u hD, map_one])
    (mul_invOfUnit (φ D) v hD')

end MvPowerSeries

namespace PowerSeries

/-- A ring homomorphism between power series rings carries `invOfUnit` to the `invOfUnit` of the
image. This is `MvPowerSeries.ringHom_invOfUnit` in the one-variable spelling.

Both sides are spelled with `PowerSeries.invOfUnit` and `PowerSeries.constantCoeff`. That is the
point of stating it: a consumer working in one variable can rewrite with it directly, instead of
crossing the `PowerSeries`/`MvPowerSeries` wrapper itself. Substitution homomorphisms are still
covered, since their target `MvPowerSeries Unit S` is `PowerSeries S`. -/
theorem ringHom_invOfUnit {F : Type*} [FunLike F (PowerSeries R) (PowerSeries S)]
    [RingHomClass F (PowerSeries R) (PowerSeries S)] (φ : F) {D : PowerSeries R}
    {u : Rˣ} {v : Sˣ} (hD : constantCoeff D = u) (hD' : constantCoeff (φ D) = v) :
    φ (invOfUnit D u) = invOfUnit (φ D) v :=
  MvPowerSeries.ringHom_invOfUnit φ hD hD'

end PowerSeries

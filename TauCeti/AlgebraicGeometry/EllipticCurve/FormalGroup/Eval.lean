/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.RingTheory.PowerSeries.Evaluation
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Inverse
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.WExpansion
public import TauCeti.RingTheory.MvPowerSeries.Evaluation
public import TauCeti.Topology.Algebra.Nonarchimedean.AdicTopology
public import TauCeti.Topology.Algebra.Nonarchimedean.GeometricSeries

/-!
# Evaluating the `w`-expansion and the formal inverse at a parameter

For a Weierstrass curve `W` over a complete linearly topologised ring `O`, the `w`-expansion of
`FormalGroup/WExpansion.lean` and the formal inverse of `FormalGroup/Inverse.lean` can both be
evaluated at a parameter `t` for which the evaluation converges. This file provides those
evaluations, the identities they inherit from the series, and their membership, unit and
non-vanishing properties.

Two hypotheses appear here, and they do different work. `PowerSeries.HasEval t` is what evaluation
itself requires, and it is all the algebraic identities require: each of them is the image of an
identity of series under the ring homomorphism `PowerSeries.eval₂Hom`. Membership in a power of an
ideal requires more — the ideal `I`, and that the ambient topology is its adic one — because it
comes from `MvPowerSeries.eval₂_mem_pow`, which sums the monomial estimates inside the closed set
`I ^ k`.

Only two of the five values are confined to `I ^ k`, and neither needs that estimate: `w(t)` and
`ι(t)` factor as `t ^ 3 * u(t)` and `-(t * d(t)⁻¹)`, so a parameter in `I ^ k` carries them there.
The three unit statements have two different sources. `u(t)` is a unit because `u(t) - 1` lies in
`I`, hence is topologically nilpotent, so Wedhorn 5.38
(`IsTopologicallyNilpotent.isUnit_one_add`) applies; that membership,
`formalUEval_sub_one_mem`, is the file's one use of `MvPowerSeries.eval₂_mem_pow`. The denominator
`d(t) = 1 - a₁ t - a₃ w(t)` and its series inverse are units for an unrelated reason, needing no
ideal at all: the series identity `mul_invOfUnit_formalInverseDenom` evaluates to
`d(t) * d(t)⁻¹ = 1`.

## Main definitions

* `WeierstrassCurve.formalWEval` : the value `w(t)` of the `w`-expansion at `t`.
* `WeierstrassCurve.formalUEval` : the value `u(t)` of its unit part `w(z) / z ^ 3`.
* `WeierstrassCurve.formalInverseDenomEval` : the value of the denominator `1 - a₁ z - a₃ w(z)`.
* `WeierstrassCurve.formalInverseDenomInvEval` : the value of that denominator's series inverse.
* `WeierstrassCurve.formalInverseEval` : the value `ι(t)` of the formal inverse at `t`.

## Main results

* `WeierstrassCurve.formalWEval_eq_pow_mul_formalUEval` : the factorisation `w(t) = t ^ 3 * u(t)`.
* `WeierstrassCurve.formalWEval_mem`, `WeierstrassCurve.formalInverseEval_mem` : a parameter in
  `I ^ k` has `w(t)` and `ι(t)` in `I ^ k`.
* `WeierstrassCurve.formalUEval_sub_one_mem` : `u(t)` is congruent to `1` modulo `I ^ k`.
* `WeierstrassCurve.isUnit_formalUEval`, `WeierstrassCurve.isUnit_formalInverseDenomEval`,
  `WeierstrassCurve.isUnit_formalInverseDenomInvEval` : the three unit statements.
* `WeierstrassCurve.formalInverseDenomEval_eq`, `WeierstrassCurve.formalInverseEval_eq` and
  `WeierstrassCurve.formalInverseEval_mul_formalInverseDenomEval` : the defining formulas for
  `d(t)` and `ι(t)`, the last in the form `ι(t) * d(t) = -t` that avoids the series inverse.
* `WeierstrassCurve.formalWEval_wEquation` : the `w`-equation at a parameter.
* `WeierstrassCurve.formalWEval_ne_zero`, `WeierstrassCurve.formalInverseEval_ne_zero` : the two
  non-vanishing statements.

## Implementation notes

The evaluation is Mathlib's `PowerSeries.eval₂` at the identity ring hom. The adic hypothesis is
carried as an explicit `IsAdic I` argument rather than through a `WithIdeal` instance, matching
`MvPowerSeries.eval₂_mem_pow`, which these results call. `WithIdeal` would supply the topology
itself at `priority := 100`, so on a ring that already carries one — `ℤ_[p]`, whose topology comes
from its metric — the adic topology is shadowed and the results become inapplicable. `IsAdic` is
instead a *proposition about* the ambient topology, so it can be supplied for such a ring.

Names follow the series on this side rather than the source's: the evaluation of `formalW` is
`formalWEval`, and so on. The source's names do not transfer, because the source-to-repository map
is not order-preserving — the source's `uSeries` is this repository's `formalInverseDenom`, while
`formalU` is the source's `vSeries` — and every series here has the same type, so a mismatched
pairing would compile.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1.

## Provenance

Adapted from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, pinned by
`TauCetiRoadmap/EllipticCurves/README.md` at `66889eada51a`, whose full expansion is
`66889eada51a74c2f5dfb7fb5909b0b5a0a2d96e`),
`EllipticCurves/WeierstrassFormalGroup/Eval.lean` — its evaluation layer down to the formal
inverse, declarations `wEval`, `vEval`, `wEval_mem`, `wEval_eq`, `wEval_eq_cube_mul`,
`vEval_sub_one_mem`, `isUnit_vEval`, `uEval`, `duEval`, `iotaEval`, `uEval_eq`,
`uEval_mul_duEval`, `isUnit_uEval`, `iotaEval_eq` and `iotaEval_mem`.

Four things are spelled differently here.

* The source evaluates through its own `ChabautyColeman.MvPSeries.eval`, which is by definition
  `MvPowerSeries.eval₂ (RingHom.id _)`. That wrapper is not ported; the definitions use Mathlib's
  `PowerSeries.eval₂` directly, as `TauCeti/RingTheory/MvPowerSeries/Evaluation.lean` already does
  for the membership estimates this file calls.
* The source's three `eval_mem_maximalIdeal_pow` lemmas are that same file's
  `MvPowerSeries.eval₂_mem_pow`, `_mul` and `_add_mul`, which are stated for an arbitrary adic
  ideal rather than the maximal one, so none of the three is re-ported.
* The source obtains unit-ness from `IsLocalRing.isUnit_of_sub_one_mem_maximalIdeal`. Here it comes
  instead from `IsTopologicallyNilpotent.isUnit_one_add` — Wedhorn 5.38, already in this repository
  — which the ambient completeness makes available and which needs no hypothesis relating `I` to
  the Jacobson radical. `IsLocalRing` is therefore not needed in this file at all.
* The source's `wPoly` is this repository's `WeierstrassCurve.wEquationRHS`, which is generic over
  an algebra, so evaluating it at `O` gives the element-level equation without a second
  definition.

The adic hypothesis is carried as an explicit `IsAdic I` argument for the reason given under
implementation notes above.
-/

public section

open PowerSeries

variable {O : Type*} [CommRing O] [UniformSpace O] [IsUniformAddGroup O] [CompleteSpace O]
  [T2Space O] [IsTopologicalRing O] [IsLinearTopology O O]

/-- Evaluation at a parameter admitting one, as a ring homomorphism `O⟦X⟧ →+* O`. Every identity
in this file is the image of an identity of series under this map, so it is factored out here; it
is private because the file's statements are about the individual values, not about the vehicle
that transports them. -/
private noncomputable def evalAt {t : O} (ht : PowerSeries.HasEval t) : PowerSeries O →+* O :=
  PowerSeries.eval₂Hom (φ := RingHom.id O) (by simpa using continuous_id) ht

/-- `evalAt` is `PowerSeries.eval₂` at the identity ring hom, as a function. -/
private theorem coe_evalAt {t : O} (ht : PowerSeries.HasEval t) :
    ⇑(evalAt ht) = eval₂ (RingHom.id O) t :=
  PowerSeries.coe_eval₂Hom (φ := RingHom.id O) _ ht

namespace WeierstrassCurve

variable (W : WeierstrassCurve O)

/-- The value of the `w`-expansion at a parameter. -/
noncomputable def formalWEval (t : O) : O := eval₂ (RingHom.id O) t W.formalW

omit [IsUniformAddGroup O] [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  [IsLinearTopology O O] in
/-- `formalWEval` is evaluation of `formalW` through the identity ring hom. -/
theorem formalWEval_def (t : O) : W.formalWEval t = eval₂ (RingHom.id O) t W.formalW := (rfl)

/-- The value of the unit part `u(z) = w(z) / z ^ 3` at a parameter. -/
noncomputable def formalUEval (t : O) : O := eval₂ (RingHom.id O) t W.formalU

omit [IsUniformAddGroup O] [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  [IsLinearTopology O O] in
/-- `formalUEval` is evaluation of `formalU` through the identity ring hom. -/
theorem formalUEval_def (t : O) : W.formalUEval t = eval₂ (RingHom.id O) t W.formalU := (rfl)

/-- **The factorisation `w(t) = t ^ 3 * u(t)`** at a parameter, from the corresponding
factorisation `formalW_eq_X_pow_mul_formalU` of the series. -/
theorem formalWEval_eq_pow_mul_formalUEval {t : O} (ht : PowerSeries.HasEval t) :
    W.formalWEval t = t ^ 3 * W.formalUEval t := by
  have h := congrArg (evalAt ht) W.formalW_eq_X_pow_mul_formalU
  rw [map_mul, map_pow] at h
  simpa [formalWEval, formalUEval, coe_evalAt, PowerSeries.eval₂_X] using h

/-- The value of the `w`-expansion at a parameter of `I ^ k` again lies in `I ^ k`: it is
`t ^ 3` times the value of the unit part. -/
theorem formalWEval_mem {I : Ideal O} {k : ℕ} {t : O} (ht : PowerSeries.HasEval t)
    (htk : t ∈ I ^ k) : W.formalWEval t ∈ I ^ k := by
  rw [W.formalWEval_eq_pow_mul_formalUEval ht]
  exact Ideal.mul_mem_right _ _ (by rw [pow_succ]; exact Ideal.mul_mem_left _ _ htk)

/-- The value of the unit part differs from `1` by an element of `I ^ k` when the parameter lies
there: its constant coefficient is `1`, and every other monomial carries a factor of the
parameter. -/
theorem formalUEval_sub_one_mem {I : Ideal O} (hI : IsAdic I) {k : ℕ} {t : O}
    (ht : PowerSeries.HasEval t) (htk : t ∈ I ^ k) : W.formalUEval t - 1 ∈ I ^ k := by
  have key := MvPowerSeries.eval₂_mem_pow (φ := RingHom.id O) (by simpa using continuous_id)
    (PowerSeries.hasEval ht) hI (fun _ ↦ htk) (W.formalU - 1) (by
      rw [← PowerSeries.constantCoeff_eq]
      simp [W.constantCoeff_formalU])
  -- `eval₂` is additive only through `eval₂Hom`, which needs the continuity and `HasEval` data.
  have hsplit : eval₂ (RingHom.id O) t (W.formalU - 1) = W.formalUEval t - 1 := by
    have h := map_sub (evalAt ht) W.formalU 1
    rw [map_one] at h
    simpa [formalUEval, coe_evalAt] using h
  rw [← hsplit]
  simpa [eval₂] using key

/-- The value of the unit part at a parameter of `I` is a unit: it differs from `1` by an element
of `I`, which is topologically nilpotent, so Wedhorn 5.38 applies. -/
theorem isUnit_formalUEval {I : Ideal O} (hI : IsAdic I) {t : O} (ht : t ∈ I) :
    IsUnit (W.formalUEval t) := by
  have : NonarchimedeanRing O := hI ▸ I.nonarchimedean
  have hsub : W.formalUEval t - 1 ∈ I := by
    simpa using W.formalUEval_sub_one_mem hI (k := 1)
      (hI.isTopologicallyNilpotent_of_mem ht) (by simpa using ht)
  simpa using (hI.isTopologicallyNilpotent_of_mem hsub).isUnit_one_add

/-! ### The inverse-side evaluations

Note which series these evaluate. The source's `uSeries` is this repository's
`formalInverseDenom`, **not** `formalU`; `formalU` is the source's `vSeries`, evaluated above as
`formalUEval`. Both are `PowerSeries O`, so pairing an evaluation with the wrong one would compile.
-/

/-- The value of the formal inverse's denominator `1 - a₁ z - a₃ w(z)` at a parameter. -/
noncomputable def formalInverseDenomEval (t : O) : O :=
  eval₂ (RingHom.id O) t W.formalInverseDenom

omit [IsUniformAddGroup O] [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  [IsLinearTopology O O] in
/-- `formalInverseDenomEval` is evaluation of `formalInverseDenom` through the identity ring
hom. -/
theorem formalInverseDenomEval_def (t : O) :
    W.formalInverseDenomEval t = eval₂ (RingHom.id O) t W.formalInverseDenom := (rfl)

/-- The value at a parameter of the power-series inverse of `formalInverseDenom`. -/
noncomputable def formalInverseDenomInvEval (t : O) : O :=
  eval₂ (RingHom.id O) t (PowerSeries.invOfUnit W.formalInverseDenom 1)

omit [IsUniformAddGroup O] [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  [IsLinearTopology O O] in
/-- `formalInverseDenomInvEval` is evaluation of the series inverse of `formalInverseDenom`
through the identity ring hom. -/
theorem formalInverseDenomInvEval_def (t : O) : W.formalInverseDenomInvEval t =
    eval₂ (RingHom.id O) t (PowerSeries.invOfUnit W.formalInverseDenom 1) := (rfl)

/-- The value of the formal inverse `ι(z)` at a parameter. -/
noncomputable def formalInverseEval (t : O) : O := eval₂ (RingHom.id O) t W.formalInverse

omit [IsUniformAddGroup O] [CompleteSpace O] [T2Space O] [IsTopologicalRing O]
  [IsLinearTopology O O] in
/-- `formalInverseEval` is evaluation of `formalInverse` through the identity ring hom. -/
theorem formalInverseEval_def (t : O) :
    W.formalInverseEval t = eval₂ (RingHom.id O) t W.formalInverse := (rfl)

/-- The denominator's value and the value of its series inverse multiply to `1`. -/
theorem formalInverseDenomEval_mul_inv {t : O} (ht : PowerSeries.HasEval t) :
    W.formalInverseDenomEval t * W.formalInverseDenomInvEval t = 1 := by
  have h := congrArg (evalAt ht) W.mul_invOfUnit_formalInverseDenom
  rw [map_mul, map_one] at h
  simpa [formalInverseDenomEval, formalInverseDenomInvEval, coe_evalAt] using h

/-- The denominator's value at a parameter is a unit. -/
theorem isUnit_formalInverseDenomEval {t : O} (ht : PowerSeries.HasEval t) :
    IsUnit (W.formalInverseDenomEval t) :=
  IsUnit.of_mul_eq_one _ (W.formalInverseDenomEval_mul_inv ht)

/-- The value of the series inverse of the denominator is a unit. -/
theorem isUnit_formalInverseDenomInvEval {t : O} (ht : PowerSeries.HasEval t) :
    IsUnit (W.formalInverseDenomInvEval t) :=
  IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact W.formalInverseDenomEval_mul_inv ht)

/-- **The defining formula for the denominator's value**: `1 - a₁ t - a₃ w(t)`. -/
theorem formalInverseDenomEval_eq {t : O} (ht : PowerSeries.HasEval t) :
    W.formalInverseDenomEval t = 1 - W.a₁ * t - W.a₃ * W.formalWEval t := by
  have h := congrArg (evalAt ht) W.formalInverseDenom_def
  rw [map_sub, map_sub, map_one, map_mul, map_mul] at h
  simpa [formalInverseDenomEval, formalWEval, coe_evalAt, PowerSeries.eval₂_C,
    PowerSeries.eval₂_X] using h

/-- **The defining formula for the formal inverse's value**: `ι(t) = -t / (1 - a₁ t - a₃ w(t))`,
written through the series inverse of the denominator. -/
theorem formalInverseEval_eq {t : O} (ht : PowerSeries.HasEval t) :
    W.formalInverseEval t = -(t * W.formalInverseDenomInvEval t) := by
  have h := congrArg (evalAt ht) W.formalInverse_def
  rw [map_neg, map_mul] at h
  simpa [formalInverseEval, formalInverseDenomInvEval, coe_evalAt, PowerSeries.eval₂_X] using h

/-- **The defining formula for `ι(t)` cleared of the series inverse**: `ι(t)` times the concrete
denominator `1 - a₁ t - a₃ w(t)` is `-t`. -/
theorem formalInverseEval_mul_formalInverseDenomEval {t : O} (ht : PowerSeries.HasEval t) :
    W.formalInverseEval t * W.formalInverseDenomEval t = -t := by
  rw [W.formalInverseEval_eq ht, neg_mul, mul_assoc, mul_comm (W.formalInverseDenomInvEval t),
    W.formalInverseDenomEval_mul_inv ht, mul_one]

/-- The formal inverse maps a parameter of `I ^ k` back into `I ^ k`: it is `-t` times a value. -/
theorem formalInverseEval_mem {I : Ideal O} {k : ℕ} {t : O} (ht : PowerSeries.HasEval t)
    (htk : t ∈ I ^ k) : W.formalInverseEval t ∈ I ^ k := by
  rw [W.formalInverseEval_eq ht]
  exact neg_mem (Ideal.mul_mem_right _ _ htk)

/-- **The `w`-equation at a parameter.** Evaluating `formalW_wEquation` at `t` shows `w(t)` is a
fixed point of `v ↦ wEquationRHS W t v`, which is the Weierstrass equation in the coordinates
`x = z / w`, `y = -1 / w`. -/
theorem formalWEval_wEquation {t : O} (ht : PowerSeries.HasEval t) :
    W.formalWEval t = wEquationRHS W t (W.formalWEval t) := by
  have h := congrArg (evalAt ht) W.formalW_wEquation
  rw [wEquationRHS_powerSeries] at h
  simp only [map_add, map_mul, map_pow] at h
  simpa [formalWEval, wEquationRHS_def, coe_evalAt, PowerSeries.eval₂_C,
    PowerSeries.eval₂_X] using h

/-- `w` does not vanish at a parameter of `I` whose cube is nonzero: the factorisation
`w(t) = t ^ 3 * u(t)` has a unit second factor. Over a domain the hypothesis is `t ≠ 0`. -/
theorem formalWEval_ne_zero {I : Ideal O} (hI : IsAdic I) {t : O} (ht : t ∈ I)
    (ht0 : t ^ 3 ≠ 0) : W.formalWEval t ≠ 0 := by
  rw [W.formalWEval_eq_pow_mul_formalUEval (hI.isTopologicallyNilpotent_of_mem ht)]
  exact fun h ↦ ht0 ((W.isUnit_formalUEval hI ht).mul_left_eq_zero.mp h)

/-- The formal inverse does not vanish at a nonzero parameter: `ι(t)` is `-t` times a unit, and
multiplying by a unit cannot create a zero. No hypothesis on `t ^ 3` is needed — unlike
`formalWEval_ne_zero`, whose factor `t ^ 3` can vanish at a nonzero nilpotent `t`. -/
theorem formalInverseEval_ne_zero {t : O} (ht : PowerSeries.HasEval t) (ht0 : t ≠ 0) :
    W.formalInverseEval t ≠ 0 := by
  rw [W.formalInverseEval_eq ht, neg_ne_zero]
  exact fun h ↦ ht0 ((W.isUnit_formalInverseDenomInvEval ht).mul_left_eq_zero.mp h)

end WeierstrassCurve

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction

/-!
# Minimality from a unit `c₄`

Mathlib defines `WeierstrassCurve.IsMinimal` by a maximality property — the valuation of the
discriminant is maximal among all integral models isomorphic to the given one — and derives
minimality only from that property or from a class that already extends it. Establishing it for a
*given* equation therefore means quantifying over every change of variables, which is not something
a caller can discharge by hand.

This file supplies the cheapest sufficient condition: an integral Weierstrass equation whose `c₄`
is a **unit** at the place is already minimal.

## Main results

* `WeierstrassCurve.isMinimal_of_valuation_c₄_eq_one`: over the fraction field of a discrete
  valuation ring, an integral Weierstrass equation with `v (c₄) = 1` is minimal.

## Why this is the useful form

The hypothesis is stated through the adic valuation of `W.c₄ : K`, matching how Mathlib phrases
`WeierstrassCurve.HasMultiplicativeReduction`, whose `multiplicativeReduction` field is exactly
`valuation K (maximalIdeal R) W.c₄ = 1`. That class *extends* `IsMinimal`, so the implication is
not needed to go from multiplicative reduction to minimality — it is needed in the other
direction, to **construct** `HasMultiplicativeReduction` for an equation one has only computed
`c₄` and `Δ` for. That is the shape a quadratic twist arrives in: twisting by a discriminant that
is a unit scales `c₄` by a unit square, so the twist's `c₄` valuation is again `1`, and this
criterion is what turns that computation into minimality of the twisted model.

## Mathematical content

It is the unit-`c₄` case of the Kraus–Laska criterion — the special case "`v (c₄) < 4` or
`v (Δ) < 12` implies minimal" of Silverman, *The Arithmetic of Elliptic Curves*,
Remark VII.1.1, restricted to `v (c₄) = 0`. The proof is direct: a change of variables scales
`c₄` by `u⁻⁴` and `Δ` by `u⁻¹²`, and integrality of the transformed model bounds `v (u⁻⁴)` by
`1`, hence `v (u⁻¹²) ≤ 1`, so no change of variables can raise the discriminant's valuation.

## Provenance

⚠ *mathlib-track*: this is a statement about Mathlib's own `IsMinimal`, with no Tau Ceti
definitions involved, and belongs upstream once its consumers are in place.

Ported from FLT, https://github.com/ImperialCollegeLondon/FLT
@ `bc2fe8ff7396469a16c2a6d51d6117f5825d93a0` (Apache-2.0), file
`FLT/Mathlib/AlgebraicGeometry/EllipticCurve/Reduction.lean`, declaration
`WeierstrassCurve.isMinimal_of_valuation_c₄_eq_one`, by Kevin Buzzard. Statement and proof are
taken unchanged; only the section's variable block is restated and the `open`s are narrowed to
Mathlib's own `Minimal` section, since this file carries no other declarations.
-/

public section

namespace WeierstrassCurve

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- **An integral Weierstrass equation whose `c₄` is a unit at the place is minimal.** No change of
variables can increase the valuation of the discriminant: it scales `Δ` by `u⁻¹²` while scaling
`c₄` by `u⁻⁴`, and integrality of the transformed equation forces `v (u⁻⁴) ≤ 1`.

This is the unit-`c₄` case of the Kraus–Laska criterion (Silverman, *AEC*, Remark VII.1.1). The
hypothesis is phrased through the adic valuation of `W.c₄ : K` to match
`WeierstrassCurve.HasMultiplicativeReduction`, so that a curve for which only `c₄` has been
computed can be given its `IsMinimal` field. -/
theorem isMinimal_of_valuation_c₄_eq_one (W : WeierstrassCurve K) [IsIntegral R W]
    (hc₄ : valuation K (maximalIdeal R) W.c₄ = 1) : IsMinimal R W := by
  refine ⟨⟨by simpa using ‹IsIntegral R W›, ?_⟩⟩
  intro C hC _
  simp only [one_smul, ← Subtype.coe_le_coe, valuation_Δ_aux_eq_of_isIntegral R (C • W),
    valuation_Δ_aux_eq_of_isIntegral R W]
  have hint : valuation K (maximalIdeal R) (C • W).c₄ ≤ 1 := by
    simpa [← integralModel_c₄_eq R (C • W)] using valuation_le_one _ _
  rw [variableChange_c₄, map_mul, map_pow, hc₄, mul_one] at hint
  simpa [variableChange_Δ, map_mul, map_pow] using mul_le_of_le_one_left'
    (pow_le_one' ((pow_le_one_iff (by norm_num)).mp hint) 12)

end WeierstrassCurve

end

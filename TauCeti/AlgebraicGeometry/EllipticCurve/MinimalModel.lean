/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction

/-!
# Minimal models: a criterion, and the comparison of two of them

Mathlib defines `WeierstrassCurve.IsMinimal` by a maximality property — the valuation of the
discriminant is maximal among all integral models isomorphic to the given one — and derives
minimality only from that property or from a class that already extends it. Establishing it for a
*given* equation therefore means quantifying over every change of variables, which is not something
a caller can discharge by hand.

This file supplies the cheapest sufficient condition — an integral Weierstrass equation whose `c₄`
is a **unit** at the place is already minimal — and then the comparison any two minimal models
admit: they have the same discriminant valuation, so a change of variables between them has a
scaling factor of valuation `1`.

## Main results

* `WeierstrassCurve.isMinimal_of_valuation_c₄_eq_one`: over the fraction field of a discrete
  valuation ring, an integral Weierstrass equation with `v (c₄) = 1` is minimal.
* `WeierstrassCurve.valuation_Δ_eq_of_isMinimal_smul`: two minimal models related by a change of
  variables have equal `v (Δ)`.
* `WeierstrassCurve.valuation_u_eq_one_of_isMinimal_smul`: for an elliptic curve, the scaling
  factor of such a change of variables satisfies `v (u) = 1`.

The last is the shape a consumer needs. `v (u) = 1` over a discrete valuation ring says `u` is a
unit of `R`, which is the hypothesis that lets a change of variables between two integral models be
descended to `R` — and thence lets properties of the reduction, such as split multiplicative
reduction, transfer between minimal models.

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
`FLT/Mathlib/AlgebraicGeometry/EllipticCurve/Reduction.lean`, by Kevin Buzzard — the source commit
is FLT PR #1088, "Quadratic twist to split multiplicative reduction". Four declarations are taken
from it:

* `isMinimal_of_valuation_c₄_eq_one`;
* `valuation_Δ_aux_smul_le`;
* `valuation_Δ_eq_of_isMinimal_smul`;
* `valuation_u_eq_one_of_isMinimal_smul`.

Statements and proofs are taken unchanged, with three deliberate divergences: the section's
variable block is restated here; the `open`s are narrowed to those of Mathlib's own `Minimal`
section; and `valuation_Δ_aux_smul_le` is **private** here where the source exports it, because it
is phrased through the internal `valuation_Δ_aux` rather than the ordinary valuation and exists only
to serve the comparison below.
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

/-! ### Comparing two minimal models

`IsMinimal` says the discriminant valuation is maximal among integral models. Two minimal models of
the same curve therefore pin each other: each is at least as good as the other, so their
valuations agree, and the change of variables between them can only scale `Δ` by a unit. -/

/-- **No integral change of variables increases the discriminant valuation of a minimal model.**
This is the maximality field of `IsMinimal`, with the `MaximalFor` comparison discharged. Kept
private: it is stated through `valuation_Δ_aux`, Mathlib's internal `{v // v ≤ 1}` wrapper, whereas
the results below speak of the ordinary valuation. -/
private theorem valuation_Δ_aux_smul_le {W : WeierstrassCurve K} [hm : IsMinimal R W]
    (D : VariableChange K) (hint : IsIntegral R (D • W)) :
    valuation_Δ_aux R (D • W) ≤ valuation_Δ_aux R ((1 : VariableChange K) • W) :=
  (le_total (valuation_Δ_aux R ((1 : VariableChange K) • W)) (valuation_Δ_aux R (D • W))).elim
    (hm.val_Δ_maximal.2 hint) id

/-- **Two minimal models related by a change of variables have the same discriminant valuation.**
So `v (Δ)` is an invariant of the curve at this place rather than of the chosen model: any two
minimal models of the same curve agree on it, and a consumer may read it off whichever model it
holds. -/
theorem valuation_Δ_eq_of_isMinimal_smul {W₁ W₂ : WeierstrassCurve K} [IsMinimal R W₁]
    [IsMinimal R W₂] (D : VariableChange K) (hD : D • W₁ = W₂) :
    valuation K (maximalIdeal R) W₂.Δ = valuation K (maximalIdeal R) W₁.Δ := by
  -- Antisymmetry: `D` carries `W₁` to `W₂` and `D⁻¹` carries `W₂` back, and by minimality neither
  -- direction can increase the valuation.
  rw [← valuation_Δ_aux_eq_of_isIntegral R W₂, ← valuation_Δ_aux_eq_of_isIntegral R W₁]
  refine le_antisymm (Subtype.coe_le_coe.mpr ?_) (Subtype.coe_le_coe.mpr ?_)
  · have hsub := valuation_Δ_aux_smul_le R D (by rw [hD]; infer_instance)
    rwa [hD, one_smul] at hsub
  · have hW₁eq : W₁ = D⁻¹ • W₂ := by rw [← hD, inv_smul_smul]
    have hsub := valuation_Δ_aux_smul_le R D⁻¹ (by rw [← hW₁eq]; infer_instance)
    rwa [← hW₁eq, one_smul] at hsub

/-- **The scaling factor of a change of variables between two minimal models of an elliptic curve
has valuation `1`.** Over a discrete valuation ring that says `u` is a **unit**: it and its inverse
are both integral, so such a change of variables is as integral as its coordinates allow. This is
the hypothesis `VariableChange.exists_baseChange_eq_of_smul_eq` asks for, and hence the step by
which a property of the reduction transfers between two minimal models of one curve. -/
theorem valuation_u_eq_one_of_isMinimal_smul {W₁ W₂ : WeierstrassCurve K} [IsMinimal R W₁]
    [IsMinimal R W₂] [W₁.IsElliptic] (D : VariableChange K) (hD : D • W₁ = W₂) :
    valuation K (maximalIdeal R) ↑D.u = 1 := by
  -- A change of variables scales `Δ` by `u⁻¹²`. The two discriminant valuations agree and are
  -- nonzero, so `v (u)¹² = 1`, and the value group is torsion-free.
  have hΔ0 : valuation K (maximalIdeal R) W₁.Δ ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr W₁.isUnit_Δ.ne_zero
  have h12 : valuation K (maximalIdeal R) ↑D.u ^ 12 = 1 := by
    have key : valuation K (maximalIdeal R) W₁.Δ
        = (valuation K (maximalIdeal R) ↑D.u)⁻¹ ^ 12 * valuation K (maximalIdeal R) W₁.Δ := by
      conv_lhs => rw [← valuation_Δ_eq_of_isMinimal_smul R D hD, ← hD, variableChange_Δ]
      rw [map_mul, map_pow, Units.val_inv_eq_inv_val, map_inv₀]
    have h1 : (valuation K (maximalIdeal R) ↑D.u)⁻¹ ^ 12 = 1 :=
      mul_right_cancel₀ hΔ0 (key.symm.trans (one_mul _).symm)
    rw [inv_pow] at h1
    exact inv_eq_one.mp h1
  exact (pow_eq_one_iff_of_nonneg zero_le (by norm_num)).mp h12

end WeierstrassCurve

end

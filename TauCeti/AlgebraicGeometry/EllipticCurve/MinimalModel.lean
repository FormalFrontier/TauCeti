/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import TauCeti.AlgebraicGeometry.EllipticCurve.IntegralModel
import TauCeti.AlgebraicGeometry.EllipticCurve.NodePolynomial

/-!
# Minimal models: a criterion, their comparison, and what transfers between them

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
* `WeierstrassCurve.HasSplitMultiplicativeReduction.of_isMinimal_smul`: split multiplicative
  reduction transfers along such a change of variables.

The third is what the last one runs on, though it is only half of what the descent needs.
`v (u) = 1` over a discrete valuation ring says `u` is a unit of `R`; turning that into a change of
variables actually *defined* over `R` is the job of
`WeierstrassCurve.VariableChange.exists_baseChange_eq_of_smul_eq`, which also consumes integrality
of both models. A change of variables defined over `R` is one the reduction can see, and that is
what carries split multiplicativity across.

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
is FLT PR #1088, "Quadratic twist to split multiplicative reduction". Five declarations are taken
from it:

* `isMinimal_of_valuation_c₄_eq_one`;
* `valuation_Δ_aux_smul_le`;
* `valuation_Δ_eq_of_isMinimal_smul`;
* `valuation_u_eq_one_of_isMinimal_smul`;
* `HasSplitMultiplicativeReduction.of_isMinimal_smul`.

The source declaration `HasSplitMultiplicativeReduction.of_isMinimal_smul` no longer exists at
FLT's current head (`9deae05a`), which drops that development entirely; the pinned revision above
is the record of it. It is absent from Mathlib too, whose `IsMinimal` API stops at the pairwise
exclusion of the reduction types and never compares two minimal models.

Statements are taken unchanged except for `of_isMinimal_smul`, which drops the source's
`[IsMinimal R W₁]`: that instance is already implied by its `h₁`, since
`HasSplitMultiplicativeReduction` extends `HasMultiplicativeReduction` extends `IsMinimal`. The
proofs diverge in six places:

* the section's variable block is restated here, and the `open`s are narrowed to those of Mathlib's
  own `Minimal` section (`IsLocalRing` is left closed, since opening it makes `maximalIdeal`
  ambiguous — `ResidueField` is written qualified instead);
* `valuation_Δ_aux_smul_le` is **private** here where the source exports it, because it is phrased
  through the internal `valuation_Δ_aux` rather than the ordinary valuation and exists only to
  serve the comparison below;
* the source's `exists_algebraMap_unit_eq_of_valuation_eq_one` — a separate shim of its own, in
  `FLT/Mathlib/RingTheory/Valuation/Discrete/IsDiscreteValuationRing.lean` — is **not ported**.
  Mathlib has since acquired that file, and with it `associated_of_valuation_eq`, which the three
  lines below call directly. The source obtains the unit in the orientation `u • x = 1` and then
  inverts it; taking `associated_of_valuation_eq 1 ↑D.u` instead lands on `algebraMap R K u = D.u`
  with no inversion at all;
* the source's `exists_variableChange_baseChange_eq_of_smul_eq` is this repository's
  `WeierstrassCurve.VariableChange.exists_baseChange_eq_of_smul_eq`, which is stated over
  `IsIntegrallyClosedIn R K` rather than a discrete valuation ring; instance search discharges it
  here;
* the source's `nodePoly_map_splits_smul_iff` is this repository's existing
  `splits_variableChange_nodePolynomial_map_iff`, and the node polynomial reaches Mathlib's class
  field through `nodePolynomial_def`, since the definition's body is not exposed across the module
  boundary;
* the `⁄K` notation is written `baseChange`, and the source's `show … from rfl` scaffolding for it
  is replaced by a single `congrArg`.
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

/-- **Split multiplicative reduction is an isomorphism invariant of minimal models.** If two
minimal Weierstrass models of an elliptic curve over `K` are related by a change of variables
(`D • W₁ = W₂`), and `W₁` has split multiplicative reduction, then so does `W₂`.

This is what makes split multiplicative reduction a property of the curve at the place rather than
of the equation presenting it. Mathlib's class is stated through a *chosen* integral model, so the
transfer is not definitional: it needs `D` to be defined over `R`. Two results combine to give
that — `valuation_u_eq_one_of_isMinimal_smul` supplies the unit scaling factor, and
`VariableChange.exists_baseChange_eq_of_smul_eq` turns that unit, with integrality of both models,
into the descent. A form of Silverman, *The Arithmetic of Elliptic Curves*, Remark VII.1.3(b), on
the uniqueness of minimal models over a discrete valuation ring. -/
theorem HasSplitMultiplicativeReduction.of_isMinimal_smul {W₁ W₂ : WeierstrassCurve K}
    [IsMinimal R W₂] [W₁.IsElliptic] (D : VariableChange K) (hD : D • W₁ = W₂)
    (h₁ : W₁.HasSplitMultiplicativeReduction R) : W₂.HasSplitMultiplicativeReduction R := by
  -- `W₁` is minimal because it has multiplicative reduction, so that is not a hypothesis.
  have hm₁ := h₁.toHasMultiplicativeReduction
  have : IsMinimal R W₁ := hm₁.toIsMinimal
  -- `v (D.u) = 1`, so `D.u` is the image of a unit of `R` and `D` descends to some `C₀` over `R`.
  have hvu := valuation_u_eq_one_of_isMinimal_smul R D hD
  obtain ⟨u₀, hau⟩ :=
    associated_of_valuation_eq (A := R) 1 (↑D.u : K) (by rw [map_one]; exact hvu.symm)
  rw [Units.smul_def, Algebra.smul_def, mul_one] at hau
  obtain ⟨C₀, hDC₀⟩ := VariableChange.exists_baseChange_eq_of_smul_eq R D hD u₀ hau
  have hW₂eq : (C₀ • W₁.integralModel R).baseChange K = W₂ := by
    rw [WeierstrassCurve.baseChange, ← map_variableChange, ← hD, ← hDC₀]
    exact congrArg _ (baseChange_integralModel_eq R W₁)
  -- `W₂` is again multiplicative, since `v (u) = 1` fixes the valuations of both `Δ` and `c₄`.
  have hc₄eq : valuation K (maximalIdeal R) W₂.c₄ = valuation K (maximalIdeal R) W₁.c₄ := by
    rw [← hD, variableChange_c₄, map_mul]
    simp [hvu]
  have hmult₂ : W₂.HasMultiplicativeReduction R :=
    { badReduction := by rw [valuation_Δ_eq_of_isMinimal_smul R D hD]; exact hm₁.badReduction
      multiplicativeReduction := by rw [hc₄eq]; exact hm₁.multiplicativeReduction }
  -- and its integral model is `C₀ •` that of `W₁`, so their node polynomials split together.
  refine { hmult₂ with splitMultiplicativeReduction := ?_ }
  have hint₂ : W₂.integralModel R = C₀ • W₁.integralModel R :=
    map_injective (IsFractionRing.injective R K)
      ((baseChange_integralModel_eq R W₂).trans hW₂eq.symm)
  rw [hint₂, ← nodePolynomial_def]
  exact (splits_variableChange_nodePolynomial_map_iff
    (algebraMap R (IsLocalRing.ResidueField R)) (W₁.integralModel R) C₀).mpr
      (by rw [nodePolynomial_def]; exact h₁.splitMultiplicativeReduction)

end WeierstrassCurve

end

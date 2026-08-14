/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import TauCeti.Algebra.Polynomial.QuadraticDiscriminant

/-!
# The node polynomial of a Weierstrass curve

When a Weierstrass curve degenerates to a node, the two tangent directions there are the roots of a
quadratic, and the reduction is called *split* exactly when those roots are rational over the
residue field. Mathlib writes that quadratic out inline, in the very definition of
`WeierstrassCurve.HasSplitMultiplicativeReduction`
(`Mathlib/AlgebraicGeometry/EllipticCurve/Reduction.lean`, applied to `W.integralModel R`), but
gives it no name and proves nothing about it. This file names it `WeierstrassCurve.nodePolynomial`
and says when it splits, supplying the criterion the TODO just above that class asks for — *"add
characterization in terms of the discriminant when the characteristic is not 2"* — together with
the characteristic-two counterpart the TODO does not ask for. Restating the class itself through
these criteria needs `integralModel` and belongs to the minimal-model slice, so the TODO is
answered at the level of the polynomial, not yet of the class.

* `WeierstrassCurve.nodePolynomial` is `c₄ T² + a₁ c₄ T - (54 b₆ - 3 b₂ b₄ + a₂ c₄)`, defined over
  any commutative ring;
* `WeierstrassCurve.nodePolynomial_coeff_zero` reads off the constant coefficient, which is *minus*
  `54 b₆ - 3 b₂ b₄ + a₂ c₄` since the definition subtracts that combination. It is the projection
  through which `QuadraticTwist.lean` states how twisting moves this coefficient;
* `WeierstrassCurve.discrim_nodePolynomial` computes its discriminant as `-c₄ c₆`. This is the
  number the twist lane needs: twisting by `(t, n)` scales `-c₄ c₆` by `(t² - 4n)⁵`, i.e. by the
  twisting parameter times a square, so twisting by the right square class moves the discriminant
  into the squares;
* `WeierstrassCurve.map_nodePolynomial` is naturality, `(W.map φ).nodePolynomial =
  W.nodePolynomial.map φ`. It is what lets the criteria below — stated for `W.nodePolynomial.map φ`,
  i.e. for the *reduction* of the node polynomial — be read as statements about the node polynomial
  of the reduced curve;
* `WeierstrassCurve.variableChange_nodePolynomial` and
  `WeierstrassCurve.splits_variableChange_nodePolynomial_map_iff`: a change of variables `(u, r, s,
  t)` transforms the node polynomial by the affine substitution `T ↦ u T + s` and the unit scalar
  `u⁻⁶`, so whether it splits is an isomorphism invariant. This is why split multiplicative
  reduction is a property of the curve and not of the equation;
* `WeierstrassCurve.splits_nodePolynomial_map_iff_isSquare` and
  `WeierstrassCurve.splits_nodePolynomial_map_iff_exists_artinSchreier_of_two_eq_zero`: the
  splitting criteria themselves, each needing only `c₄` to survive the map. Away from residue
  characteristic two it splits iff the image of `-c₄ c₆` is a square; in residue characteristic
  two, where that says nothing, iff an Artin-Schreier condition holds. Both come from the general
  quadratic criteria of `TauCeti/Algebra/Polynomial/QuadraticDiscriminant.lean`.

Nothing here assumes a valuation or a reduction: every statement is about a Weierstrass curve over
a commutative ring and a ring homomorphism to a field, so it applies to any reduction map one later
chooses. They advance `TauCetiRoadmap/EllipticCurves/README.md` §Layer 5 (twists), whose headline
`exists_quadraticTwist_hasSplitMultiplicativeReduction` — a curve with nonsplit multiplicative
reduction acquires split reduction after a separable quadratic twist — carries no residue-
characteristic hypothesis, so it needs both criteria: away from residue characteristic two one
feeds the twist's scaling of `-c₄ c₆` into `splits_nodePolynomial_map_iff_isSquare`, and in residue
characteristic two the route is
`splits_nodePolynomial_map_iff_exists_artinSchreier_of_two_eq_zero`.

Adapted from the FLT project (`ImperialCollegeLondon/FLT`, at the roadmap's pin `bc2fe8ff7396`, FLT
PR #1088, Apache 2.0): the node-polynomial block of
`FLT/Mathlib/AlgebraicGeometry/EllipticCurve/Reduction.lean`, together with
`splitPolynomial_discrim` from `FLT/Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean`,
renamed here to `discrim_nodePolynomial` because `splitPolynomial` names no declaration. Those
files' headers read `Authors: Kevin Buzzard, William Coram, Claude` and `Authors: Kevin Buzzard,
Claude`; following this repository's convention for adapted material, the upstream authorship is
credited here rather than in the copyright header. Ported with the source's `@[expose]` dropped,
and with the minimal-model and multiplicative-reduction blocks of the source file left to the PR
that consumes them.
-/

public section

namespace WeierstrassCurve

variable {A : Type*} [CommRing A] {B : Type*} [CommRing B] {k : Type*} [Field k]

/-- The **node polynomial** `c₄ T² + a₁ c₄ T - (54 b₆ - 3 b₂ b₄ + a₂ c₄)`, whose roots are the
slopes of the two tangent directions at the node of a multiplicative reduction. This is the
polynomial Mathlib writes out inline in `WeierstrassCurve.HasSplitMultiplicativeReduction`, which
asks for the splitting over the residue field of this polynomial formed from the *integral model*
`W.integralModel R`, as its one extra condition on top of `HasMultiplicativeReduction`. -/
noncomputable def nodePolynomial (W : WeierstrassCurve A) : Polynomial A :=
  .C W.c₄ * .X ^ 2 + .C (W.a₁ * W.c₄) * .X - .C (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄)

/-- The defining formula for the node polynomial. The definition's body is not exposed across the
module boundary, so this is how downstream modules see it;
`nodePolynomial_map_eq_quadratic` is the corresponding statement for its image under a ring
homomorphism. -/
lemma nodePolynomial_def (W : WeierstrassCurve A) :
    W.nodePolynomial = .C W.c₄ * .X ^ 2 + .C (W.a₁ * W.c₄) * .X
      - .C (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄) := by
  simp only [nodePolynomial]

/-- The constant coefficient of the node polynomial. Note the sign: `nodePolynomial` *subtracts*
`54 b₆ - 3 b₂ b₄ + a₂ c₄`, so `coeff 0` is minus that combination, not it.

Deliberately not `@[simp]`: the normal form wanted downstream rewrites a twisted curve's
coefficient back to the base curve's (`nodePolynomial_coeff_zero_quadraticTwistOf`), and that
lemma's left-hand side is exactly this one's, so tagging both would make the twist lemma
non-normal-form. -/
lemma nodePolynomial_coeff_zero (W : WeierstrassCurve A) :
    W.nodePolynomial.coeff 0 = -(54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄) := by
  simp [nodePolynomial_def]

/-- The discriminant of the node polynomial is `-c₄ c₆`. Hence — away from residue characteristic
two, and provided `c₄` survives the reduction — the tangent directions at the node are rational
over the residue field exactly when the image of `-c₄ c₆` is a square there
(`splits_nodePolynomial_map_iff_isSquare`); twisting by `(t, n)` multiplies `-c₄ c₆` by
`(t² - 4n)⁵ = (t² - 4n)⁴ · (t² - 4n)`, i.e. by the twisting parameter up to a square. -/
theorem discrim_nodePolynomial (W : WeierstrassCurve A) :
    discrim W.c₄ (W.a₁ * W.c₄) (-(54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄))
      = -(W.c₄ * W.c₆) := by
  simp only [discrim, c₄, c₆, b₂, b₄, b₆]; ring

/-- The node polynomial is natural in the coefficient ring: it commutes with base change of the
Weierstrass equation along any ring homomorphism. -/
@[simp]
lemma map_nodePolynomial (φ : A →+* B) (W : WeierstrassCurve A) :
    (W.map φ).nodePolynomial = W.nodePolynomial.map φ := by
  simp only [nodePolynomial, WeierstrassCurve.map_c₄, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_b₂,
    WeierstrassCurve.map_b₄, WeierstrassCurve.map_b₆, WeierstrassCurve.map_a₂, Polynomial.map_add,
    Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
    Polynomial.map_ofNat, map_add, map_sub, map_mul, map_ofNat]

/-- The reduced node polynomial, presented as a quadratic with an additive constant term — the
shape `C a * X ^ 2 + C b * X + C c` that the criteria of
`TauCeti/Algebra/Polynomial/QuadraticDiscriminant.lean` consume. -/
lemma nodePolynomial_map_eq_quadratic (φ : A →+* B) (W : WeierstrassCurve A) :
    W.nodePolynomial.map φ = .C (φ W.c₄) * .X ^ 2 + .C (φ (W.a₁ * W.c₄)) * .X
      + .C (-φ (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄)) := by
  simp only [nodePolynomial, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X]
  rw [map_neg, sub_eq_add_neg]

/-- The image of `discrim_nodePolynomial` under a ring homomorphism, in the shape produced by the
quadratic criteria applied to `nodePolynomial_map_eq_quadratic`. -/
lemma discrim_map_nodePolynomial (φ : A →+* B) (W : WeierstrassCurve A) :
    discrim (φ W.c₄) (φ (W.a₁ * W.c₄)) (-φ (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄))
      = φ (-(W.c₄ * W.c₆)) := by
  have h := congrArg φ W.discrim_nodePolynomial
  simp only [discrim, map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat] at h ⊢
  linear_combination h

/-- A power of the constant polynomial `u⁻¹` absorbs any smaller power of the constant
polynomial `u`. -/
private lemma C_inv_pow_mul_C_pow (u : Aˣ) (m n : ℕ) :
    Polynomial.C (↑u⁻¹ : A) ^ (m + n) * Polynomial.C (↑u : A) ^ n
      = Polynomial.C (↑u⁻¹ : A) ^ m := by
  have hCu : Polynomial.C (↑u⁻¹ : A) * Polynomial.C (↑u : A) = 1 := by
    rw [← Polynomial.C_mul, u.inv_mul, Polynomial.C_1]
  rw [pow_add, mul_assoc, pow_mul_pow_eq_one n hCu, mul_one]

/-- Under a change of variables `C = (u, r, s, t)`, the node polynomial transforms by the affine
substitution `T ↦ u T + s` and the unit scalar `u⁻⁶` — reflecting that the tangent slopes `λ`
transform as `λ ↦ (λ - s)/u`. Over a field this makes splitting invariant; see
`splits_variableChange_nodePolynomial_map_iff`. -/
lemma variableChange_nodePolynomial (W : WeierstrassCurve A) (C : VariableChange A) :
    (C • W).nodePolynomial = .C ((↑C.u⁻¹ : A) ^ 6)
      * W.nodePolynomial.comp (.C (↑C.u : A) * .X + .C C.s) := by
  -- `ring` treats `↑u` and `↑u⁻¹` as unrelated constants, so the two cancellations it needs are
  -- supplied to `linear_combination`: `e2` corrects the `X²` coefficient, where the scalar `u⁻⁶`
  -- meets the `u²` from `(uX + s)²`, and `e1` the `X` coefficient, where it meets a single `u`.
  have e2 := C_inv_pow_mul_C_pow C.u 4 2
  have e1 := C_inv_pow_mul_C_pow C.u 5 1
  have hc₄ : Polynomial.C W.c₄ = Polynomial.C W.b₂ ^ 2 - 24 * Polynomial.C W.b₄ := by
    rw [c₄]
    simp only [Polynomial.C_sub, Polynomial.C_mul, Polynomial.C_pow, map_ofNat]
  simp only [nodePolynomial, variableChange_a₁, variableChange_a₂, variableChange_c₄,
    variableChange_b₂, variableChange_b₄, variableChange_b₆, Polynomial.mul_comp,
    Polynomial.add_comp, Polynomial.sub_comp, Polynomial.C_comp, Polynomial.X_comp, pow_two,
    mul_add, add_mul, mul_sub, sub_mul, Polynomial.C_mul, Polynomial.C_add, Polynomial.C_sub,
    Polynomial.C_pow, map_ofNat, Polynomial.ofNat_comp]
  -- the `r`-shift contributes `c₄` through `variableChange_a₂`, in expanded form
  linear_combination (-Polynomial.C W.c₄ * Polynomial.X ^ 2) * e2
    + (-(2 * Polynomial.C W.c₄ * Polynomial.C C.s + Polynomial.C W.a₁ * Polynomial.C W.c₄)
        * Polynomial.X) * e1
    + (-3 * Polynomial.C (↑C.u⁻¹ : A) ^ 6 * Polynomial.C C.r) * hc₄

/-- **Invariance of the node polynomial's splitting under change of variables.** Since a change of
variables transforms the node polynomial by an affine substitution and a unit scalar
(`variableChange_nodePolynomial`), whether it splits over a field `k` is unchanged. This is what
makes split multiplicative reduction an isomorphism invariant rather than a property of the
equation. -/
lemma splits_variableChange_nodePolynomial_map_iff (φ : A →+* k) (W : WeierstrassCurve A)
    (C : VariableChange A) :
    ((C • W).nodePolynomial.map φ).Splits ↔ (W.nodePolynomial.map φ).Splits := by
  have hu : φ (↑C.u : A) ≠ 0 := (RingHom.isUnit_map φ C.u.isUnit).ne_zero
  have hu6 : φ ((↑C.u⁻¹ : A) ^ 6) ≠ 0 := by
    rw [map_pow]; exact pow_ne_zero 6 (RingHom.isUnit_map φ C.u⁻¹.isUnit).ne_zero
  simp only [variableChange_nodePolynomial, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_comp, Polynomial.map_add, Polynomial.map_X]
  rw [Polynomial.splits_mul_iff_right (Polynomial.C_ne_zero.mpr hu6) (Polynomial.Splits.C _)]
  exact (Polynomial.splits_iff_comp_splits_of_natDegree_eq_one
    (Polynomial.natDegree_linear hu)).symm

/-- **Split criterion away from residue characteristic two.** Over a field `k` with `2 ≠ 0`, and
provided `c₄` does not die under `φ` — the condition that makes the reduced polynomial genuinely
quadratic, and which multiplicative reduction supplies — the node polynomial splits, i.e. the two
tangent directions at the node are `k`-rational, exactly when `φ (-(c₄ * c₆))`, the image of its
discriminant (`discrim_nodePolynomial`), is a square in `k`. This answers Mathlib's TODO in
`Reduction.lean` at the level of the node polynomial; restating
`HasSplitMultiplicativeReduction` itself through it needs `integralModel`. It is also the tool
that, applied to a quadratic twist via the scaling
`-c₄' c₆' = (t² - 4n)⁵ · (-c₄ c₆)`, turns a nonsplit reduction into a split one after twisting by
the right square class. -/
lemma splits_nodePolynomial_map_iff_isSquare [NeZero (2 : k)] (φ : A →+* k) (W : WeierstrassCurve A)
    (hc₄ : φ W.c₄ ≠ 0) :
    (W.nodePolynomial.map φ).Splits ↔ IsSquare (φ (-(W.c₄ * W.c₆))) := by
  rw [nodePolynomial_map_eq_quadratic, Polynomial.splits_quadratic_iff_isSquare hc₄,
    discrim_map_nodePolynomial]

/-- **Split criterion in residue characteristic two.** Over a field `k` of characteristic `2`,
where the square-class criterion `splits_nodePolynomial_map_iff_isSquare` says nothing, the node
polynomial splits exactly when its Artin-Schreier invariant lies in the image of `z ↦ z² + z`.
Only `c₄` need be assumed nonzero: in characteristic two `1728 = 0`, so `c_relation` reads
`c₄³ = c₆²` and `c₆ ≠ 0` comes for free. Together they force the linear coefficient `a₁ c₄` to be
nonzero, which is what makes the criterion applicable. -/
lemma splits_nodePolynomial_map_iff_exists_artinSchreier_of_two_eq_zero (h2 : (2 : k) = 0)
    (φ : A →+* k) (W : WeierstrassCurve A) (hc₄ : φ W.c₄ ≠ 0) :
    (W.nodePolynomial.map φ).Splits ↔ ∃ z, φ (W.a₁ * W.c₄) ^ 2 * (z ^ 2 + z)
      = φ W.c₄ * (-φ (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄)) := by
  -- `1728 = 0` in characteristic two, so `c_relation` gives `φ c₄ ^ 3 = φ c₆ ^ 2`.
  have hc₆ : φ W.c₆ ≠ 0 := by
    intro h0
    refine hc₄ (pow_eq_zero_iff three_ne_zero |>.mp ?_)
    have h := congrArg φ W.c_relation
    have h1728 : (1728 : k) = 0 := by linear_combination (864 : k) * h2
    simp only [map_mul, map_sub, map_pow, map_ofNat] at h
    linear_combination -h + φ W.Δ * h1728 + φ W.c₆ * h0
  -- In characteristic two the discriminant is the square of the linear coefficient
  -- (`discrim_eq_sq_of_two_eq_zero`), and it equals `φ (-(c₄ c₆)) ≠ 0`, so that coefficient is
  -- nonzero — which is what makes the Artin-Schreier criterion applicable.
  have hb : φ (W.a₁ * W.c₄) ≠ 0 := by
    intro h0
    refine neg_ne_zero.mpr (mul_ne_zero hc₄ hc₆) ?_
    rw [← map_mul, ← map_neg, ← discrim_map_nodePolynomial φ W,
      discrim_eq_sq_of_two_eq_zero h2, h0, zero_pow two_ne_zero]
  rw [nodePolynomial_map_eq_quadratic,
    Polynomial.splits_quadratic_iff_exists_artinSchreier_of_two_eq_zero h2 hc₄ hb]

end WeierstrassCurve

end

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.SMul
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Separating
public import TauCeti.FieldTheory.FunctionField.Differential.Kaehler

/-!
# The invariant differential of an elliptic curve

For an elliptic curve `E` over a field `F` this file constructs the invariant differential
`ω = dx / (2y + a₁x + a₃)` inside the module of Kähler differentials `Ω[K(E)/F]` of the
function field, and proves that `ω` is a basis: `Ω[K(E)/F]` is a one-dimensional `K(E)`-vector
space, so every differential of `K(E)` is `c • ω` for a unique `c ∈ K(E)`.

The imported function-field API proves that `x` is a separating element of `K(E)/F`. The general
separating-element API then says that `dx` is a basis of the Kähler differentials; rescaling it
by `W_Y⁻¹` gives the invariant-differential basis.

## Main definitions

* `WeierstrassCurve.Affine.invariantDifferentialDenom`: the denominator `2y + a₁x + a₃`.
* `WeierstrassCurve.Affine.invariantDifferential`: the invariant differential `ω`, as an
  element of `Ω[K(E)/F]`.
* `WeierstrassCurve.Affine.invariantDifferentialBasis`: `ω` as a basis of `Ω[K(E)/F]`.

## Main results

* `WeierstrassCurve.Affine.invariantDifferentialDenom_ne_zero`: the denominator is nonzero.
* `WeierstrassCurve.Affine.existsUnique_smul_invariantDifferential`: every differential is
  `c • ω` for a unique `c`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1 and III.5.

Silverman's III.1.5 says more than anything proved here: that `div ω = 0`, so that `ω` is
regular and nonvanishing at every point. This file proves that `ω` is a *basis* of
`Ω[K(E)/F]`, which does not imply that — a nonzero rational differential may have both zeros
and poles. The divisor statement needs a pointwise regularity and nonvanishing theory not
developed here.

## Provenance

Ported from the AINTLIB `HasseWeil` project (Chris Birkbeck), Apache-2.0, at commit
`513e83879e2f`: `HasseWeil/InvariantDifferential.lean` (`D_x_ne_zero`, `denom_ne_zero`,
`invariantDifferential` and `invariantDifferential_ne_zero`) and
`HasseWeil/FormalGroupCorrespondence.lean` (`kaehler_rank_one`, the one-dimensionality, proved
there by the same span-of-`dx` argument).
-/

public section

open Polynomial Polynomial.Bivariate

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] (E : WeierstrassCurve.Affine F)

/-! ### The denominator `2y + a₁x + a₃` -/

/-- The denominator `2y + a₁x + a₃` of the invariant differential, as an element of `K(E)`. It
is the value at the generic point of the partial derivative `W_Y = polynomialY`, which is
`invariantDifferentialDenom_eq_evalEval_polynomialY`;
`invariantDifferentialDenom_ne_zero` shows it is nonzero when `E` is elliptic. The converse
fails: `y² = x³` over `ℚ` is singular, yet its `W_Y = 2y` is nonzero. -/
noncomputable def invariantDifferentialDenom : E.FunctionField :=
  2 * genericY E + algebraMap F E.FunctionField E.a₁ * genericX E +
    algebraMap F E.FunctionField E.a₃

/-- The defining formula for `invariantDifferentialDenom`. -/
theorem invariantDifferentialDenom_def :
    invariantDifferentialDenom E =
      2 * genericY E + algebraMap F E.FunctionField E.a₁ * genericX E +
        algebraMap F E.FunctionField E.a₃ :=
  (rfl)

/-- **The denominator is `W_Y` at the generic point.** This is the reading that makes it the
denominator of `ω = dx / W_Y`. -/
theorem invariantDifferentialDenom_eq_evalEval_polynomialY :
    invariantDifferentialDenom E =
      (E⁄E.FunctionField).toAffine.polynomialY.evalEval (genericX E) (genericY E) := by
  rw [evalEval_polynomialY]
  simp only [invariantDifferentialDenom_def, WeierstrassCurve.baseChange,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]

/-- **The denominator of the invariant differential is nonzero.** It is the image of `W_Y` in
`K(E)`, and `W_Y` is a nonzero polynomial of degree below `deg W`, so it survives both
`F[X][Y] → F[E]` and `F[E] → K(E)`. -/
@[simp]
theorem invariantDifferentialDenom_ne_zero [E.IsElliptic] :
    invariantDifferentialDenom E ≠ 0 := by
  rw [invariantDifferentialDenom_eq_evalEval_polynomialY]
  exact evalEval_polynomialY_genericX_genericY_ne_zero E

/-! ### The invariant differential -/

/-- The invariant differential `ω = dx / (2y + a₁x + a₃)`, as an element of `Ω[K(E)/F]`. -/
noncomputable def invariantDifferential :
    KaehlerDifferential F E.FunctionField :=
  (invariantDifferentialDenom E)⁻¹ • KaehlerDifferential.D F E.FunctionField (genericX E)

/-- The defining formula for `invariantDifferential`. The definition body is not exposed, so this
equation lemma is how a consumer in another module computes with it. Not `@[simp]`: the point of
naming `invariantDifferentialDenom` is that the nonvanishing results can be stated over it, which
unfolding everywhere would defeat. -/
theorem invariantDifferential_def :
    invariantDifferential E =
      (invariantDifferentialDenom E)⁻¹ •
        KaehlerDifferential.D F E.FunctionField (genericX E) :=
  (rfl)

/-- **The invariant differential is nonzero** as an element of `Ω[K(E)/F]`. It is the product of
an inverse of the nonzero denominator with `dx`, both nonzero. -/
@[simp]
theorem invariantDifferential_ne_zero [E.IsElliptic] : invariantDifferential E ≠ 0 := by
  rw [invariantDifferential_def]
  exact smul_ne_zero (inv_ne_zero (invariantDifferentialDenom_ne_zero E))
    (TauCeti.D_ne_zero_of_separating (transcendental_genericX E))

/-- **The invariant differential spans `Ω[K(E)/F]`**: it differs from `dx` by an invertible
scalar. -/
theorem span_invariantDifferential_eq_top [E.IsElliptic] :
    Submodule.span E.FunctionField {invariantDifferential E} = ⊤ := by
  rw [invariantDifferential_def,
    Submodule.span_singleton_smul_eq
      (IsUnit.mk0 _ (inv_ne_zero (invariantDifferentialDenom_ne_zero E))),
    TauCeti.span_D_eq_top_of_separating (transcendental_genericX E)]

/-- **`ω` is a basis of `Ω[K(E)/F]`**, the module being one-dimensional and `ω` nonzero. -/
noncomputable def invariantDifferentialBasis [E.IsElliptic] :
    Module.Basis Unit E.FunctionField (KaehlerDifferential F E.FunctionField) :=
  (TauCeti.kaehlerBasisOfSeparating (transcendental_genericX E)).unitsSMul
    (fun _ => Units.mk0 (invariantDifferentialDenom E)⁻¹
      (inv_ne_zero (invariantDifferentialDenom_ne_zero E)))

/-- The unique `Unit`-indexed vector of `invariantDifferentialBasis` is the invariant differential
`ω`. -/
@[simp]
theorem invariantDifferentialBasis_apply [E.IsElliptic] (i : Unit) :
    invariantDifferentialBasis E i = invariantDifferential E :=
  by
    rw [invariantDifferentialBasis, Module.Basis.unitsSMul_apply,
      TauCeti.kaehlerBasisOfSeparating_apply, Units.smul_def]
    exact (invariantDifferential_def E).symm

/-- **Every differential of `K(E)` is `c • ω` for a unique `c ∈ K(E)`.** This is the form the
differential calculus of isogenies consumes: the pullback coefficient of an isogeny `φ` is the
scalar attached to `φ^*ω` by this statement. -/
theorem existsUnique_smul_invariantDifferential [E.IsElliptic]
    (η : KaehlerDifferential F E.FunctionField) :
    ∃! c : E.FunctionField, c • invariantDifferential E = η := by
  have hmem : η ∈ Submodule.span E.FunctionField {invariantDifferential E} := by
    rw [span_invariantDifferential_eq_top E]; trivial
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  refine ⟨c, hc, fun c' hc' => ?_⟩
  have h := hc'.trans hc.symm
  rw [← sub_eq_zero, ← sub_smul] at h
  rcases smul_eq_zero.mp h with h' | h'
  · exact sub_eq_zero.mp h'
  · exact absurd h' (invariantDifferential_ne_zero E)

end WeierstrassCurve.Affine

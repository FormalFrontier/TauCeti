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

The file also records the **chain rule** obtained by differentiating the Weierstrass relation:
`W_X · dx + W_Y · dy = 0`, where the coefficients are the two partial derivatives of the
Weierstrass polynomial evaluated at the generic point.

## Main definitions

* `WeierstrassCurve.Affine.invariantDifferentialDenom`: the denominator `2y + a₁x + a₃`.
* `WeierstrassCurve.Affine.invariantDifferential`: the invariant differential `ω`, as an
  element of `Ω[K(E)/F]`.
* `WeierstrassCurve.Affine.invariantDifferentialBasis`: `ω` as a basis of `Ω[K(E)/F]`.

## Main results

* `WeierstrassCurve.Affine.polynomialX_smul_D_genericX_add_polynomialY_smul_D_genericY_eq_zero`:
  the chain rule `W_X · dx + W_Y · dy = 0`.
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

The proofs are reorganised here, and the reorganisation is what removes the source's two
overrides: `D_x_ne_zero` carried a `maxHeartbeats` override and `kaehler_rank_one` carried a
larger one, while no declaration here needs any. The source's `[DecidableEq F]` hypothesis is
also dropped. Its direct span-of-`dx` proof is replaced by the general separating-element API in
`TauCeti.FieldTheory.FunctionField.Differential.Kaehler`; the curve-specific separability input is
provided by `Affine.FunctionField.Separating`. The Weierstrass relation itself,
which the source re-derives inside `AdjoinRoot`, is the existing `equation_genericX_genericY`.
The chain rule, the basis and the uniqueness statement are stated here and are not in the
source, which proves only `Module.finrank = 1`.

Sources swept for the same material and not carrying it:
`github.com/MichaelStollBayreuth/EllipticCurves` @ `449c7b936813` and
`github.com/ImperialCollegeLondon/FLT`, whose only mentions of `KaehlerDifferential` are in
Henselian-local-ring files; and pinned Mathlib, which computes `Module.rank Ω[S⁄R]` only for
standard smooth presentations (`RingTheory/Smooth/StandardSmoothCotangent.lean`), a hypothesis
not available here.
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
denominator of `ω = dx / W_Y`, and it is the form the chain rule below produces. -/
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

/-! ### The chain rule -/

/-- The differential of the quadratic side `y² + a₁xy + a₃y` of the Weierstrass relation. -/
private lemma D_quadratic_side :
    KaehlerDifferential.D F E.FunctionField
        (genericY E ^ 2 + algebraMap F E.FunctionField E.a₁ * genericX E * genericY E +
          algebraMap F E.FunctionField E.a₃ * genericY E) =
      (2 * genericY E + algebraMap F E.FunctionField E.a₁ * genericX E +
          algebraMap F E.FunctionField E.a₃) •
          KaehlerDifferential.D F E.FunctionField (genericY E) +
        (algebraMap F E.FunctionField E.a₁ * genericY E) •
          KaehlerDifferential.D F E.FunctionField (genericX E) := by
  simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, Derivation.map_algebraMap,
    smul_zero, add_zero, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, smul_smul,
    ← Nat.cast_smul_eq_nsmul E.FunctionField]
  rw [mul_comm (genericY E) (algebraMap F E.FunctionField E.a₁), add_smul, add_smul]
  abel

/-- The differential of the cubic side `x³ + a₂x² + a₄x + a₆` of the Weierstrass relation. -/
private lemma D_cubic_side :
    KaehlerDifferential.D F E.FunctionField
        (genericX E ^ 3 + algebraMap F E.FunctionField E.a₂ * genericX E ^ 2 +
          algebraMap F E.FunctionField E.a₄ * genericX E + algebraMap F E.FunctionField E.a₆) =
      (3 * genericX E ^ 2 + 2 * algebraMap F E.FunctionField E.a₂ * genericX E +
          algebraMap F E.FunctionField E.a₄) •
        KaehlerDifferential.D F E.FunctionField (genericX E) := by
  simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, Derivation.map_algebraMap,
    smul_zero, add_zero, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, smul_smul,
    ← Nat.cast_smul_eq_nsmul E.FunctionField]
  rw [← add_smul, ← add_smul]
  congr 1
  ring

/-- **The chain rule for the Weierstrass relation**: `W_X · dx + W_Y · dy = 0` in `Ω[K(E)/F]`,
the two coefficients being the partial derivatives of the Weierstrass polynomial evaluated at
the generic point. It holds for every Weierstrass curve, singular ones included: it is the
differential of the relation `equation_genericX_genericY`, which needs no hypothesis.

Ellipticity enters only afterwards, through `invariantDifferentialDenom_ne_zero`, which is what
lets the identity be solved for `dy`. -/
theorem polynomialX_smul_D_genericX_add_polynomialY_smul_D_genericY_eq_zero :
    (E⁄E.FunctionField).toAffine.polynomialX.evalEval (genericX E) (genericY E) •
        KaehlerDifferential.D F E.FunctionField (genericX E) +
      (E⁄E.FunctionField).toAffine.polynomialY.evalEval (genericX E) (genericY E) •
        KaehlerDifferential.D F E.FunctionField (genericY E) = 0 := by
  have h := equation_genericX_genericY E
  rw [WeierstrassCurve.Affine.equation_iff] at h
  rw [evalEval_polynomialX, evalEval_polynomialY]
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at h ⊢
  have key := congrArg (KaehlerDifferential.D F E.FunctionField) h
  rw [D_quadratic_side, D_cubic_side] at key
  rw [sub_smul, ← key]
  abel

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

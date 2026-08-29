/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.GenericPoint
public import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.ZSMul
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Basic
-- Both `ΨSq ≠ 0` lemmas are used only inside proofs below, so both imports are private:
-- Mathlib's `ΨSq_ne_zero` for the characteristic-conditional discharge, and this repository's
-- `ΨSq_ne_zero_of_Δ_ne_zero` for the characteristic-free one.
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Coprimality

/-!
# The coordinate pullback of multiplication by `n`, for every nonzero `n`

`Isogeny/Basic.lean` gives the identity coordinate pullback and `Isogeny/Frobenius.lean` gives
the Frobenius one. This file gives `[n]`: multiplication by `n` pulls back to a map
`W.CoordinateRing →ₐ[F] W.FunctionField` wherever `ψₙ` does not vanish at the generic point.

**That non-vanishing is available for every `n ≠ 0` once the curve is nonsingular**, so this
file constructs `[n]` in every characteristic, `[p]` in characteristic `p` included. Two lemmas
discharge it and neither subsumes the other: `psiFunctionField_ne_zero` from `(n : F) ≠ 0`,
which needs no nonsingularity, and `psiFunctionField_ne_zero_of_Δ_ne_zero` from `W.Δ ≠ 0` and
`n ≠ 0`, which needs no hypothesis on the characteristic. `mulByIntPullback` itself, and
everything it is built from, carry neither: they ask for `psiFunctionField W n ≠ 0` directly.

The construction is the division-polynomial formula read at the *generic* point. The coordinate
ring `W.CoordinateRing` is `F[X][Y]` modulo the Weierstrass relation, so the pair `(X, Y)` is
itself a point of `W` over the function field `W.FunctionField` — the generic point. `n` times
it has coordinates `φₙ / ψₙ²` and `ωₙ / ψₙ³` by the division-polynomial formulas, and sending
`X` and `Y` there is exactly a coordinate pullback.

## What is not here

The `MapsInfinity` condition, and so `[n]` as an `Isogeny W W`, are not proved here. Neither
criterion `Isogeny/Basic.lean` offers applies directly: `mapsInfinity_of_pow` wants a fixed
power of every coordinate function to be pulled back, which is the Frobenius shape and not this
one, and `mapsInfinity_iff_isEquiv_comap_infinityPlace` wants the induced map of *function
fields*, which is available only after the pullback below is known injective. That chain —
injectivity, the function-field map, then the place comparison — is its own topic and its own
file. Note the order of dependence: `Isogeny/FunctionField.lean` proves transcendence,
injectivity and the field pullback for *any* isogeny, but each of those consumes
`mapsInfinity`, so none of them can be used to establish it.

Every definition here is paired with a `_def` equation lemma, because a `def`'s body is not
exposed across the module boundary even inside a `public section`: a downstream
`simp only [mulByIntX]` is rejected with *Expected a definition with an exposed body*. Without
them the file cannot be computed with from outside at all.

One fact is the whole content here: `equation_mulByInt`, that the pair `(φₙ/ψₙ², ωₙ/ψₙ³)`
satisfies the equation of the base-changed curve. It is *not* a polynomial identity to be
checked; it holds because `n • P` is a point of the curve whenever `P` is, which is
`WeierstrassCurve.zsmul_point_eq_smulEval` at the generic point.

That the generic point is itself a point of the curve — the other half of the argument — lives
in `Affine/FunctionField/GenericPoint.lean` as `WeierstrassCurve.Affine.equation_genericPoint`,
since it is about `W` and not about `[n]`.

## Main definitions

* `TauCeti.Isogeny.mulByIntX`, `TauCeti.Isogeny.mulByIntY`: the rational expressions
  `φₙ/ψₙ²` and `ωₙ/ψₙ³`, the coordinates of `[n]` at the generic point where `ψₙ ≠ 0`.
* `TauCeti.Isogeny.mulByIntPullback`: the coordinate pullback of `[n]`, given `ψₙ ≠ 0`.
* `TauCeti.Isogeny.mulByIntPullbackOfNeZero`: its specialisation to `n ≠ 0` on an elliptic
  curve, where the non-vanishing is discharged.

The generic point itself (`genericX`, `genericY`, `functionFieldCurve`) is not defined here; it
is `WeierstrassCurve.Affine`'s, in `Affine/FunctionField/GenericPoint.lean`.

## Main results

* `TauCeti.Isogeny.equation_mulByInt`: the coordinates of `[n]` satisfy the equation of `W` over
  its function field.
* `TauCeti.Isogeny.psiFunctionField_ne_zero`: `ψₙ` does not vanish at the generic point when
  `(n : F) ≠ 0`, needing no nonsingularity.
* `TauCeti.Isogeny.psiFunctionField_ne_zero_of_Δ_ne_zero`: the same conclusion from `W.Δ ≠ 0`
  and `n ≠ 0`, with no hypothesis on the characteristic. These are the two discharges of
  `mulByIntPullback`'s hypothesis; neither subsumes the other.
* `TauCeti.Isogeny.mulByIntPullback_mk`: the pullback of an arbitrary class, as evaluation of a
  bivariate polynomial at `(φₙ/ψₙ², ωₙ/ψₙ³)`, with `TauCeti.Isogeny.mulByIntPullback_X` and
  `TauCeti.Isogeny.mulByIntPullback_Y` its values on the two coordinates.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4 and the
  division-polynomial formulas of Exercise 3.7.
* Adapted from the AINTLIB `HasseWeil` project (Chris Birkbeck),
  [`HasseWeil/MulByIntPullback.lean`](https://github.com/CBirkbeck/AINTLIB), Apache-2.0, at commit
  `513e83879e2f8cbc626eb9e04d660e92be16ccba`, declarations `x_gen`, `y_gen`, `W_KE`,
  `generic_equation`, `Φ_ff`, `ΨSq_ff`, `ψ_ff`, `ω_ff`, `mulByInt_x`, `mulByInt_y`,
  `mulByInt_xHom`, `mulByInt_weierstrass` and `mulByInt_coordHom`. The source stops at a
  `RingHom` out of the coordinate ring and then builds its own function-field pullback,
  injectivity and transcendence statements by hand; here the ring hom is upgraded to the
  `AlgHom` that `TauCeti.CoordinatePullback` already asks for. The source's function-field
  pullback, injectivity and transcendence are **not** ported and **not** reproved here: they are
  deferred until `MapsInfinity` is available, because each of the corresponding general results
  in `Isogeny/FunctionField.lean` consumes it. See "What is not here".
-/

public section

open Polynomial WeierstrassCurve

open scoped Polynomial.Bivariate

namespace TauCeti

variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)

namespace Isogeny

/-- The image of the division polynomial `ψₙ` in the function field, i.e. `ψₙ` evaluated at the
generic point. Its non-vanishing is the hypothesis every construction below carries. -/
noncomputable def psiFunctionField (n : ℤ) : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (Affine.CoordinateRing.mk W (W.ψ n))

/-- The image of the division polynomial `ωₙ` in the function field. -/
noncomputable def omegaFunctionField (n : ℤ) : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (Affine.CoordinateRing.mk W (W.ω n))

/-- The image of the division polynomial `φₙ` in the function field. -/
noncomputable def phiFunctionField (n : ℤ) : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (Affine.CoordinateRing.mk W (W.φ n))

/-- The rational division-polynomial expression `φₙ / ψₙ²`.

This is the `x`-coordinate of `[n]` at the generic point exactly when `ψₙ` does not vanish
there; at a zero of `ψₙ` the quotient is junk, since `[n]` sends that point to infinity, which
has no affine coordinate. Every result about it below therefore carries `ψₙ ≠ 0`. -/
noncomputable def mulByIntX (n : ℤ) : W.FunctionField :=
  phiFunctionField W n / psiFunctionField W n ^ 2

/-- The rational division-polynomial expression `ωₙ / ψₙ³`, the `y`-coordinate of `[n]` at the
generic point under the same proviso as `mulByIntX`: exactly when `ψₙ` does not vanish there. -/
noncomputable def mulByIntY (n : ℤ) : W.FunctionField :=
  omegaFunctionField W n / psiFunctionField W n ^ 3

/-- **The defining equation of `psiFunctionField`.** -/
theorem psiFunctionField_def (n : ℤ) : psiFunctionField W n =
    algebraMap W.CoordinateRing W.FunctionField (Affine.CoordinateRing.mk W (W.ψ n)) := (rfl)

/-- **The defining equation of `omegaFunctionField`.** -/
theorem omegaFunctionField_def (n : ℤ) : omegaFunctionField W n =
    algebraMap W.CoordinateRing W.FunctionField (Affine.CoordinateRing.mk W (W.ω n)) := (rfl)

/-- **The defining equation of `phiFunctionField`.** -/
theorem phiFunctionField_def (n : ℤ) : phiFunctionField W n =
    algebraMap W.CoordinateRing W.FunctionField (Affine.CoordinateRing.mk W (W.φ n)) := (rfl)

/-- **The defining equation of `mulByIntX`**: the `x`-coordinate of `[n]` is `φₙ / ψₙ²`. -/
theorem mulByIntX_def (n : ℤ) :
    mulByIntX W n = phiFunctionField W n / psiFunctionField W n ^ 2 := (rfl)

/-- **The defining equation of `mulByIntY`**: the `y`-coordinate of `[n]` is `ωₙ / ψₙ³`. -/
theorem mulByIntY_def (n : ℤ) :
    mulByIntY W n = omegaFunctionField W n / psiFunctionField W n ^ 3 := (rfl)

/-- The `Z`-coordinate of the Jacobian triple of `[n]` at the generic point is `ψₙ`.

Private, like the two below: all three are `rw`-lemmas for `equation_mulByInt`, which is the
public statement of what they add up to. They are not `@[simp]` either — `smulEval` is an
`abbrev`, so `simp` unfolds the left-hand side through `Function.comp_apply` and `map_ψ` before
these could fire, and `simpNF` rejects them. -/
private theorem smulEval_genericPoint_Z (n : ℤ) :
    smulEval W.functionFieldCurve W.genericX W.genericY n 2 = psiFunctionField W n := by
  dsimp only [smulEval, Affine.functionFieldCurve, Function.comp_def]
  rw [map_ψ, psiFunctionField]
  exact Affine.evalEval_genericPoint W (W.ψ n)

/-- The `X`-coordinate of the Jacobian triple of `[n]` at the generic point is `φₙ`. -/
private theorem smulEval_genericPoint_X (n : ℤ) :
    smulEval W.functionFieldCurve W.genericX W.genericY n 0 = phiFunctionField W n := by
  dsimp only [smulEval, Affine.functionFieldCurve, Function.comp_def]
  rw [map_φ, phiFunctionField]
  exact Affine.evalEval_genericPoint W (W.φ n)

/-- The `Y`-coordinate of the Jacobian triple of `[n]` at the generic point is `ωₙ`. -/
private theorem smulEval_genericPoint_Y (n : ℤ) :
    smulEval W.functionFieldCurve W.genericX W.genericY n 1 = omegaFunctionField W n := by
  dsimp only [smulEval, Affine.functionFieldCurve, Function.comp_def]
  rw [map_ω, omegaFunctionField]
  exact Affine.evalEval_genericPoint W (W.ω n)

/-- `ψₙ² = ΨSqₙ` in the function field: the division polynomial's square is the univariate
`ΨSq`, already known in the coordinate ring as `mk_ψ` followed by `mk_Ψ_sq`. -/
@[simp]
theorem psiFunctionField_sq (n : ℤ) : psiFunctionField W n ^ 2 =
      algebraMap W.CoordinateRing W.FunctionField (Affine.CoordinateRing.mk W (C (W.ΨSq n))) := by
  rw [psiFunctionField, ← map_pow, Affine.CoordinateRing.mk_ψ, Affine.CoordinateRing.mk_Ψ_sq]

/-- **The coordinates of `[n]` satisfy the equation of `W` over its function field.**

This is the fact that makes `[n]` a coordinate pullback at all, and it is *not* a polynomial
identity: it holds because `n • P` is again a point of the curve whenever `P` is. Concretely,
`zsmul_point_eq_smulEval` identifies `n • (generic point)` with the Jacobian class of
`(φₙ : ωₙ : ψₙ)`, that class is nonsingular because it is a point, and `ψₙ ≠ 0` lets it be read
in affine coordinates — where it becomes exactly this equation. -/
theorem equation_mulByInt [W.IsElliptic] {n : ℤ} (hn : psiFunctionField W n ≠ 0) :
    W.functionFieldCurve.Equation (mulByIntX W n) (mulByIntY W n) := by
  have hns := W.nonsingular_genericPoint
  have hsmul : Jacobian.Nonsingular W.functionFieldCurve.toJacobian
      (smulEval W.functionFieldCurve W.genericX W.genericY n) := by
    rw [← Jacobian.nonsingularLift_iff, ← zsmul_point_eq_smulEval _ hns n]
    exact (n • Jacobian.Point.fromAffine (Affine.Point.some _ _ hns)).nonsingular
  have hZ : smulEval W.functionFieldCurve W.genericX W.genericY n 2 ≠ 0 := by
    rw [smulEval_genericPoint_Z]; exact hn
  have hJ := (Jacobian.equation_of_Z_ne_zero hZ).mp hsmul.1
  rwa [smulEval_genericPoint_X, smulEval_genericPoint_Y, smulEval_genericPoint_Z,
    ← mulByIntX_def, ← mulByIntY_def] at hJ

/-- If `ψₙ` vanishes at the generic point then `ΨSqₙ` is the zero polynomial. Both discharge
lemmas below reduce to this and then cite a non-vanishing of `ΨSqₙ`; they differ only in which
one, so the transport through the coordinate ring lives here once. -/
private theorem ΨSq_eq_zero_of_psiFunctionField_eq_zero {n : ℤ}
    (h : psiFunctionField W n = 0) : W.ΨSq n = 0 := by
  have hzero : algebraMap W.CoordinateRing W.FunctionField
      (Affine.CoordinateRing.mk W (C (W.ΨSq n))) = 0 := by
    rw [← psiFunctionField_sq, h, zero_pow two_ne_zero]
  rw [AdjoinRoot.mk_C] at hzero
  exact FaithfulSMul.algebraMap_injective F[X] W.CoordinateRing
    ((FaithfulSMul.algebraMap_injective W.CoordinateRing W.FunctionField
      (hzero.trans (map_zero _).symm)).trans (map_zero _).symm)

/-- **`ψₙ` does not vanish at the generic point** when the image of `n` in `F` is nonzero.

The hypothesis is on `n` in `F`, not on `n` in `ℤ`: in characteristic `p` it excludes `n = p`.
It asks nothing about nonsingularity, which is what keeps it useful where
`psiFunctionField_ne_zero_of_Δ_ne_zero` does not apply; neither of the two subsumes the other.
The restriction is inherited from `Mathlib.ΨSq_ne_zero`, and every non-vanishing lemma in
Mathlib's division-polynomial development is conditional the same way — `preΨ_ne_zero`,
`ΨSq_ne_zero`, `Ψ₃_ne_zero`, `preΨ₄_ne_zero` — because each is proved from a leading coefficient
(`(W.ΨSq n).coeff (n.natAbs ^ 2 - 1) = n ^ 2`), exactly what vanishes when `p ∣ n`. -/
theorem psiFunctionField_ne_zero {n : ℤ} (hn : (n : F) ≠ 0) : psiFunctionField W n ≠ 0 :=
  fun h ↦ WeierstrassCurve.ΨSq_ne_zero W hn (ΨSq_eq_zero_of_psiFunctionField_eq_zero W h)

/-- **`ψₙ` does not vanish at the generic point of a nonsingular curve, for every `n ≠ 0`** — in
every characteristic, `p ∣ n` included.

This is the characteristic-free discharge of `mulByIntPullback`'s hypothesis, and it is what lets
this file construct `[p]` in characteristic `p`. It trades the condition on the characteristic for
nonsingularity: `ΨSq_ne_zero_of_Δ_ne_zero` gets `ΨSqₙ ≠ 0` from `W.Δ ≠ 0` by way of
`IsCoprime (W.Φ n) (W.ΨSq n)` (Silverman, Exercise III.3.7), which reads the non-vanishing off
coprimality rather than off a leading coefficient. `Δ ≠ 0` is stated as a hypothesis rather than
taken as `[W.IsElliptic]` so that the lemma matches its supplier; `mulByIntPullbackOfNeZero`
supplies it from the instance. -/
theorem psiFunctionField_ne_zero_of_Δ_ne_zero (hΔ : W.Δ ≠ 0) {n : ℤ} (hn : n ≠ 0) :
    psiFunctionField W n ≠ 0 :=
  fun h ↦ WeierstrassCurve.ΨSq_ne_zero_of_Δ_ne_zero W hΔ hn
    (ΨSq_eq_zero_of_psiFunctionField_eq_zero W h)

/-- **The coordinate pullback of `[n]`.** The coordinate ring is `F[X]` with a root of the
Weierstrass polynomial adjoined, so a map out of it is exactly a value for `X` together with a
value for `Y` satisfying that polynomial — here `φₙ/ψₙ²` and `ωₙ/ψₙ³`, which satisfy it by
`equation_mulByInt`.

`CoordinatePullback` asks for an `F`-algebra hom, which is what `AdjoinRoot.liftAlgHom` produces
from the `F`-algebra map `F[X] → W.FunctionField` sending `X` to `φₙ/ψₙ²`.

The hypothesis is the weakest one the construction uses: `ψₙ` must not vanish at the generic
point, which is what makes `φₙ/ψₙ²` and `ωₙ/ψₙ³` defined. Two lemmas discharge it —
`psiFunctionField_ne_zero` and `psiFunctionField_ne_zero_of_Δ_ne_zero` — and
`mulByIntPullbackOfNeZero` is the packaged form. -/
noncomputable def mulByIntPullback [W.IsElliptic] {n : ℤ} (hn : psiFunctionField W n ≠ 0) :
    CoordinatePullback W W :=
  AdjoinRoot.liftAlgHom W.polynomial (aeval (mulByIntX W n)) (mulByIntY W n) <| by
    -- `liftAlgHom` wants the equation in `eval₂` form against the coerced `aeval`, and
    -- `equation_mulByInt` is the same fact with the base change written out.
    have hcoe : ((aeval (mulByIntX W n) : F[X] →ₐ[F] W.FunctionField) :
        F[X] →+* W.FunctionField) =
        eval₂RingHom (algebraMap F W.FunctionField) (mulByIntX W n) :=
      RingHom.ext fun _ ↦ rfl
    have h := equation_mulByInt W hn
    dsimp only [Affine.Equation, Affine.functionFieldCurve] at h
    rw [Affine.map_polynomial, ← eval₂_eval₂RingHom_apply] at h
    rw [hcoe]
    exact h

/-- **The coordinate pullback of `[n]` for every `n ≠ 0`**, the non-vanishing hypothesis of
`mulByIntPullback` being discharged by `psiFunctionField_ne_zero_of_Δ_ne_zero`. This is the
specialisation to use unless you can supply `ψₙ ≠ 0` yourself.

The hypothesis is on `n` in `ℤ`, so this does give `[p]` in characteristic `p`. Nonsingularity
comes from the `[W.IsElliptic]` instance the definition already carried, which is why taking
`n ≠ 0` here is a strict weakening of the earlier `(n : F) ≠ 0` and costs nothing. -/
noncomputable abbrev mulByIntPullbackOfNeZero [W.IsElliptic] {n : ℤ} (hn : n ≠ 0) :
    CoordinatePullback W W :=
  mulByIntPullback W (psiFunctionField_ne_zero_of_Δ_ne_zero W W.isUnit_Δ.ne_zero hn)

/-- **The pullback of `[n]` on an arbitrary class**: the class of a bivariate polynomial `p` goes
to `p` evaluated at `(φₙ/ψₙ², ωₙ/ψₙ³)` over the function field. This is the general evaluation
rule; `mulByIntPullback_X` and `mulByIntPullback_Y` are its two special cases. -/
@[simp]
theorem mulByIntPullback_mk [W.IsElliptic] {n : ℤ} (hn : psiFunctionField W n ≠ 0) (p : F[X][Y]) :
    mulByIntPullback W hn (Affine.CoordinateRing.mk W p) =
      (p.map (mapRingHom (algebraMap F W.FunctionField))).evalEval (mulByIntX W n)
        (mulByIntY W n) := by
  rw [mulByIntPullback, AdjoinRoot.liftAlgHom_mk]
  exact eval₂_eval₂RingHom_apply (algebraMap F W.FunctionField) _ _ p

/-- The pullback of `[n]` sends the class of `X` to `φₙ/ψₙ²`.

Stated with `AdjoinRoot.of`, not `algebraMap F[X] W.CoordinateRing`, because
`AdjoinRoot.algebraMap_eq` is itself a `simp` lemma: a goal mentioning the class of `X` is
already normalised this way by the time this fires. -/
@[simp]
theorem mulByIntPullback_X [W.IsElliptic] {n : ℤ} (hn : psiFunctionField W n ≠ 0) :
    mulByIntPullback W hn (AdjoinRoot.of W.polynomial X) = mulByIntX W n := by
  rw [mulByIntPullback, AdjoinRoot.liftAlgHom_of, aeval_X]

/-- The pullback of `[n]` sends the class of `Y` to `ωₙ/ψₙ³`. -/
@[simp]
theorem mulByIntPullback_Y [W.IsElliptic] {n : ℤ} (hn : psiFunctionField W n ≠ 0) :
    mulByIntPullback W hn (AdjoinRoot.root W.polynomial) = mulByIntY W n := by
  rw [mulByIntPullback, AdjoinRoot.liftAlgHom_root]

end Isogeny

end TauCeti

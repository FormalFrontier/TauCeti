/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.IsAlgClosed
public import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Eval
public import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.ZSMul

/-!
# Coprimality of the division polynomials `Φₙ` and `ΨSqₙ`

Over a field, the `x`-coordinate of `n • (x, y)` is the rational function `Φₙ / ΨSqₙ`. This file
proves that numerator and denominator are **coprime** as soon as the curve is nonsingular, so that
quotient is already in lowest terms and its degree is visible from the two degrees separately.

The argument is the geometric one (Sutherland Lemma 6.8, Silverman Exercise III.3.7). A common
factor of `Φₙ` and `ΨSqₙ` survives to the algebraic closure, where it has a root `a`; that `a` is
the `x`-coordinate of an actual point `(a, b)` of the curve, and `Φₙ(a) = ΨSqₙ(a) = 0` makes both
the `X` and the `Z` Jacobian coordinate of `n • (a, b)` vanish. No point of a nonsingular curve
has `X = Z = 0`, so there was no common factor.

## Main results

* `WeierstrassCurve.isCoprime_Φ_ΨSq`: `IsCoprime (W.Φ n) (W.ΨSq n)` whenever `W.Δ ≠ 0`.
* `WeierstrassCurve.ΨSq_ne_zero_of_Δ_ne_zero`: `W.ΨSq n ≠ 0` for `n ≠ 0`, with **no** hypothesis
  on the characteristic.

## Implementation notes

**Coprimality needs no hypothesis on `n`.** The statement holds at `n = 0` as well, where it reads
`IsCoprime 1 0` — true because `Φ_zero` makes the first argument a unit — and the proof below never
splits on `n`. Since no hypothesis mentions `n` it is an explicit argument, while
`ΨSq_ne_zero_of_Δ_ne_zero` does need `n ≠ 0` and reads `n` off that hypothesis instead — the
split Mathlib's own `Φ_ne_zero` and `ΨSq_ne_zero` make in this same family.

**`W.Δ ≠ 0` is necessary, not an artefact of the proof.** On the cusp curve `Y² = X³` every
coefficient vanishes and `cusp_Ψ₂Sq` computes `Ψ₂Sq = 4X³`, while `Φ₂` is `X⁴`; the two share the
factor `X³`. So no version of this statement survives dropping nonsingularity, and the hypothesis
is stated as `W.Δ ≠ 0` rather than `[W.IsElliptic]` because that is all the proof consumes.

**`ΨSq_ne_zero_of_Δ_ne_zero` trades a characteristic hypothesis for nonsingularity.** Mathlib's
`ΨSq_ne_zero` concludes the same thing from `(n : F) ≠ 0`, which fails exactly when the
characteristic divides `n`. Coprimality removes that restriction: were `ΨSqₙ` zero, `Φₙ` would have
to be a unit, and `natDegree_Φ_pos` says it has positive degree. Neither statement subsumes the
other — Mathlib's holds on singular curves, this one in every characteristic — so both are useful.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md:99` — "**`[n]` is division polynomials**": for `n ≠ 0`,
multiplication-by-`n` is an isogeny of degree `n²`, pinned by the division-polynomial
multiplication formula. Reading that degree off `Φₙ / ΨSqₙ` requires knowing the fraction is in
lowest terms, which is what this file supplies; `ΨSq_ne_zero_of_Δ_ne_zero` is the accompanying
statement that the denominator is not the zero polynomial in any characteristic.

## Provenance

Ported, with the authors' proofs, from AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0), the
HasseWeil project at `dev/hasse-weil @ 513e83879e2f` — the revision
`TauCetiRoadmap/EllipticCurves/README.md:1071` pins for that project, as distinct from the
restructured `projects/HasseWeil` copy carried at the NagellLutz entry's `dev/modular-curves` pin.
Source file `projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean`, section
`Coprimality`, declaration `isCoprime_Φ_ΨSq`. The section's `exists_point_on_curve`, which the
proof below calls, is ported in `Affine/IsAlgClosed.lean` instead, since it is about
`Affine.Equation` and mentions no division polynomial. That file's header reads
`Authors: David Kurniadi Angdinata, Junyan Xu`; following this repository's convention for adapted
material the upstream authorship is credited here rather than in the copyright header.

Three of the source's calls are spelled differently here, because the corresponding lemmas already
exist under this repository's or Mathlib's names: the source's `evalEval_ψ_sq` and
`evalEval_φ_eq_Φ` are `Eval.lean`'s `evalEval_Ψ_sq_eq_eval_ΨSq` (composed with
`evalEval_ψ_eq_evalEval_Ψ`, since Mathlib states the square for `Ψ` rather than `ψ`) and
`evalEval_φ_eq_eval_Φ`; the source's `zsmul_eq_smulEval` is `ZSMul.lean`'s
`zsmul_point_eq_smulEval`. The source's `evalEval_eq_of_mk_eq` is not ported: `Eval.lean` already
has it. The degree computation for the quadratic is `Polynomial.degree_quadratic` here in place of
the source's explicit `natDegree` bound, and the unused `n ≠ 0` argument of the source's
`isCoprime_Φ_ΨSq` is dropped. `ΨSq_ne_zero_of_Δ_ne_zero` has no counterpart in the source.
-/

public section

open Polynomial

namespace WeierstrassCurve

open TauCeti.WeierstrassCurve

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

/-- **The division polynomials `Φₙ` and `ΨSqₙ` of a nonsingular curve are coprime**, so the
`x`-coordinate `Φₙ / ΨSqₙ` of `n • (x, y)` is in lowest terms (Sutherland Lemma 6.8, Silverman
Exercise III.3.7). Nonsingularity is necessary and no hypothesis on `n` is needed; see the module
docstring for both. -/
theorem isCoprime_Φ_ΨSq (n : ℤ) (hΔ : W.Δ ≠ 0) : IsCoprime (W.Φ n) (W.ΨSq n) := by
  let f := algebraMap F (AlgebraicClosure F)
  rw [← Polynomial.isCoprime_map f, ← map_Φ, ← map_ΨSq]
  set W' := W.map f with hW'
  rw [@Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed _ _
    (AlgebraicClosure F) _ _ (Algebra.id _)]
  intro a
  by_contra h
  push Not at h
  obtain ⟨hΦ, hΨ⟩ := h
  simp only [Polynomial.coe_aeval_eq_eval] at hΦ hΨ
  -- a common root of `Φₙ` and `ΨSqₙ` is the `x`-coordinate of a point of the curve
  obtain ⟨b, hb⟩ := W'.toAffine.exists_point_on_curve a
  have hΔ' : W'.Δ ≠ 0 := by rw [hW', map_Δ]; exact (map_ne_zero_iff f f.injective).mpr hΔ
  have hns : W'.toAffine.Nonsingular a b :=
    (W'.toAffine.equation_iff_nonsingular_of_Δ_ne_zero hΔ').mp hb
  -- at that point both the `Z` and the `X` Jacobian coordinate of `n • (a, b)` vanish
  have hψ : (W'.ψ n).evalEval a b = 0 := by
    refine (pow_eq_zero_iff two_ne_zero).mp ?_
    rw [evalEval_ψ_eq_evalEval_Ψ W' hb n, evalEval_Ψ_sq_eq_eval_ΨSq W' hb n]
    exact hΨ
  have hφ : (W'.φ n).evalEval a b = 0 := by rwa [evalEval_φ_eq_eval_Φ W' hb n]
  have hZ : smulEval W' a b n 2 = 0 := by simp [smulEval, hψ]
  have hX : smulEval W' a b n 0 = 0 := by simp [smulEval, hφ]
  -- but `n • (a, b)` is a nonsingular Jacobian point, and those never have `X = Z = 0`
  have hns_smul : Jacobian.Nonsingular W' (smulEval W' a b n) := by
    rw [← Jacobian.nonsingularLift_iff, ← zsmul_point_eq_smulEval W' hns n]
    exact (n • Jacobian.Point.fromAffine (Affine.Point.some _ _ hns)).nonsingular
  exact Jacobian.X_ne_zero_of_Z_eq_zero hns_smul hZ hX

/-- **`ΨSqₙ` is nonzero on a nonsingular curve, in every characteristic.** Mathlib's
`ΨSq_ne_zero` assumes `(n : F) ≠ 0` instead; see the module docstring on why neither statement
subsumes the other. -/
theorem ΨSq_ne_zero_of_Δ_ne_zero {n : ℤ} (hΔ : W.Δ ≠ 0) (hn : n ≠ 0) : W.ΨSq n ≠ 0 := fun h ↦
  (W.natDegree_Φ_pos hn).ne'
    (natDegree_eq_zero_of_isUnit (isCoprime_zero_right.mp (h ▸ W.isCoprime_Φ_ΨSq n hΔ)))

end WeierstrassCurve

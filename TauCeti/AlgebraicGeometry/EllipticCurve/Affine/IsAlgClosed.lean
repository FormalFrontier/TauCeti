/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Every `x`-coordinate of a Weierstrass curve over an algebraically closed field is attained

Fixing `x = a` in the Weierstrass equation leaves a monic quadratic in `y`, so over an
algebraically closed field it has a root and `a` is the `x`-coordinate of a solution. The statement
is about `Affine.Equation` alone: no nonsingularity, no ellipticity, and no division polynomial is
involved, which is why it lives here rather than with any consumer.

## Main results

* `WeierstrassCurve.Affine.exists_point_on_curve`: over an algebraically closed field
  every element is the `x`-coordinate of a solution of `W.Equation`.

Stated for an arbitrary affine Weierstrass curve over an algebraically closed field. It yields a
solution of the *equation*, not an element of `W.Point`; a caller wanting a point pairs it with
`equation_iff_nonsingular_of_Δ_ne_zero` or `equation_iff_nonsingular`, which is what makes the
hypothesis-free form the useful one.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md:99` — "**`[n]` is division polynomials**". The consumer is
`DivisionPolynomial/Coprimality.lean`, whose proof of `isCoprime_Φ_ΨSq` passes to the algebraic
closure and needs a common root of `Φₙ` and `ΨSqₙ` to be the `x`-coordinate of an actual point.
Nothing here mentions a division polynomial.

## Provenance

Ported, with the author's proof, from AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0), the
HasseWeil project at `dev/hasse-weil @ 513e83879e2f` — the revision
`TauCetiRoadmap/EllipticCurves/README.md:1071` pins for that project. Source file
`projects/HasseWeil/HasseWeil/Auxiliary/DivisionPolynomial.lean`, section `Coprimality`,
declaration `exists_point_on_curve`, whose header credits David Kurniadi Angdinata and Junyan Xu.
Upstream it sits beside its coprimality consumer and is stated for a global
`WeierstrassCurve`; here it is separated out and stated for the affine model, which is the level
its content lives at. The degree of the quadratic is `Polynomial.degree_quadratic` here in place of
the source's explicit `natDegree` bound.
-/

public section

open Polynomial

namespace WeierstrassCurve

namespace Affine

variable {F : Type*} [Field F] [IsAlgClosed F] (W : Affine F)

/-- **Over an algebraically closed field every `x`-coordinate is realised by a point.** Solving the
Weierstrass equation for `y` at a fixed `x` is finding a root of a quadratic, which an
algebraically closed field always has. -/
theorem exists_point_on_curve (a : F) : ∃ b : F, W.Equation a b := by
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_root
    (C 1 * X ^ 2 + C (W.a₁ * a + W.a₃) * X + C (-(a ^ 3 + W.a₂ * a ^ 2 + W.a₄ * a + W.a₆)))
    (by rw [degree_quadratic one_ne_zero]; simp)
  rw [IsRoot.def] at hb
  simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X, one_mul] at hb
  exact ⟨b, (W.equation_iff a b).mpr (by linear_combination hb)⟩

end Affine

end WeierstrassCurve

end

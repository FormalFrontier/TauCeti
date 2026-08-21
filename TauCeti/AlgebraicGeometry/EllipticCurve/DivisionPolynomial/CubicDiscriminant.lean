/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import TauCeti.Algebra.CubicDiscriminant

/-!
# The sharp discriminant divisibility for a model with `a₁ = a₃ = 0`

For a Weierstrass model with `a₁ = a₃ = 0` — so the equation is the cubic
`y² = x³ + a₂x² + a₄x + a₆` — a point whose `y²` divides `Ψ₃(x)` has `y²` dividing the
**discriminant of that cubic**, Mathlib's `Cubic.discr ⟨1, a₂, a₄, a₆⟩`.

This is sharper than dividing `Δ`. Mathlib's `twoTorsionPolynomial_discr` records
`Cubic.discr ⟨4, b₂, 2b₄, b₆⟩ = 16Δ`, and for these models `Δ = 16 · Cubic.discr ⟨1, a₂, a₄, a₆⟩`,
so the cubic discriminant is the invariant with the factors of `16` divided out. It is the `Δ` of
the classical statement of Nagell–Lutz for a short model, where `a₂ = 0` too and the conclusion
reads `y² ∣ 4a₄³ + 27a₆²` up to sign.

The proof is two ring identities, and neither mentions a curve. Writing
`f(x) = x³ + a₂x² + a₄x + a₆`, the first is

`f'(x)² + Q(x) = (12x + 4a₂) · f(x)`,   `Q(x) = 3x⁴ + 4a₂x³ + 6a₄x² + 12a₆x + (4a₂a₆ − a₄²)`,

so anything dividing `f(x)` and `Q(x)` divides `f'(x)²`; the second expresses
`Cubic.discr ⟨1, a₂, a₄, a₆⟩` as a combination of `f(x)` and `f'(x)²`. Both are stated for an
arbitrary divisor `d`. Both are pure cubic algebra and live in `TauCeti.Algebra.CubicDiscriminant`
(`TauCeti.Cubic.dvd_derivative_sq` and `TauCeti.Cubic.dvd_discr`), which this file imports. `Ψ₃`
enters only here: for `a₁ = a₃ = 0` it evaluates to exactly that `Q(x)`, and the curve equation
makes `y²` a divisor of `f(x)`.

## Main results

* `TauCeti.WeierstrassCurve.eval_Ψ₃_of_a₁_eq_zero_of_a₃_eq_zero`: for `a₁ = a₃ = 0`, `Ψ₃` is `Q`.
* `TauCeti.WeierstrassCurve.sq_dvd_cubic_discr`: `y² ∣ Cubic.discr ⟨1, a₂, a₄, a₆⟩`, the three
  composed.

Both are over an arbitrary commutative ring, for an arbitrary point of the curve — no domain,
torsion, integrality or ellipticity hypothesis.

⚠ The input `y² ∣ Ψ₃(x)` is a hypothesis, and it is **not** something torsion alone provides. Over
an arbitrary commutative ring finite order says nothing about divisibility; the divisibility is
extracted in the integral Nagell–Lutz setting, from the coordinate formula for `2 • P` together
with the integrality of the coordinates. Both of those are point-level results that this file does
not contain. Read the hypothesis as the shape a later torsion argument is expected to supply, not
as a consequence of torsion.

This is an ingredient for the Nagell–Lutz milestone of `TauCetiRoadmap/EllipticCurves/README.md`,
Layer 6, item "The torsion subgroup and Nagell–Lutz", whose short-model target `lutz_nagell` asks
for `y = 0 ∨ y² ∣ Δ`; it is the sharp algebraic form of that second conjunct's divisibility step.

## Provenance

Ported from the AINTLIB `NagellLutz` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0), pinned by
that roadmap at `dev/modular-curves @ 9fec8eba7652`:
`LutzNagell/LutzNagellTheorem/PIDMain.lean`, the algebraic core of
`lutz_nagell_cubicDisc_discriminant` (:438). The source states the conclusion as the raw polynomial
`4a₄³ + 27a₆² + 4a₂³a₆ − a₂²a₄² − 18a₂a₄a₆` and reaches it inside a torsion argument; here it is
the negative of Mathlib's `Cubic.discr`, and the torsion-dependent part — which needs the
point-level `[n]`-multiplication material — is left out, with `y² ∣ Ψ₃(x)` as a hypothesis instead.
-/

public section

open Polynomial

namespace TauCeti

namespace WeierstrassCurve

open Polynomial

variable {R : Type*} [CommRing R] (W : _root_.WeierstrassCurve R) {x y : R}

/-- For a model with `a₁ = a₃ = 0`, the univariate `Ψ₃` is the quartic
`3x⁴ + 4a₂x³ + 6a₄x² + 12a₆x + (4a₂a₆ − a₄²)`. -/
@[simp]
theorem eval_Ψ₃_of_a₁_eq_zero_of_a₃_eq_zero (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) :
    (W.Ψ₃).eval x = 3 * x ^ 4 + 4 * W.a₂ * x ^ 3 + 6 * W.a₄ * x ^ 2 + 12 * W.a₆ * x +
      (4 * W.a₂ * W.a₆ - W.a₄ ^ 2) := by
  simp only [_root_.WeierstrassCurve.Ψ₃, _root_.WeierstrassCurve.b₂, _root_.WeierstrassCurve.b₄,
    _root_.WeierstrassCurve.b₆, _root_.WeierstrassCurve.b₈, ha₁, ha₃, eval_add, eval_mul,
    eval_pow, eval_C, eval_X, eval_ofNat]
  ring

/-- **The sharp discriminant divisibility.**

For a model with `a₁ = a₃ = 0`, a point whose `y²` divides `Ψ₃(x)` has `y²` dividing the
discriminant of the defining cubic `x³ + a₂x² + a₄x + a₆`. For a short model (`a₂ = 0` as well)
this is the classical `y² ∣ 4a₄³ + 27a₆²` up to sign. -/
theorem sq_dvd_cubic_discr (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    (hcurve : y ^ 2 = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)
    (hΨ₃ : y ^ 2 ∣ (W.Ψ₃).eval x) :
    y ^ 2 ∣ (_root_.Cubic.mk 1 W.a₂ W.a₄ W.a₆).discr :=
  have hf : y ^ 2 ∣ x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := hcurve ▸ dvd_rfl
  Cubic.dvd_discr hf
    (Cubic.dvd_derivative_sq hf (eval_Ψ₃_of_a₁_eq_zero_of_a₃_eq_zero W ha₁ ha₃ ▸ hΨ₃))

end WeierstrassCurve

end TauCeti

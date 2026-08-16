/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Weierstrass

/-!
# Division polynomials of the cusp curve

The cusp curve `Y² = X³` has every coefficient zero, so its low division polynomials collapse to
their leading terms. Two different mechanisms produce that collapse: `Ψ₂Sq`, `Ψ₃` and `preΨ₄` are
polynomials in the `bᵢ`, all of which vanish, leaving the one monomial that carries no `bᵢ`;
whereas `ψ₂ = 2Y + a₁X + a₃` contains no `bᵢ` at all and collapses directly because `a₁ = a₃ = 0`.

## Main results

* `WeierstrassCurve.cusp_ψ₂`, `.cusp_Ψ₂Sq`, `.cusp_Ψ₃`, `.cusp_preΨ₄`: on the cusp curve
  `ψ₂ = 2Y`, `Ψ₂Sq = 4X³`, `Ψ₃ = 3X⁴` and `preΨ₄ = 2X⁶`.

Three of these parameterise the univariate family: `preΨ'` is generated from `Ψ₂Sq ^ 2`, `Ψ₃`
and `preΨ₄`, so collapsing those collapses `preΨ`, `ΨSq` and `Φ` on the cusp curve too — but only
once the consumer unfolds whichever of those definitions it is working with, since they are
definitions rather than simp lemmas and bare `simp` does not reduce them. `ψ₂` is not one of the
three; it serves the bivariate division polynomials.

## Implementation notes

`cusp`'s definition body is unexposed, so these proofs do not unfold it — they project through the
`@[simp]` lemmas `cusp_a₁` … `cusp_a₆` that `Weierstrass.lean` provides for exactly this purpose.
Everything else here *is* unfolded, and each name is exposed by a different Mathlib module, which
is worth recording separately since a future bump could move any one of them:

* `ψ₂`, `Ψ₂Sq`, `Ψ₃`, `preΨ₄` — Mathlib's `DivisionPolynomial/Basic.lean`, whose
  `@[expose] public section` is at line 94;
* `b₂`, `b₄`, `b₆`, `b₈` — Mathlib's `EllipticCurve/Weierstrass.lean`, definitions at 101–114
  under the `@[expose] public section` at line 66;
* `Affine.polynomialY`, which `cusp_ψ₂` alone unfolds — `Affine/Basic.lean:192`, exposed at line 49.

`C_ofNat` appears in two of the proofs because the `Ψ₂Sq` and `ψ₂` normal forms end with a
constant polynomial `C 4` / `C 2` that must be matched against the numeral in the statement.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md:99` — "**`[n]` is division polynomials**", which names
`ZSMul.lean` and mathlib #13782 as "the mathlib-track anchor Layer 1 consumes". Three of these
four are that file's cusp specialisation, used to evaluate the universal division polynomials at
`(1, 1)`; `cusp_Ψ₂Sq` completes the family. The onward consumer is Layer 6's "**The torsion
subgroup and Nagell–Lutz**" (`README.md:821`), whose stated route is division polynomials.

## Provenance

Adapted from `LutzNagell/ZSMul.lean` in AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at
`dev/modular-curves @ 9fec8eba7652` — the revision `TauCetiRoadmap/EllipticCurves/README.md` pins
for the NagellLutz project. Declarations `cusp_ψ₂`, `cusp_Ψ₃`, `cusp_preΨ₄`. That file's header
reads `Authors: David Kurniadi Angdinata, Junyan Xu`; following this repository's convention for
adapted material the upstream authorship is credited here rather than in the copyright header.

Three changes from the source. The statements are generalised from `cusp ℤ` to `cusp R` over any
`CommRing R` — nothing in them is specific to `ℤ`. The source unfolds `cusp` directly
(`simp [cusp, ψ₂, …]`), which is not available across a module boundary, so the projection lemmas
are used instead. And `cusp_Ψ₂Sq` has no counterpart upstream: it is added here to complete the
family, since without it `simp` leaves `(cusp R).Ψ₂Sq` irreducible and any consumer of `preΨ`,
`ΨSq` or `Φ` on the cusp curve would have to re-derive it.
-/

public section

noncomputable section

open Polynomial

open scoped Polynomial.Bivariate

namespace WeierstrassCurve

variable (R : Type*) [CommRing R]

/-- On the cusp curve `Y² = X³`, the `2`-division polynomial is `2Y`. -/
@[simp]
lemma cusp_ψ₂ : (cusp R).ψ₂ = 2 * Y := by
  simp [ψ₂, Affine.polynomialY, C_ofNat]

/-- On the cusp curve `Y² = X³`, the univariate polynomial congruent to `ψ₂²` is `4X³`. -/
@[simp]
lemma cusp_Ψ₂Sq : (cusp R).Ψ₂Sq = 4 * X ^ 3 := by
  simp [Ψ₂Sq, b₂, b₄, b₆, C_ofNat]

/-- On the cusp curve `Y² = X³`, the `3`-division polynomial is `3X⁴`. -/
@[simp]
lemma cusp_Ψ₃ : (cusp R).Ψ₃ = 3 * X ^ 4 := by
  simp [Ψ₃, b₂, b₄, b₆, b₈]

/-- On the cusp curve `Y² = X³`, the auxiliary polynomial `preΨ₄` is `2X⁶`. -/
@[simp]
lemma cusp_preΨ₄ : (cusp R).preΨ₄ = 2 * X ^ 6 := by
  simp [preΨ₄, b₂, b₄, b₆, b₈]

end WeierstrassCurve

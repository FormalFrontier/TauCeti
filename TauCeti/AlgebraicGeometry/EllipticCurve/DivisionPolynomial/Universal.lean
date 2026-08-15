/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Universal
public import TauCeti.NumberTheory.EllipticDivisibilitySequence.NormEDS

/-!
# Division polynomials of the universal curve

Every Weierstrass curve is a specialization of the universal one, and division polynomials commute
with base change. Composing the two identifies the division polynomials of a curve `W` over `R`,
evaluated at a point `(x, y)` of the affine plane, with those of `Universal.curve` pushed forward
along `Universal.polyEval`.

Each proof is the same two steps: unfold `polyEval` into a `map` followed by `evalEval`
(`polyEval_apply`), then rewrite the base change of the universal curve back to `W`
(`map_specialize`). The division polynomial in between is carried across by the relevant Mathlib
`map_*` lemma.

## Main results

* `WeierstrassCurve.Universal.evalEval_ψ₂`, `.evalEval_Ψ₃`, `.evalEval_preΨ₄`, `.evalEval_ψ`,
  `.evalEval_φ`: the polynomials `ψ₂`, `Ψ₃`, `ψₙ` and `φₙ` of `W` at `(x, y)`, together with the
  auxiliary `preΨ₄`, are the universal ones evaluated through `Universal.polyEval`.
* `WeierstrassCurve.Universal.isEllipticSequence_polyToField_ψ`: the universal `ψ` family, taken
  into `Universal.Field`, is an elliptic sequence.

## Implementation notes

`Ψ₃` and `preΨ₄` are univariate, so their statements evaluate `C W.Ψ₃` rather than `W.Ψ₃`; the two
extra rewrites in those proofs (`map_C`, `coe_mapRingHom`) only move that `C` past the base change.

The companion transport for `ω` is **not** here. It cannot be: `WeierstrassCurve.ω` does not exist
in this repository or in the pinned Mathlib, and neither does the `map_ω` such a proof would rewrite
with. `DivisionPolynomial/Invariant.lean` lists both among what it deliberately leaves out, and
records the chain still missing for them — `redInvarDenom` together with the upper part of
`redInvar_normEDS ← invar₂_normEDS ← invar_normEDS ← net_normEDS`, the source's names for it. The
lower two links are `isEllipticNet_normEDS` and `invarNum_mul_invarDenom`, both present, so what
remains is `invar₂_normEDS` and `redInvar_normEDS`. `evalEval_ω` belongs with that work rather
than here.

## Provenance

Adapted from `LutzNagell/ZSMul.lean` in AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0),
at `dev/modular-curves @ 9fec8eba7652` — the revision `TauCetiRoadmap/EllipticCurves/README.md`
pins for the NagellLutz project. Declarations `Universal.evalEval_ψ₂`, `evalEval_Ψ₃`,
`evalEval_preΨ₄`, `evalEval_ψ` and `evalEval_φ`; the sixth, `evalEval_ω`, is excluded for the
reason above. `isEllipticSequence_polyToField_ψ` adapts that same file's `isEllSequence_ψᵤ`.
That file's header reads `Authors: David Kurniadi Angdinata, Junyan Xu`; following this
repository's convention for adapted material the upstream authorship is credited here rather than
in the copyright header.

The `evalEval_*` statements are the source's unchanged. Docstrings are added here, and the
source's shared `variable {m n : ℤ}` is narrowed to `n`: of those five only `evalEval_ψ` and
`evalEval_φ` carry an index, and both use `n` alone. `isEllSequence_ψᵤ` is stated upstream through
an `abbrev ψᵤ` and its own `ψᵤ_eq_normEDS`; here the abbreviation is dropped and that equation is
inlined as a `have`, so the statement is spelled on `fun n ↦ polyToField (curve.ψ n)` directly.
-/

public section

noncomputable section

open Polynomial

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x y : R}

namespace Universal

/-- The `2`-division polynomial of `W` at `(x, y)` is the universal one under `polyEval`. -/
lemma evalEval_ψ₂ : W.ψ₂.evalEval x y = polyEval W x y curve.ψ₂ := by
  simp_rw [polyEval_apply, ← map_ψ₂, map_specialize]

/-- The `3`-division polynomial of `W` at `(x, y)` is the universal one under `polyEval`. -/
lemma evalEval_Ψ₃ : (C W.Ψ₃).evalEval x y = polyEval W x y (C curve.Ψ₃) := by
  simp_rw [polyEval_apply, map_C, coe_mapRingHom, ← map_Ψ₃, map_specialize]

/-- The polynomial `preΨ₄` of `W` at `(x, y)` is the universal one under `polyEval`. -/
lemma evalEval_preΨ₄ : (C W.preΨ₄).evalEval x y = polyEval W x y (C curve.preΨ₄) := by
  simp_rw [polyEval_apply, map_C, coe_mapRingHom, ← map_preΨ₄, map_specialize]

variable {n : ℤ}

/-- The `n`-division polynomial `ψₙ` of `W` at `(x, y)` is the universal one under `polyEval`. -/
lemma evalEval_ψ : (W.ψ n).evalEval x y = polyEval W x y (curve.ψ n) := by
  simp_rw [polyEval_apply, ← map_ψ, map_specialize]

/-- The numerator `φₙ` of `W` at `(x, y)` is the universal one under `polyEval`. -/
lemma evalEval_φ : (W.φ n).evalEval x y = polyEval W x y (curve.φ n) := by
  simp_rw [polyEval_apply, ← map_φ, map_specialize]

/-- **The universal `ψ` family is an elliptic sequence.** Pushing `ψₙ` of the universal curve into
`Universal.Field` gives a normalised EDS, hence an elliptic sequence — over the universal field,
with no hypothesis on any coefficient.

The proof recognises the family as a `normEDS` outright, which is what puts the whole `normEDS` API
— including `NormEDS.lean`'s `universalNormEDS_ne_zero` — within reach of the universal division
polynomials. -/
lemma isEllipticSequence_polyToField_ψ :
    IsEllipticSequence fun n : ℤ ↦ polyToField (curve.ψ n) := by
  have h : (fun n : ℤ ↦ polyToField (curve.ψ n))
      = normEDS (polyToField curve.ψ₂) (polyToField (Polynomial.C curve.Ψ₃))
          (polyToField (Polynomial.C curve.preΨ₄)) := by
    funext n; rw [← _root_.map_normEDS]; rfl
  rw [h]
  exact isEllipticSequence_normEDS _ _ _

end Universal

end WeierstrassCurve

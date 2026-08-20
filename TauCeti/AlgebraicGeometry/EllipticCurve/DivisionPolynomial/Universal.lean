/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Cusp
public import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Omega

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
  `.evalEval_φ`, `.evalEval_ω`, `.evalEval_ψc`: the polynomials `ψ₂`, `Ψ₃`, `ψₙ`, `φₙ`, `ωₙ` and
  the complement `ψc n` of `W` at `(x, y)`, together with the auxiliary `preΨ₄`, are the
  universal ones evaluated through `Universal.polyEval`.
* `WeierstrassCurve.Universal.isEllipticSequence_polyToField_ψ`: the universal `ψ` family, taken
  into `Universal.Field`, is an elliptic sequence.
* `WeierstrassCurve.Universal.polyEval_cusp_ψ`, `.polyEval_cusp_φ`, `.polyEval_cusp_ψc`,
  `.polyEval_cusp_ω`: specialised to the cusp curve at `(1, 1)`, `ψₙ` evaluates to `n` itself,
  the numerator `φₙ` to `1`, the complement `ψc n` to `2`, and `ωₙ` to `1`.

## Implementation notes

`Ψ₃` and `preΨ₄` are univariate, so their statements evaluate `C W.Ψ₃` rather than `W.Ψ₃`; the two
extra rewrites in those proofs (`map_C`, `coe_mapRingHom`) only move that `C` past the base change.

`polyEval_cusp_ψ` is where the three transport lemmas above earn their keep. `Cusp.lean` collapses
`ψ₂`, `Ψ₃` and `preΨ₄` on `cusp R` to `2Y`, `3X⁴` and `2X⁶`; rewriting the transports backwards
turns `polyEval (cusp ℤ) 1 1 (curve.ψ n)` into those three evaluated at `(1, 1)`, which are `2`,
`3` and `2` — so the sequence is `normEDS 2 3 2`, and the identity of #3364 finishes it. That is
the only reason this file imports `Cusp.lean`.

**`polyEval_cusp_φ` does not port as written, and the reason is the module system rather than a
missing prerequisite.** The source closes it with `simp_rw [φ, map_sub, …, polyEval]`, unfolding
`polyEval`'s definition, which is rejected across a module boundary — *"Invalid simp theorem
`polyEval`: Expected a definition with an exposed body"*. Supplying the equation lemma instead does
not help either: `polyEval`'s image lives in `Poly`, whose `Sub` and `Mul` instances are themselves
unexposed, so a bare `map_sub` cannot solve `?f` in the pattern `?f (?a - ?b)` and fails to fire at
all. **Naming the ring hom is what fixes it** — `map_sub (polyEval (cusp ℤ) 1 1)` makes the match
first-order, and the same for `map_mul` and `map_pow`. That leaves the arithmetic
`polyEval (cusp ℤ) 1 1 (C X) * n ^ 2 - (n + 1) * (n - 1) = 1`, which `ring` closes once `C X`
evaluates to `1`.

The remaining two companions, `polyEval_cusp_ψc` and `polyEval_cusp_ω`, together with the sixth
transport `evalEval_ω`, needed `ψc`, `two_mul_ω` and `map_ω` — the `ω` API this passage once
recorded as not yet here. `DivisionPolynomial/Omega.lean` now supplies all three, on top of
`reducedInvarNum_eq_reducedInvarDenom_mul`, so they are below: `evalEval_ω` closes the transport
family, `polyEval_cusp_ψc` reads the complement off `complEDS₂_two_three_two`, and
`polyEval_cusp_ω` divides the cusp evaluation of `two_mul_ω` by two.

## Provenance

Adapted from `LutzNagell/ZSMul.lean` in AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0),
at `dev/modular-curves @ 9fec8eba7652` — the revision `TauCetiRoadmap/EllipticCurves/README.md`
pins for the NagellLutz project. Declarations `Universal.evalEval_ψ₂`, `evalEval_Ψ₃`,
`evalEval_preΨ₄`, `evalEval_ψ`, `evalEval_φ` and (added with the `ω` port, read at
`main @ 1c1c74664e40071c2c2165bc55ca2616a67ccd6b`) `evalEval_ω`.
`isEllipticSequence_polyToField_ψ` adapts that same file's `isEllSequence_ψᵤ`.
That file's header reads `Authors: David Kurniadi Angdinata, Junyan Xu`; following this
repository's convention for adapted material the upstream authorship is credited here rather than
in the copyright header.

`polyEval_cusp_ψ` and `polyEval_cusp_φ` adapt that same file's declarations of those names, at the
roadmap's NagellLutz pin `dev/modular-curves @ 9fec8eba7652`. Three changes. `ψ` and `φ` need
qualifying, because this file opens `Universal` rather than `WeierstrassCurve` alone. The source's
`normEDS_two_three_two` hint is dropped rather than renamed — `normEDS_two_three_two_eq_id` is
redundant here, since #3364's general `normEDS_two_three_two_eq_intCast` is `@[simp]` and reaches
the same normal form first. And `polyEval_cusp_φ`'s proof is restructured for the reason given
above: the source's unfold of `polyEval` is unavailable, so each `map_*` names its ring hom.
The source's `polyEval_cusp_ψc` and `polyEval_cusp_ω` are adapted below (read at
`main @ 1c1c74664e40071c2c2165bc55ca2616a67ccd6b`), with the same two mechanical changes as
their siblings — qualified names, ring-hom-named `map_*` rewrites in place of unfolding
`polyEval` — plus `ψc_def` in place of unfolding `ψc`, whose body is likewise unexposed.

The `evalEval_*` statements are the source's unchanged. Docstrings are added here, and the
source's shared `variable {m n : ℤ}` is narrowed to `n`: of the seven transports only
`evalEval_ψ`, `evalEval_φ`, `evalEval_ω` and `evalEval_ψc` carry an index, and all four use `n`
alone. `isEllSequence_ψᵤ` is stated upstream through
an `abbrev ψᵤ` and its own `ψᵤ_eq_normEDS`; here the abbreviation is dropped, the identification
of `ψ` with `normEDS` is the named `ψ_eq_normEDS` (`DivisionPolynomial/NormEDS.lean`), and a
`have` transports it through `polyToField`, so the statement is spelled on
`fun n ↦ polyToField (curve.ψ n)` directly.
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
    funext n; rw [ψ_eq_normEDS, _root_.map_normEDS]
  rw [h]
  exact isEllipticSequence_normEDS _ _ _

/-- **On the cusp curve at `(1, 1)`, the `n`-division polynomial evaluates to `n`.** -/
lemma polyEval_cusp_ψ : polyEval (cusp ℤ) 1 1 (curve.ψ n) = n := by
  rw [WeierstrassCurve.ψ, map_normEDS, ← evalEval_ψ₂, ← evalEval_Ψ₃, ← evalEval_preΨ₄, cusp_ψ₂,
    cusp_Ψ₃, cusp_preΨ₄]
  simp [evalEval]

/-- **On the cusp curve at `(1, 1)`, the numerator `φₙ` evaluates to `1`.** -/
lemma polyEval_cusp_φ : polyEval (cusp ℤ) 1 1 (curve.φ n) = 1 := by
  -- Each `map_*` names its ring hom; the implementation notes say why unification cannot.
  rw [WeierstrassCurve.φ, map_sub (polyEval (cusp ℤ) 1 1), map_mul (polyEval (cusp ℤ) 1 1),
    map_mul (polyEval (cusp ℤ) 1 1), map_pow (polyEval (cusp ℤ) 1 1), polyEval_cusp_ψ,
    polyEval_cusp_ψ, polyEval_cusp_ψ]
  simp [polyEval_apply, evalEval]
  ring

/-- The `ω`-division polynomial of `W` at `(x, y)` is the universal one under `polyEval`. -/
lemma evalEval_ω : (W.ω n).evalEval x y = polyEval W x y (curve.ω n) := by
  simp_rw [polyEval_apply, ← map_ω, map_specialize]

/-- The complement `ψc n` of `W` at `(x, y)` is the universal one under `polyEval`. -/
lemma evalEval_ψc : (W.ψc n).evalEval x y = polyEval W x y (curve.ψc n) := by
  simp_rw [polyEval_apply, ← map_ψc, map_specialize]

/-- **On the cusp curve at `(1, 1)`, the complement `ψc n` evaluates to `2`.** -/
lemma polyEval_cusp_ψc : polyEval (cusp ℤ) 1 1 (curve.ψc n) = 2 := by
  rw [ψc_def, map_complEDS₂, ← evalEval_ψ₂, ← evalEval_Ψ₃, ← evalEval_preΨ₄, cusp_ψ₂,
    cusp_Ψ₃, cusp_preΨ₄]
  simp [evalEval]

/-- **On the cusp curve at `(1, 1)`, `ω n` evaluates to `1`.** -/
lemma polyEval_cusp_ω : polyEval (cusp ℤ) 1 1 (curve.ω n) = 1 := by
  -- Evaluate `two_mul_ω` at the cusp: `ψc` gives `2`, `φ` gives `1`, the cusp's `a₁` and `a₃`
  -- vanish, so `h` collapses to `2 * (the goal's left side) = 2` and the `2` cancels.
  have h := congr(polyEval (cusp ℤ) 1 1 $(two_mul_ω curve n))
  simp only [map_mul (polyEval (cusp ℤ) 1 1), map_sub (polyEval (cusp ℤ) 1 1),
    map_pow (polyEval (cusp ℤ) 1 1), polyEval_cusp_ψc, polyEval_cusp_ψ, polyEval_cusp_φ] at h
  -- The residual `a₁`/`a₃` terms sit under `CC`, whose body is unexposed and has no cusp value
  -- lemma, so no named rewrite can kill them; evaluating the wrappers is the one route left.
  simpa [polyEval_apply, evalEval] using h

end Universal

end WeierstrassCurve

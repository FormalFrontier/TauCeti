/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Universal

/-!
# Coordinates of scalar multiplication through the division polynomials

The Nagell–Lutz route expresses `n • (X, Y)` on the universal curve through the division
polynomials: the affine `X`-coordinate is `φₙ/ψₙ²` and the `Y`-coordinate is `ωₙ/ψₙ³`, as
elements of `Universal.Field`. This file defines those two rational functions, `smulX` and
`smulY`, develops the `smulX` calculus — values at `0`, `1` and `2`, the offset `ψₙ₊₁ψₙ₋₁/ψₙ²`
from the `X`-coordinate, evenness in `n`, nonvanishing, the difference `smulX m - smulX n` as a
single quotient, and the separation statement `smulX m = smulX n ↔ m = n ∨ m = -n` — and then
**proves the identification itself**: `zsmul_point_eq_smulX_smulY` says that
`(smulX n, smulY n)`
really are the affine coordinates of `n • (X, Y)`, for every `n ≠ 0`. `smulY`'s own sign rule is
here too: negating a nonzero index negates the point, so `smulY (-n)` is the `negY` of
`(smulX n, smulY n)`.

The middle of the file turns that calculus on the pair `(smulX 1, smulY 1)`, which is the
distinguished point `(X, Y)` itself. For `n ≠ 0` the vertical gap
`smulY n - negY (smulX n) (smulY n)` is `ψ₂ₙ/ψₙ⁴`, hence nonzero, so `smulY n` never equals the
`negY` of its own pair. The quotient formula genuinely needs `n ≠ 0`, since `ψ₀ = 0` leaves it
meaningless; `smulY_ne_negY` carries the same hypothesis because it is *derived* from that formula,
not because it fails at `n = 0` — there it reads `0 ≠ -a₃`, which holds. At `n = 1` the gap
is `ψ₂`, which selects the tangent branch of Mathlib's `Affine.slope` and gives the tangent slope
`slopeOne` the closed form `-Wₓ/ψ₂`. Feeding that slope to Mathlib's affine addition formula sends
`(smulX 1, smulY 1)` to `(smulX 2, smulY 2)`: `addX … = smulX 2` and `addY … = smulY 2`. Those two
are the `n = 2` base case of the induction; `smulX_add` and `smulY_add_sub_negY`, the chord
formulas relating the values at `n + m`, `n - m`, `n` and `m`, are its step.

With the identification in hand the geometric consequences are immediate: the distinguished point
is not torsion (`zsmul_point_ne_zero`), and `n ↦ n • point` is injective
(`Jacobian.zsmul_point_injective`). Next comes the Jacobian form of the identification, where
the three division polynomials appear as honest homogeneous coordinates `(φₙ : ωₙ : ψₙ)` and the
statement needs no hypothesis on `n` at all: at `n = 0` the triple is the point at infinity.

That Jacobian form is what lets Mathlib's doubling and addition formulas be run on the triple
directly. `dblXYZ_smulField` and `addXYZ_smulField` say that `dblXYZ` and `addXYZ` carry
`(φₙ : ωₙ : ψₙ)` to `(φ₂ₙ : ω₂ₙ : ψ₂ₙ)` and `(φₘ : ωₘ : ψₘ)`, `(φₙ : ωₙ : ψₙ)` to
`(φₙ₊ₘ : ωₙ₊ₘ : ψₙ₊ₘ)` scaled by `ψₙ₋ₘ` — as equalities of triples, not merely of the points they
represent, which is what makes them usable as rewrite rules. Both descend to `Universal.Ring`,
where they are identities between polynomials modulo the Weierstrass polynomial.

The file closes by specializing. A point `(x, y)` on a curve `W` over any commutative ring induces
`Universal.ringEval`, and `ringEval_comp_smulRing` says it carries the universal triple to
`smulEval W x y n`, the division polynomials of `W` evaluated at `(x, y)`. The three identities
above therefore hold for `W` at `(x, y)`, and feeding them to an even-odd induction proves
**`zsmul_point_eq_smulEval`**: over a field, `n • (x, y)` has Jacobian coordinates
`(φₙ(x,y) : ωₙ(x,y) : ψₙ(x,y))`, for every `n` and with no hypothesis on the characteristic. That
is the statement the Nagell–Lutz layer consumes.

## Main definitions

* `WeierstrassCurve.Universal.Affine.smulX`: the rational function `φₙ/ψₙ²`.
* `WeierstrassCurve.Universal.Affine.smulY`: the rational function `ωₙ/ψₙ³`.
* `WeierstrassCurve.Universal.Affine.slopeOne`: the slope of the tangent at `(X, Y)`.
* `WeierstrassCurve.Universal.Jacobian.smulPoly`, `.smulRing`, `.smulField`: the triple
  `(φₙ, ωₙ, ψₙ)` as a `Fin 3 → _`, over the polynomial ring, the universal ring and the
  universal field respectively.
* `WeierstrassCurve.smulEval`: the same triple for a concrete curve `W`, evaluated at a point
  `(x, y)` of the affine plane over any commutative ring.

## Main results

* `WeierstrassCurve.Universal.Affine.smulX_eq`: `smulX n = smulX 1 - ψₙ₊₁ψₙ₋₁/ψₙ²` for `n ≠ 0`,
  the offset from the `X`-coordinate that `smulX_two` and `smulX_sub_smulX` both run through.
* `WeierstrassCurve.Universal.Affine.smulX_sub_smulX`: `smulX m - smulX n` as a single
  quotient, by the elliptic-sequence relation of the universal `ψ` family.
* `WeierstrassCurve.Universal.Affine.smulX_ne_zero`: `smulX n ≠ 0` for `n ≠ 0`.
* `WeierstrassCurve.Universal.Affine.smulX_eq_smulX_iff`: `smulX m = smulX n ↔ m = n ∨ m = -n`,
  the field-level form of the fact that `x`-coordinates separate multiples up to sign.
* `WeierstrassCurve.Universal.Affine.smulY_neg`: for `n ≠ 0`, `smulY (-n)` is the `negY` of the
  coordinates at `n` — the long-Weierstrass correction that `ω_neg` carries, in the universal
  field.
* `WeierstrassCurve.Universal.Affine.smulY_sub_negY`: the gap `smulY n - negY (smulX n) (smulY n)`
  is `ψ₂ₙ/ψₙ⁴`, whence `smulY_ne_negY` — the gap never vanishes for `n ≠ 0`.
* `WeierstrassCurve.Universal.Affine.slopeOne_eq_neg_div`: the tangent slope at `(X, Y)` is
  `-Wₓ/ψ₂`, the ratio of the two partial derivatives of the Weierstrass polynomial.
* `WeierstrassCurve.Universal.Affine.addX_smul_one_smul_one`,
  `.addY_smul_one_smul_one`: doubling `(X, Y)` along that tangent with Mathlib's affine addition
  formula returns `(smulX 2, smulY 2)` — the base case of the scalar-multiplication induction.
* `WeierstrassCurve.Universal.Affine.smulX_add`, `.smulY_add_sub_negY`: the chord formulas, giving
  `smulX (n + m)` and the vertical gap at `n + m` in terms of the values at `n`, `m` and `n - m`
  — the induction step.
* `WeierstrassCurve.Universal.Affine.zsmul_point_eq_smulX_smulY`: **the identification**. For
  `n ≠ 0` the pair `(smulX n, smulY n)` is nonsingular and `n • (X, Y)` is the affine point it
  names.
* `WeierstrassCurve.Universal.Affine.zsmul_point_ne_zero` and
  `WeierstrassCurve.Universal.Jacobian.zsmul_point_ne_zero`:
  the distinguished point is not torsion, in affine and in Jacobian coordinates; whence
  `Jacobian.zsmul_point_injective`, that `n ↦ n • point` is injective.
* `WeierstrassCurve.Universal.Jacobian.zsmul_point_eq_smulField`: the Jacobian identification,
  `(n • point).point = ⟦(φₙ : ωₙ : ψₙ)⟧`, with no hypothesis on `n`.
* `WeierstrassCurve.Universal.Jacobian.dblXYZ_smulField`, `.addXYZ_smulField`: Mathlib's Jacobian
  doubling and addition formulas evaluated on the universal triples, as equalities of triples.
  `.dblXYZ_smulRing` and `.addXYZ_smulRing` are the same over `Universal.Ring`.
* `WeierstrassCurve.Universal.Jacobian.dblZ_smulPoly`, `.addZ_smulPoly`: the `Z`-coordinates of
  those two formulas, `ψ₂ₙ` and `ψₙ₊ₘψₙ₋ₘ`, already in the polynomial ring — no reduction modulo
  the Weierstrass polynomial is needed for the third coordinate.
* `WeierstrassCurve.Universal.Jacobian.smulPoly_neg`, `.smulRing_neg`, `.smulField_neg`: negating
  the index is Mathlib's Jacobian negation rescaled by `-1`.
* `WeierstrassCurve.Universal.ringEval_comp_smulRing`: `smulEval` is the specialization of
  `smulRing` along the homomorphism a point of `W` induces — the bridge from the universal
  identities to a concrete curve, and what `dblXYZ_smulEval` and `addXYZ_smulEval` are proved
  through.
* `WeierstrassCurve.zsmul_point_eq_smulEval`: **the headline**. Over a field, `n • (x, y)`
  in Jacobian
  coordinates is `(φₙ(x,y) : ωₙ(x,y) : ψₙ(x,y))`, for every nonsingular `(x, y)` and every `n`.
* `WeierstrassCurve.two_zsmul_eq_zero_of_evalEval_ψ₂_eq_zero`: the converse at `n = 2` — a
  vanishing `ψ₂` at a nonsingular point forces `2 • P = 0`.

## Provenance

Ported from J. Xu and D. K. Angdinata's `projects/NagellLutz/LutzNagell/ZSMul.lean` in AINTLIB
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0, `main @
1c1c74664e40071c2c2165bc55ca2616a67ccd6b`): `smulX` (`:164`), `smulY` (`:168`), the value
lemmas (`:171`–`:174`), `smulX_eq` (`:176`), `smulX_two` (`:183`), `smulX_sub_smulX` (`:186`),
`smulX_neg` (`:201`), `smulX_ne_zero` (`:203`), `smulX_ne_smulX` (`:206`),
`smulX_eq_smulX_iff` (`:217`), and `smulY_neg` (`:290`), pulled forward from the slope slice's
range so that `smulY` does not ship without its negative-index rule. The source's `ψᵤ`
abbreviation is dropped in favour of `polyToField (curve.ψ n)`, the
`DivisionPolynomial/Universal.lean` convention.

Five departures beyond that respelling. The elliptic-sequence step of `smulX_sub_smulX` is
respelt through `IsEllipticNet.rel` and `linear_combination` (the source converts against its
`isEllSequence_ψᵤ`, a statement shape Mathlib has since replaced). The equation lemmas
`smulX_def` and `smulY_def` are added for consumers in other modules, as in `Omega.lean`.
`smulY_neg` reads its coordinate identity off Mathlib's `Jacobian.negY_of_Z_ne_zero` at
`(φₙ : ωₙ : ψₙ)` instead of the source's private field-level auxiliary (`:286`), still naming
its ring hom (`map_neg polyToField`) where the source unfolds `ψᵤ`, because an unnamed
`map_neg` does not fire on a `polyToField` application in this direction. `smulX_eq` meets that
same direction problem — the source's forward
`simp only [φ, ψᵤ, map_sub, map_mul, map_pow, ← add_div]` does not fire here — so it instead
maps a polynomial-level identity with `congrArg polyToField` and clears the denominator with
`field_simp` and `linear_combination`. Finally `@[simp]` is added to `smulX_neg`, `smulY_neg`,
`smulX_ne_zero` and `smulX_eq_smulX_iff`; the source tags only the four value lemmas.

The tangent-and-doubling block below adds, at the same revision, `smulY_sub_negY` (`:227`),
`slopeOne` (`:241`), `slopeOne_eq_neg_div` (`:244`), `addX_smul_one_smul_one` (`:261`) and
`addY_smul_one_smul_one` (`:277`), with the same `ψᵤ` respelling and one added equation lemma,
`slopeOne_def`.

One statement is generalised rather than transcribed, and the source's two `n = 1` wrappers go
with it. The source proves only `smulY_one_ne_negY` (`:237`); here `smulY_ne_negY` states it for
every `n ≠ 0`, which `smulY_sub_negY` already gives — the gap `ψ₂ₙ/ψₙ⁴` is a quotient of nonzero
elements. Given the general form, both of the source's specialisations are **dropped rather than
ported**: `smulY_one_ne_negY` (`:237`) is `smulY_ne_negY one_ne_zero` and is written that way at
its two call sites, and `smulY_one_sub_negY` (`:233`) is `smulY_sub_negY one_ne_zero` followed by
the collapse of `ψ₂ₙ` to `ψ₂` and `ψₙ⁴` to `1`, which its one consumer `slopeOne_eq_neg_div`
carries as a local `have`.

None of the source's four private field-level auxiliaries in that range is ported, because none
of them has a consumer left here.

* `smulY_sub_negY_aux` (`:222`) is not needed: `smulY_sub_negY` runs through this file's own
  `smulY_neg` — negating the index negates the point — which already reads its coordinate identity
  off Mathlib's `Jacobian.negY_of_Z_ne_zero`. What is left is `ω_neg`, `ω_spec` and `ψ_mul_ψc`,
  with no field-level algebra to package.
* `addX_smul_one_smul_one_aux` (`:252`) has no call site **in the source either**: at
  `1c1c7466` the name occurs exactly once repo-wide per copy, its own definition.
* `addX_smul_ring_identity` (`:257`) and `addY_smul_one_smul_one_aux` (`:271`) each package the
  residue of one `field_simp` in the source's normal form. Both residues differ here, and
  `linear_combination` against the mapped certificate, respectively `ring`, closes each in a line.

Two further departures. Mathlib's `Affine.slope` is defined by cases, and the source supplies the
decidability it needs with a namespace-wide `attribute [local instance] Classical.propDecidable`
(`:159`, and again at `:406`). Nothing of the kind is needed here: Mathlib carries
`FractionRing.instDecidableEq`, so `DecidableEq Universal.Field` synthesizes outright — checked
with `#synth`, which returns that instance — and every declaration in this file mentioning
`slope` or the Jacobian group law elaborates without any `Classical`.
And the map-direction problem recorded above for `smulX_eq` recurs at every proof in the block.
Measured against the `unusedSimpArgs` linter at this pin: bare `map_sub` and `map_neg` fire at no
site, while bare `map_mul`, `map_add`, `map_pow` and `map_ofNat` fire at all of them — the
unexposed instances are `Sub` and `Neg`. Each `map_*` names its hom regardless, for uniformity
with the rest of the file. Naming alone is not enough in the last three proofs, which state their
polynomial-level certificate as a `have` and map it with `congrArg polyToField`, the shape
`smulX_eq` uses: `polyToField_apply` is `@[simp]` here, so `field_simp` shatters
`polyToField (C X)` into `algebraMap _ _ (AdjoinRoot.of _ X)` while leaving
`polyToField curve.polynomialX` folded, and the two sides of the goal then share no atoms.

The identification block below adds, at the same revision,
`smulX_add` (`:300`), `smulY_add_sub_negY` (`:324`), `eq_of_sub_negY_eq` (`:345`),
`zsmul_point_eq_smulX_smulY` (`:353`),
`Affine.zsmul_point_ne_zero` (`:398`), `Jacobian.zsmul_point_ne_zero` (`:411`),
`Jacobian.zsmul_point_injective` (`:416`), `smulPoly`, `smulRing` and
`smulField` (`:423`–`:427`), `algebraMap_comp_smulRing` (`:429`) and
`Jacobian.zsmul_point_eq_smulField` (`:433`). The first three come from before the previous
slice's range: they are the chord formulas, and the headline induction step cannot be stated
without them. The source's `curveField` has no counterpart here and is spelled
`pointedCurve.toAffine`.

One prerequisite is **strengthened rather than transcribed**, in
`DivisionPolynomial/Universal.lean`: what was `isEllipticSequence_polyToField_ψ` is now
`isEllipticNet_polyToField_ψ`, the source's `net_ψᵤ` (`:140`) rather than its
`isEllSequence_ψᵤ` (`:139`). `smulY_add_sub_negY` needs the elliptic-net relation at the
**nonzero** shift `s = m`, which an elliptic sequence — the `s = 0` case — does not give;
`isEllipticNet_normEDS` was already available, so the change is two tokens, and
`smulX_sub_smulX`, the one existing call site, takes the `s = 0` instance.

`eq_of_sub_negY_eq` is the first consumer of `(2 : Universal.Field) ≠ 0`. No instance is added for
it: Mathlib's `charZero` for a fraction ring carries `CharZero Universal.Field` from
`CharZero Universal.Ring`, and `EllipticCurve/Universal.lean` imports `Algebra/CharP/Algebra.lean`
so that it is in scope.

One statement is restated. The source's `zsmul_point_ne` (`:416`) is the pairwise form
`m ≠ n → m • point ≠ n • point`; here it is `zsmul_point_injective`, the equivalent
`Function.Injective fun n : ℤ ↦ n • Jacobian.point`, which says the same thing in the idiom the
rest of the library uses and composes with the `Function.Injective` API.

Five departures inside the block itself. The source's `some_eq_some_iff` (used at `:372`) is
**not** added: Mathlib's spelling is the auto-generated `Affine.Point.some.injEq`, which Mathlib
itself uses, and `EllipticCurve/Universal.lean` records that this repository declines `Iff`
wrappers around auto-generated `injEq`s. The source's two `erw`s (`:363`, `:372`) are both gone:
the first only bridged `((0 + 1 + 1 : ℕ) : ℤ)` to `(2 : ℤ)`, which an explicit cast rewrite
does, and the second additionally saw through `Affine.Point.neg_some`, which is a named `rfl`
lemma and can simply be cited. The `n = 1` instance of the induction hypothesis is obtained at an
ascribed type so that its index cast is normalised **before** the pair is destructured: afterwards
the nonsingularity witness mentions the cast, and no rewrite of the equation alone is
type-correct. And the two chord formulas are stated without the source's cosmetic
`let ψ₂ x y := y - negY x y` binder, which the source immediately removes again with `change`.
And of the block's two candidate `@[simp]` lemmas only `algebraMap_comp_smulRing` carries the
tag. `zsmul_point_eq_smulField` cannot: `Jacobian.point_def` and `Affine.point_def` are both
`@[simp]`, so simpNF reports the left-hand side `(n • Jacobian.point).point` as not in normal
form — it reduces to `(Point.fromAffine (Affine.Point.mk ⋯)).point` before the lemma could fire.
It was tagged and rejected by a full `lint-env` run before being left untagged.

Three declarations of the source's are not ported. Its `smulX_add_aux` (`:295`) and
`smulY_add_sub_negY_aux` (`:317`) each package the residue of one `field_simp`; both residues
differ here and are closed in place. Its `net_add_sub_iff`, which lives in
`LutzNagell/EllipticDivisibilitySequence.lean` rather than in this file, is inlined as the local
`key` of `smulY_add_sub_negY` — normalising the eight index sums of `IsEllipticNet.rel` needs
`linear_combination (norm := ring_nf)`, since `ring1` does not reduce inside `curve.ψ`'s argument.
The source's `instance : AddGroup ((curve.baseChange Universal.Field).toAffine.Point)` (`:341`) is
an `inferInstance` cache and is not needed, and neither is its second
`attribute [local instance] Classical.propDecidable` (`:406`), for the reason already given.

The final block below completes the port of the source file, adding, at the same revision,
`dblZ_smulPoly` (`:446`), `nonsingular_smulField` (`:454`), `dblXYZ_smulField` (`:469`),
`dblXYZ_smulRing` (`:480`), `addZ_smulPoly` (`:484`), `smulPoly_neg` (`:496`),
`smulRing_neg` (`:499`), `smulField_neg` (`:502`), `smulPoly_zero` and
`smulField_zero` (`:505`–`:506`), `addXYZ_smulField` (`:508`), `addXYZ_smulRing` (`:533`),
then `smulEval` (`:560`), `ringEval_comp_smulRing` (`:566`), `dblXYZ_smulEval` (`:577`),
`addXYZ_smulEval` (`:581`) and `zsmul_eq_smulEval` (`:599`), the last ported under the name
`zsmul_point_eq_smulEval` because its conclusion is about the `.point` projection. The three
`₁`-suffixed
adjacent-index lemmas (`:539`, `:546`, `:589`) are in the source's range but are **not** ported,
for the reason given below.
The two zero lemmas are moved ahead of `dblXYZ_smulField`, which uses `smulField_zero` to
identify the `n = 0` triple; the source proves that case by unfolding `dblXYZ` instead.
`ringEval_comp_smulRing` is placed in the `Universal` namespace rather than at
`WeierstrassCurve` level as upstream, matching where `EllipticCurve/Universal.lean` keeps the rest
of the `ringEval` API. The source's `curveRing_map_ringEval` is this repository's `map_ringEval`.
The source's `ringEval_ψ` (`:572`) is **not ported**: it is the third coordinate of
`ringEval_comp_smulRing`, used once, so it lives as a typed local `have` in `addXYZ_smulEval`
rather than as public API.
The source's `ω_neg_eq_neg_negY` (`:489`) is **not ported**: it is `ω_neg` followed by `negY_eq`
and `ring`, and `smulPoly_neg` — its only advertised consumer — discharges the middle coordinate
through the default `simp` set instead, so the intermediate lemma has no caller.

**None of the source's three `₁`-suffixed adjacent-index lemmas is ported** (`:539`, `:546`,
`:589`). Each is its `addXYZ_smul{Field,Ring,Eval}` parent followed by `add_sub_cancel_left`,
`ψ_one`, `map_one`/`evalEval_one` and `one_smul` — the scaling factor at adjacent indices is
`ψ` of a gap of `1`. Only the `Eval` form ever had a consumer, and only one, so those four
rewrites are appended to that call site's own `rw` chain instead; the intermediate
specialisations earn nothing.

**`point_point` (`:420`) is not ported at all, and the previous slice's copy of it is deleted
here.** That slice predicted this block would supply a consumer; it does not. At `1c1c7466` the
source's `point_point` occurs exactly once per copy — its own definition — so nothing consumes it
upstream either, and it restates `Jacobian.point_def`, `Affine.point_def` and
`Point.fromAffine_some` without adding content. `algebraMap_comp_smulRing` (`:429`), predicted
alongside it, **is** consumed — cited four times
across `dblXYZ_smulRing`, `addXYZ_smulRing` and `smulField_neg`. It is load-bearing rather than
decorative: upstream `algebraMap _ _ ∘ smulRing n = smulField n` holds by `rfl`, and here it does
not, `polyToField`'s body being unexposed.

One prerequisite is added, in `EllipticCurve/Universal.lean`: `map_polyToField`, for the same
reason. Upstream `curveField = curvePoly.map polyToField` definitionally, so a curve-dependent
transport such as `map_dblZ` lands on `curveField` with no further step; here it lands on
`curvePoly.map polyToField` and the identification has to be cited. Both proofs that cite it do so
after `map_dblZ`. `map_addZ` is not in that class: `addZ` takes no curve argument, so its transport
never mentions a mapped curve. `map_polyToField` carries `@[simp]`, as does
`ringEval_comp_smulRing`: both are map-specialization normal forms, reducing a mapped universal
object to the concrete one it names, and neither loops. `api-design` asked for both tags in round
three, over an initial judgement here that two explicit call sites did not warrant the global
surface; the normal-form reading is the better one, and a full `lint-env` confirms neither tag
introduces a simpNF violation.

Two of the source's proofs are replaced rather than transcribed, both because a tactic upstream
relies on is unavailable over `Poly = ℤ[A₁,⋯,A₆][X][Y]`. Instance search gives up on that
triple-nested polynomial ring — `IsRightCancelAdd Poly` and `HasDistribNeg Poly` both fail to
synthesize in this import closure, while their two-level analogues succeed and raising
`synthInstance.maxSize` does not help. So `addZ_smulPoly` discharges its elliptic-sequence
certificate through `sub_eq_zero` and `ring` where the source uses `convert`, and `smulPoly_neg`
is proved coordinatewise with `ring` where the source uses a single `simp` carrying
`Odd.neg_pow`. `ring` itself works over `Poly`; it is the additive-cancellation and sign lemmas
that are out of reach.

`ringEval_comp_smulRing` is also proved differently. The source threads a nine-lemma `conv_rhs`
chain that ends by unfolding `polyEval`; that definition's body is unexposed here. The proof
instead runs coordinatewise through `ringEval_mk` and `evalEval_φ`/`evalEval_ω`/`evalEval_ψ`,
which `DivisionPolynomial/Universal.lean` already carries — the source's own `:99`–`:106`, ported
in an earlier slice and, before this proof, cited nowhere outside their own file.

Finally the source's two private helpers in this range, `two_zsmul_point_eq_dblXYZ` (`:458`) and
`add_point_of_ne_eq_addXYZ` (`:463`), are **not** ported as declarations. Each has exactly one
call site and one instantiation, so each is inlined as a typed local `have` — `h2` in
`dblXYZ_smulField` and `hadd` in `addXYZ_smulField` — which keeps both proofs inside the length
cap. The source's `zsmul_point_ne`, which `add_point_of_ne_eq_addXYZ` consumes, is this file's
`zsmul_point_injective`, so the distinctness side condition is discharged through injectivity.
-/

public section

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Universal.Affine

variable {m n : ℤ}

/-- The rational function `φₙ/ψₙ²` in the universal field. For `n ≠ 0` it is the affine
`X`-coordinate of `n • (X, Y)` on the universal curve, by `zsmul_point_eq_smulX_smulY` below. -/
def smulX (n : ℤ) : Universal.Field :=
  polyToField (curve.φ n) / polyToField (curve.ψ n) ^ 2

/-- The rational function `ωₙ/ψₙ³` in the universal field. For `n ≠ 0` it is the affine
`Y`-coordinate of `n • (X, Y)` on the universal curve, by `zsmul_point_eq_smulX_smulY` below. -/
def smulY (n : ℤ) : Universal.Field :=
  polyToField (curve.ω n) / polyToField (curve.ψ n) ^ 3

/-- The defining formula for `smulX`. The definition body is not exposed, so this equation
lemma is how a consumer in another module computes with it. -/
theorem smulX_def (n : ℤ) : smulX n = polyToField (curve.φ n) / polyToField (curve.ψ n) ^ 2 := (rfl)

/-- The defining formula for `smulY`. The definition body is not exposed, so this equation
lemma is how a consumer in another module computes with it. -/
theorem smulY_def (n : ℤ) : smulY n = polyToField (curve.ω n) / polyToField (curve.ψ n) ^ 3 := (rfl)

/-- `smulX` at `0` is `0`. -/
@[simp] lemma smulX_zero : smulX 0 = 0 := by simp [smulX_def]

/-- `smulY` at `0` is `0`. -/
@[simp] lemma smulY_zero : smulY 0 = 0 := by simp [smulY_def]

/-- `smulX` at `1` is the `X`-coordinate itself. -/
@[simp] lemma smulX_one : smulX 1 = polyToField (C X) := by simp [smulX_def]

/-- `smulY` at `1` is the `Y`-coordinate itself. -/
@[simp] lemma smulY_one : smulY 1 = polyToField Y := by simp [smulY_def]

/-- `smulX n` differs from the `X`-coordinate by `ψₙ₊₁ψₙ₋₁/ψₙ²`. -/
lemma smulX_eq (hn : n ≠ 0) :
    smulX n = smulX 1 - polyToField (curve.ψ (n + 1)) * polyToField (curve.ψ (n - 1)) /
      polyToField (curve.ψ n) ^ 2 := by
  have hψ : polyToField (curve.ψ n) ≠ 0 := polyToField_ψ_ne_zero hn
  have h : curve.φ n + curve.ψ (n + 1) * curve.ψ (n - 1) = C X * curve.ψ n ^ 2 := by
    rw [WeierstrassCurve.φ]
    ring
  have hF := congrArg polyToField h
  simp only [map_add polyToField, map_mul polyToField, map_pow polyToField] at hF
  rw [smulX_def, smulX_one]
  field_simp
  linear_combination hF

/-- `smulX` at `2`, in terms of the `X`-coordinate and `ψ₃/ψ₂²`. -/
lemma smulX_two : smulX 2 = smulX 1 - polyToField (curve.ψ 3) / polyToField (curve.ψ 2) ^ 2 := by
  simp [smulX_eq two_ne_zero]

/-- The difference of two values of `smulX` as a single quotient: the numerator is
`ψₙ₊ₘψₙ₋ₘ`, by the elliptic-sequence relation of the universal `ψ` family. -/
lemma smulX_sub_smulX (hm : m ≠ 0) (hn : n ≠ 0) :
    smulX m - smulX n = polyToField (curve.ψ (n + m)) * polyToField (curve.ψ (n - m)) /
      (polyToField (curve.ψ n) * polyToField (curve.ψ m)) ^ 2 := by
  have key := isEllipticNet_polyToField_ψ n m 1 0
  simp only [IsEllipticNet.rel, add_zero, ψ_one, map_one, mul_one] at key
  rw [smulX_eq hm, smulX_eq hn, sub_sub_sub_cancel_left,
    div_sub_div _ _ (pow_ne_zero 2 (polyToField_ψ_ne_zero hn))
      (pow_ne_zero 2 (polyToField_ψ_ne_zero hm)), mul_pow]
  congr 1
  linear_combination -key

/-- `smulX` is even in `n`. -/
@[simp] lemma smulX_neg : smulX (-n) = smulX n := by simp [smulX_def, φ_neg, ψ_neg]

/-- Negating a nonzero index negates the point: `smulY (-n)` is the long-Weierstrass `negY`
of the coordinates `(smulX n, smulY n)`. -/
@[simp] lemma smulY_neg (h0 : n ≠ 0) :
    smulY (-n) = pointedCurve.toAffine.negY (smulX n) (smulY n) := by
  -- The identity is Mathlib's Jacobian-to-affine `negY` formula at `(φₙ : ωₙ : ψₙ)`.
  have key := WeierstrassCurve.Jacobian.negY_of_Z_ne_zero (W := pointedCurve)
    (P := ![polyToField (curve.φ n), polyToField (curve.ω n), polyToField (curve.ψ n)])
    (by simpa using polyToField_ψ_ne_zero h0)
  simp only [WeierstrassCurve.Jacobian.negY_eq, pointedCurve_a₁, pointedCurve_a₃,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons] at key
  refine .trans ?_ key
  -- `ω_neg` negates the numerator and `ψ_neg` the denominator's cube, so the signs cancel.
  rw [smulY_def, ψ_neg, ω_neg]
  simp only [map_add polyToField, map_mul polyToField, map_pow polyToField, map_neg polyToField]
  ring

/-- `smulX n` is nonzero for `n ≠ 0`. -/
@[simp] lemma smulX_ne_zero (h0 : n ≠ 0) : smulX n ≠ 0 :=
  div_ne_zero polyToField_φ_ne_zero (pow_ne_zero _ <| polyToField_ψ_ne_zero h0)

/-- `smulX` separates indices that agree in neither order nor sign. -/
lemma smulX_ne_smulX (ne : m ≠ n) (ne_neg : m ≠ -n) : smulX m ≠ smulX n := by
  obtain rfl | hm := eq_or_ne m 0
  · simpa using (smulX_ne_zero ne.symm).symm
  obtain rfl | hn := eq_or_ne n 0
  · simpa using smulX_ne_zero ne
  rw [← sub_ne_zero, smulX_sub_smulX hm hn]
  refine div_ne_zero (mul_ne_zero ?_ ?_) (pow_ne_zero _ <| mul_ne_zero ?_ ?_) <;>
    apply polyToField_ψ_ne_zero <;> omega

/-- Two values of `smulX` agree exactly when the indices agree up to sign. -/
@[simp] lemma smulX_eq_smulX_iff : smulX m = smulX n ↔ m = n ∨ m = -n := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · contrapose! h
    exact smulX_ne_smulX h.1 h.2
  · rintro (rfl | rfl)
    exacts [rfl, smulX_neg]

/-- **The gap between `smulY n` and the `negY` of its own pair is `ψ₂ₙ/ψₙ⁴`.** Being a quotient of
nonzero `ψ`'s it never vanishes, which is what puts the pair `(smulX n, smulY n)` in the tangent
branch of `Affine.slope`. -/
-- The proof reads the negated coordinate off `smulY_neg`, so the gap becomes
-- `smulY n - smulY (-n)`; `ω_neg` turns the numerator into `2ωₙ + a₁φₙψₙ + a₃ψₙ³`, which
-- `ω_spec` names `ψc n` and `ψ_mul_ψc` divides into `ψ₂ₙ/ψₙ`.
lemma smulY_sub_negY (h0 : n ≠ 0) :
    smulY n - pointedCurve.toAffine.negY (smulX n) (smulY n) =
      polyToField (curve.ψ (2 * n)) / polyToField (curve.ψ n) ^ 4 := by
  have hψ : polyToField (curve.ψ n) ≠ 0 := polyToField_ψ_ne_zero h0
  have h : curve.ψ n * (2 * curve.ω n + CC curve.a₁ * curve.φ n * curve.ψ n
      + CC curve.a₃ * curve.ψ n ^ 3) = curve.ψ (2 * n) := by rw [ω_spec, ψ_mul_ψc]
  have hF := congrArg polyToField h
  simp only [map_mul polyToField, map_add polyToField, map_pow polyToField, map_ofNat] at hF
  rw [← smulY_neg h0, smulY_def, smulY_def, ψ_neg, ω_neg]
  simp only [map_add polyToField, map_mul polyToField, map_pow polyToField, map_neg polyToField]
  field_simp
  linear_combination hF

/-- **`smulY n` never equals the `negY` of its own pair, for `n ≠ 0`.** The gap computed above is
`ψ₂ₙ/ψₙ⁴`, a quotient of nonzero elements. -/
lemma smulY_ne_negY (h0 : n ≠ 0) :
    smulY n ≠ pointedCurve.toAffine.negY (smulX n) (smulY n) := by
  rw [← sub_ne_zero, smulY_sub_negY h0]
  exact div_ne_zero (polyToField_ψ_ne_zero (by omega))
    (pow_ne_zero _ (polyToField_ψ_ne_zero h0))

/-- The slope of the tangent line to `pointedCurve` at its distinguished point `(X, Y)`: Mathlib's
`Affine.slope` at the coincident pair `(X, Y), (X, Y)`. -/
def slopeOne : Universal.Field :=
  pointedCurve.toAffine.slope (smulX 1) (smulX 1) (smulY 1) (smulY 1)

/-- The defining formula for `slopeOne`. The definition body is not exposed, so this equation
lemma is how a consumer in another module computes with it. -/
theorem slopeOne_def :
    slopeOne = pointedCurve.toAffine.slope (smulX 1) (smulX 1) (smulY 1) (smulY 1) := (rfl)

/-- **The tangent slope in closed form**: `-Wₓ/ψ₂`, the ratio of the two partial derivatives of
the Weierstrass polynomial at `(X, Y)`. -/
lemma slopeOne_eq_neg_div :
    slopeOne = -polyToField curve.polynomialX / polyToField (curve.ψ 2) := by
  have h : curve.polynomialX
      = CC curve.a₁ * Y - (3 * C X ^ 2 + 2 * CC curve.a₂ * C X + CC curve.a₄) := by
    simp_rw [Affine.polynomialX, CC]
    simp only [map_ofNat, C_add, C_mul, C_pow]
  -- The gap at `n = 1`: `smulY_sub_negY`'s numerator `ψ₂ₙ` is `ψ₂` and its denominator `ψₙ⁴`
  -- is `1`, so the tangent branch's denominator is `ψ₂`.
  have hgap : smulY 1 - pointedCurve.toAffine.negY (smulX 1) (smulY 1) =
      polyToField (curve.ψ 2) := by
    rw [smulY_sub_negY one_ne_zero, mul_one, ψ_one, map_one, one_pow, div_one]
  rw [slopeOne_def, Affine.slope_of_Y_ne rfl (smulY_ne_negY one_ne_zero), hgap, h,
    smulX_one, smulY_one, pointedCurve_a₁, pointedCurve_a₂, pointedCurve_a₄]
  simp only [map_add polyToField, map_sub polyToField, map_mul polyToField,
    map_pow polyToField, map_ofNat]
  ring

/-- **Mathlib's `addX` at `(smulX 1, smulX 1)` along the tangent slope is `smulX 2`.** The affine
addition formula run on the distinguished point against itself lands on the value at `2`. -/
-- The certificate is `C_Ψ₃`, expressing `Ψ₃` through the partial derivatives: in the universal
-- field `Ψ₂Sq` becomes `ψ₂²` and the Weierstrass polynomial vanishes, leaving the numerator
-- identity that clearing `ψ₂²` out of `addX` demands.
lemma addX_smul_one_smul_one :
    pointedCurve.toAffine.addX (smulX 1) (smulX 1) slopeOne = smulX 2 := by
  have hψ₂ : polyToField (curve.ψ 2) ≠ 0 := polyToField_ψ_ne_zero two_ne_zero
  have hF := congrArg polyToField (C_Ψ₃ curve)
  simp only [map_sub polyToField, map_add polyToField, map_mul polyToField, map_pow polyToField,
    map_ofNat, polyToField_Ψ₂Sq, polyToField_polynomial, mul_zero, ← ψ_three, ← ψ_two] at hF
  rw [Affine.addX, slopeOne_eq_neg_div, smulX_two, smulX_one, pointedCurve_a₁, pointedCurve_a₂]
  field_simp
  linear_combination hF

/-- **The same for `addY`: it returns `smulY 2`.** Together with the previous lemma this is the
`n = 2` base case of `zsmul_point_eq_smulX_smulY` below, which is what makes `(smulX 2, smulY 2)`
the coordinates of `2 • (X, Y)`. -/
-- The certificate is `ω_def` at `2`: the reduced-invariant denominator is `1` and the
-- complement's auxiliary term `0`, the multiples of the Weierstrass polynomial vanish,
-- `polynomialY` is `ψ₂` and `C Ψ₃` is `ψ₃`, giving the numerator `addY` produces over `ψ₂³`.
lemma addY_smul_one_smul_one :
    pointedCurve.toAffine.addY (smulX 1) (smulX 1) (smulY 1) slopeOne = smulY 2 := by
  have hψ₂ : polyToField (curve.ψ 2) ≠ 0 := polyToField_ψ_ne_zero two_ne_zero
  have hY : Affine.polynomialY curve = curve.ψ 2 := by rw [ψ_two, ψ₂]
  have hneg : Affine.negPolynomial curve
      = -(Y : Poly) - (CC curve.a₁ * C X + CC curve.a₃) := by
    rw [Affine.negPolynomial]
    simp only [C_add, C_mul]
  have hF := congrArg polyToField (ω_def curve 2)
  simp only [reducedInvarDenom_two, complEDS₂Aux_two, one_mul, sub_zero, hY, hneg, ← ψ_three,
    map_add polyToField, map_sub polyToField, map_mul polyToField, map_pow polyToField,
    map_neg polyToField, map_ofNat, polyToField_polynomial, mul_zero, zero_mul, add_zero] at hF
  rw [Affine.addY, Affine.negAddY, addX_smul_one_smul_one, smulY_one, smulX_two, smulX_one,
    slopeOne_eq_neg_div, Affine.negY, pointedCurve_a₁, pointedCurve_a₃, smulY_def 2, hF]
  field_simp
  ring

/-- The difference `smulX (n - m) - smulX (n + m)` as a single quotient, with numerator
`ψ₂ₙψ₂ₘ`: this is `smulX_sub_smulX` at the pair `(n - m, n + m)`, whose index sum and difference
collapse to `2n` and `2m`. -/
lemma smulX_sub_sub_smulX_add (add_ne : n + m ≠ 0) (sub_ne : n - m ≠ 0) :
    smulX (n - m) - smulX (n + m) =
      polyToField (curve.ψ (2 * n)) * polyToField (curve.ψ (2 * m)) /
        (polyToField (curve.ψ (n + m)) * polyToField (curve.ψ (n - m))) ^ 2 := by
  rw [smulX_sub_smulX sub_ne add_ne]
  simp only [show n + m + (n - m) = 2 * n by ring, show n + m - (n - m) = 2 * m by ring]

/-- **The addition formula for the `X`-coordinate.** `smulX (n + m)` is `smulX (n - m)` less the
product of the two vertical gaps, divided by the square of the horizontal one — the classical
chord construction, written in the `smulX`/`smulY` calculus. -/
-- Both sides become quotients of `ψ`'s once `smulY_sub_negY`, `smulX_sub_smulX` and
-- `smulX_sub_sub_smulX_add` are applied; the identity is then pure field algebra.
lemma smulX_add (hm : m ≠ 0) (hn : n ≠ 0) (add_ne : n + m ≠ 0) (sub_ne : n - m ≠ 0) :
    smulX (n + m) = smulX (n - m) -
      (smulY n - pointedCurve.toAffine.negY (smulX n) (smulY n)) *
        (smulY m - pointedCurve.toAffine.negY (smulX m) (smulY m)) / (smulX m - smulX n) ^ 2 := by
  have hψm : polyToField (curve.ψ m) ≠ 0 := polyToField_ψ_ne_zero hm
  have hψn : polyToField (curve.ψ n) ≠ 0 := polyToField_ψ_ne_zero hn
  have hψa : polyToField (curve.ψ (n + m)) ≠ 0 := polyToField_ψ_ne_zero add_ne
  have hψs : polyToField (curve.ψ (n - m)) ≠ 0 := polyToField_ψ_ne_zero sub_ne
  rw [eq_sub_iff_add_eq, ← eq_sub_iff_add_eq', smulY_sub_negY hm, smulY_sub_negY hn,
    smulX_sub_smulX hm hn, smulX_sub_sub_smulX_add add_ne sub_ne]
  field_simp

/-- **The addition formula for the vertical gap.** The gap at `n + m` is a difference of the gaps
at `m` and at `n`, each weighted by a horizontal distance, over the horizontal distance between
`n` and `m`. -/
-- The certificate is the elliptic-net relation `ER(n + m, n, n - m, m)` of the universal `ψ`
-- family. The shift `s = m` is nonzero, which is why `isEllipticNet_polyToField_ψ` is needed and
-- the elliptic-*sequence* consequence used by `smulX_sub_smulX` is not enough.
lemma smulY_add_sub_negY (hm : m ≠ 0) (hn : n ≠ 0) (add_ne : n + m ≠ 0) (sub_ne : n - m ≠ 0) :
    smulY (n + m) - pointedCurve.toAffine.negY (smulX (n + m)) (smulY (n + m)) =
      ((smulY m - pointedCurve.toAffine.negY (smulX m) (smulY m)) * (smulX n - smulX (n + m)) -
        (smulY n - pointedCurve.toAffine.negY (smulX n) (smulY n)) * (smulX m - smulX (n + m))) /
          (smulX m - smulX n) := by
  have hψm : polyToField (curve.ψ m) ≠ 0 := polyToField_ψ_ne_zero hm
  have hψn : polyToField (curve.ψ n) ≠ 0 := polyToField_ψ_ne_zero hn
  have hψa : polyToField (curve.ψ (n + m)) ≠ 0 := polyToField_ψ_ne_zero add_ne
  have hψs : polyToField (curve.ψ (n - m)) ≠ 0 := polyToField_ψ_ne_zero sub_ne
  have hnet := isEllipticNet_polyToField_ψ (n + m) n (n - m) m
  simp only [IsEllipticNet.rel] at hnet
  -- The net relation with its indices normalised. `ring_nf` is the norm because `ring1` does not
  -- reduce inside `curve.ψ`'s argument, where all eight index sums live.
  have key : polyToField (curve.ψ (2 * (n + m))) * polyToField (curve.ψ (n - m)) *
        polyToField (curve.ψ n) * polyToField (curve.ψ m) =
      (polyToField (curve.ψ (2 * n + m)) * polyToField (curve.ψ (2 * m)) *
          polyToField (curve.ψ n) -
        polyToField (curve.ψ (n + 2 * m)) * polyToField (curve.ψ (2 * n)) *
          polyToField (curve.ψ m)) * polyToField (curve.ψ (n + m)) := by
    linear_combination (norm := ring_nf) hnet
  simp_rw [smulY_sub_negY add_ne, smulY_sub_negY hm, smulY_sub_negY hn, smulX_sub_smulX hn add_ne,
    smulX_sub_smulX hm add_ne, smulX_sub_smulX hm hn, add_sub_cancel_left, add_sub_cancel_right]
  field_simp
  linear_combination (norm := ring_nf) key

/-- `z ↦ z - W.negY x z` is injective, since it is `z ↦ 2z + a₁x + a₃`.

Stated over an opaque affine curve `W` rather than inlined at its one call site: the argument
below applies it to `pointedCurve.toAffine`, and keeping `W` a variable is what stops the
concrete universal curve's coefficients from being `whnf`-reduced. -/
private lemma eq_of_sub_negY_eq {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    (W : WeierstrassCurve.Affine F) {x z₁ z₂ : F}
    (h : z₁ - W.negY x z₁ = z₂ - W.negY x z₂) : z₁ = z₂ := by
  simp only [Affine.negY] at h
  have h2z : (2 : F) * z₁ = 2 * z₂ := by linear_combination h
  exact mul_left_cancel₀ h2 h2z

/-- **The affine coordinates of `n • (X, Y)` are `(smulX n, smulY n)`.** This is the theorem the
whole `smulX`/`smulY` calculus above was built for: the rational functions `φₙ/ψₙ²` and `ωₙ/ψₙ³`
really are the coordinates of the `n`-fold multiple of the distinguished point on the universal
curve, for every nonzero `n`. -/
-- Strong induction on `n > 0`, then `Int.negInduction` for the sign. Base cases `n = 1`, where
-- both sides are `(X, Y)`, and `n = 2`, the doubling `addX_smul_one_smul_one` /
-- `addY_smul_one_smul_one`. The step writes `(n + 1) • P` as `(n • P) + P` and matches
-- coordinates against Mathlib's chord formula: `smulX_add` against `addX_eq_addX_negY_sub`, and
-- `smulY_add_sub_negY` against `addY_sub_negY_addY` — the latter determines `smulY` only through
-- `z ↦ z - negY x z`, which `eq_of_sub_negY_eq` inverts.
theorem zsmul_point_eq_smulX_smulY : n ≠ 0 →
    ∃ h : Affine.Nonsingular pointedCurve.toAffine (smulX n) (smulY n),
      n • point = .some _ _ h := by
  induction n using Int.negInduction with
  | nat n =>
    refine n.strong_induction_on fun n ih h0 ↦ ?_
    obtain _ | _ | _ | n := n
    · exact (h0 rfl).elim
    · simp_rw [zero_add, Nat.cast_one, one_zsmul, smulX_one, smulY_one]
      exact ⟨Affine.equation_iff_nonsingular.mp equation_point, Affine.point_def⟩
    -- The `n = 1` instance, with its index cast normalised before the pair is destructured:
    -- afterwards `ns`'s type mentions the cast and no rewrite of `eq` alone is type-correct.
    all_goals obtain ⟨ns, eq⟩ :
        ∃ h : Affine.Nonsingular pointedCurve.toAffine (smulX 1) (smulY 1),
          (1 : ℤ) • point = .some _ _ h := ih 1 (by omega) one_ne_zero
    · rw [show ((0 + 1 + 1 : ℕ) : ℤ) = 2 by norm_num, ← addX_smul_one_smul_one,
        ← addY_smul_one_smul_one, show (2 : ℤ) = 1 + 1 by norm_num, add_zsmul, eq]
      exact ⟨Affine.nonsingular_add ns ns fun h ↦ smulY_ne_negY one_ne_zero h.2,
        Affine.Point.add_self_of_Y_ne (smulY_ne_negY one_ne_zero)⟩
    set n2 := n + 1 + 1 with hn2
    obtain ⟨ns2, eq2⟩ := ih n2 (by omega) (by omega)
    have ne : smulX n2 ≠ smulX 1 := smulX_ne_smulX (by omega) (by omega)
    obtain ⟨ns1, eq1⟩ := ih (n + 1) (by omega) (by omega)
    simp_rw [show ((n + 1 : ℕ) : ℤ) = (n2 : ℤ) + (-1 : ℤ) by omega, add_zsmul, neg_smul] at eq1
    rw [eq2, eq, Affine.Point.neg_some, Affine.Point.add_of_X_ne ne,
      Affine.Point.some.injEq] at eq1
    -- `_U` and `L` abbreviate the curve and the chord's slope; both appear a dozen times below.
    let _U := pointedCurve.toAffine
    let L := _U.slope (smulX n2) (smulX 1) (smulY n2) (smulY 1)
    have X_eq : smulX ((n2 : ℤ) + 1) = _U.addX (smulX n2) (smulX 1) L := by
      rw [smulX_add one_ne_zero (by omega) (by omega) (by omega),
        Affine.addX_eq_addX_negY_sub _ _ ne, sub_eq_add_neg (n2 : ℤ), ← eq1.1]
    have hfact₁ :=
      smulY_add_sub_negY (n := n2) (m := 1) one_ne_zero (by omega) (by omega) (by omega)
    have hfact₂ := _U.addY_sub_negY_addY (x₁ := smulX n2) (x₂ := smulX 1) (smulY n2) (smulY 1) ne
    have Y_eq : smulY ((n2 : ℤ) + 1) = _U.addY (smulX n2) (smulX 1) (smulY n2) L :=
      eq_of_sub_negY_eq two_ne_zero _U (x := _U.addX (smulX n2) (smulX 1) L) <| by
        -- `hfact₂` is stated through two `let`s, which `simp only` zeta-reduces away.
        simp only at hfact₂
        rw [X_eq] at hfact₁
        rw [hfact₁, hfact₂]
    rw [show ((n + 1 + 1 + 1 : ℕ) : ℤ) = (n2 : ℤ) + 1 by omega, X_eq, Y_eq, add_zsmul, eq, eq2]
    exact ⟨Affine.nonsingular_add ns2 ns fun h ↦ ne h.1, Affine.Point.add_of_X_ne ne⟩
  | neg ih n =>
    rw [neg_ne_zero]
    intro h0
    obtain ⟨ns, eq⟩ := ih n h0
    simp_rw [smulX_neg, smulY_neg h0, neg_smul, eq, Affine.Point.neg_some]
    exact ⟨(Affine.nonsingular_neg ..).mpr ns, trivial⟩

/-- **The distinguished point `(X, Y)` on the universal curve is not torsion.** Every nonzero
multiple of it has affine coordinates, so none of them is the point at infinity. -/
lemma zsmul_point_ne_zero (h0 : n ≠ 0) : n • point ≠ 0 := by
  obtain ⟨ns, eq⟩ := zsmul_point_eq_smulX_smulY h0
  rw [eq]
  exact Affine.Point.some_ne_zero ns

end WeierstrassCurve.Universal.Affine

namespace WeierstrassCurve.Universal.Jacobian

open WeierstrassCurve.Jacobian

variable {m n : ℤ}

/-- **No nonzero multiple of the distinguished point vanishes in Jacobian coordinates.** This is
`Affine.zsmul_point_ne_zero` moved along `Point.toAffineAddEquiv`, which is exactly how
`Jacobian.point` is defined from `Affine.point`. -/
lemma zsmul_point_ne_zero (h0 : n ≠ 0) : n • Jacobian.point ≠ 0 := by
  rw [Jacobian.point_def, ← Point.toAffineAddEquiv_symm_apply,
    ← map_zsmul (Point.toAffineAddEquiv _).symm, Ne,
    map_eq_zero_iff _ (Point.toAffineAddEquiv _).symm.injective]
  exact Universal.Affine.zsmul_point_ne_zero h0

/-- **The multiples of the distinguished point are pairwise distinct**: `n ↦ n • point` is
injective. Distinct integers therefore give distinct points, so the subgroup generated by the
distinguished point is a free abelian group of rank one — the point has infinite order. -/
-- Mathlib's `injective_zsmul_iff_not_isOfFinAddOrder`, with the non-torsion side supplied by
-- `zsmul_point_ne_zero` through `isOfFinAddOrder_iff_zsmul_eq_zero`.
lemma zsmul_point_injective : Function.Injective fun n : ℤ ↦ n • Jacobian.point :=
  injective_zsmul_iff_not_isOfFinAddOrder.mpr fun h ↦
    let ⟨_k, hk, hz⟩ := isOfFinAddOrder_iff_zsmul_eq_zero.mp h
    zsmul_point_ne_zero hk hz

/-- The three families of universal division polynomials as a 3-tuple. -/
abbrev smulPoly (n : ℤ) : Fin 3 → Poly := ![curve.φ n, curve.ω n, curve.ψ n]

/-- The three families of division polynomials as elements of the universal ring. -/
abbrev smulRing (n : ℤ) : Fin 3 → Universal.Ring := AdjoinRoot.mk _ ∘ smulPoly n

/-- The three families of division polynomials as elements of the universal field. -/
abbrev smulField (n : ℤ) : Fin 3 → Universal.Field := polyToField ∘ smulPoly n

/-- **The `Z` coordinate of `smulField n` is `ψₙ`.** The third component of the universal-field
triple is the division polynomial itself, carried across by `polyToField`, with no
denominator. -/
-- `smulField` is `polyToField ∘ ![φ, ω, ψ]`, so this is `comp_fin3` followed by the third
-- component of `fin3_def_ext` — a rewrite route for a projection that would otherwise be
-- discharged by definitional reduction.
lemma smulField_Z (n : ℤ) : smulField n (2 : Fin 3) = polyToField (curve.ψ n) := by
  rw [smulField, comp_fin3]
  exact (fin3_def_ext ..).2.2

/-- `smulField` is `smulRing` pushed into the field of fractions, coordinate by coordinate. -/
@[simp]
lemma algebraMap_comp_smulRing (n : ℤ) : algebraMap _ _ ∘ smulRing n = smulField n := by
  -- Not `rfl`: `polyToField`'s body is unexposed, so its factorisation through `AdjoinRoot.mk`
  -- has to come from the equation lemma.
  ext i
  fin_cases i <;> simp [Function.comp_def, polyToField_apply]

/-- **The Jacobian coordinates of `n • (X, Y)` are `(φₙ : ωₙ : ψₙ)`.** The Jacobian form of
`Affine.zsmul_point_eq_smulX_smulY`: where the affine statement divides by `ψₙ²` and `ψₙ³`, the
Jacobian one carries `ψₙ` as the third coordinate and holds for `n = 0` as well, the triple
becoming `(1 : 1 : 0)`, the point at infinity.

For `n ≠ 0` the two triples differ by the scalar `ψₙ⁻¹`, which is what `Quotient.sound` needs:
Jacobian coordinates scale as `(u²x, u³y, uz)`, and those are precisely the powers by which
`smulX` and `smulY` divide. -/
-- Not `@[simp]`: `Jacobian.point_def` and `Affine.point_def` are both `@[simp]`, so they rewrite
-- `Jacobian.point` inside this left-hand side, so simpNF rejects the tag.
theorem zsmul_point_eq_smulField : (n • Jacobian.point).point = ⟦smulField n⟧ := by
  rw [← fin3_def (smulField n)]
  simp_rw [smulField, smulPoly, Function.comp_def, fin3_def_ext]
  obtain rfl | hn := eq_or_ne n 0
  · simp_rw [zero_zsmul, φ_zero, ω_zero, ψ_zero, map_zero, map_one]
    rfl
  obtain ⟨ns, eq⟩ := Universal.Affine.zsmul_point_eq_smulX_smulY hn
  rw [Jacobian.point_def, ← Point.toAffineAddEquiv_symm_apply,
    ← map_zsmul (Point.toAffineAddEquiv _).symm, eq]
  have hψ : polyToField (curve.ψ n) ≠ 0 := polyToField_ψ_ne_zero hn
  refine Quotient.sound ⟨.mk0 _ (inv_ne_zero hψ), ?_⟩
  simp_rw [Units.smul_def, smul_fin3]
  ext i
  -- `polyToField_apply` is `@[simp]` here; letting it fire would shatter `polyToField (ψ n)`
  -- into `algebraMap _ _ (AdjoinRoot.mk _ _)` and turn `hψ` into a divisibility side goal.
  fin_cases i <;>
    simp [-polyToField_apply, Universal.Affine.smulX_def, Universal.Affine.smulY_def, hψ,
      inv_mul_eq_div]

/-- `smulPoly` at `0` is the triple `(1, 1, 0)`. -/
@[simp] lemma smulPoly_zero : smulPoly 0 = ![1, 1, 0] := by simp [smulPoly]

/-- `smulRing` at `0` is the triple `(1, 1, 0)`, the universal-ring representation of the point
at infinity. -/
@[simp] lemma smulRing_zero : smulRing 0 = ![1, 1, 0] := by
  simp [smulRing, smulPoly_zero, comp_fin3]

/-- `smulField` at `0` is the triple `(1 : 1 : 0)`, the point at infinity. -/
@[simp] lemma smulField_zero : smulField 0 = ![1, 1, 0] := by
  simp [smulField, smulPoly_zero, comp_fin3]

/-- **The `Z`-coordinate of Mathlib's Jacobian doubling formula at `(φₙ, ωₙ, ψₙ)` is `ψ₂ₙ`** —
already in the polynomial ring, with no reduction modulo the Weierstrass polynomial. -/
-- `dblZ` is `Z * (Y - negY)`, which at this triple is `ψₙ * (2ωₙ + a₁φₙψₙ + a₃ψₙ³)`; `ω_spec`
-- names the second factor `ψc n` and `ψ_mul_ψc` multiplies the two into `ψ₂ₙ`. `ω_spec` is stated
-- with `CC curve.aᵢ` and `negY_eq` produces `curvePoly.aᵢ`; the two agree definitionally, so the
-- certificate is taken at the ascribed type rather than rewritten across.
lemma dblZ_smulPoly : dblZ curvePoly (smulPoly n) = curve.ψ (2 * n) := by
  have key : 2 * curve.ω n + curvePoly.a₁ * curve.φ n * curve.ψ n
      + curvePoly.a₃ * curve.ψ n ^ 3 = curve.ψc n := curve.ω_spec n
  rw [← ψ_mul_ψc, ← key]
  simp only [dblZ, smulPoly, negY_eq, fin3_def_ext]
  ring

/-- The triple `(φₙ : ωₙ : ψₙ)` is a nonsingular Jacobian point representative of the universal
curve, for every `n` — it represents `n • (X, Y)`, which is a point of the curve. -/
lemma nonsingular_smulField : Nonsingular pointedCurve (smulField n) := by
  rw [← nonsingularLift_iff]
  simpa only [zsmul_point_eq_smulField] using (n • Jacobian.point).nonsingular

/-- **Mathlib's Jacobian doubling formula sends `(φₙ : ωₙ : ψₙ)` to `(φ₂ₙ : ω₂ₙ : ψ₂ₙ)`**, as an
equality of triples and not merely of the points they represent. -/
-- At `n = 0` the triple is `(1, 1, 0)` and `dblXYZ_of_Z_eq_zero` applies. Otherwise both sides
-- have `Z`-coordinate `ψ₂ₙ ≠ 0` (`dblZ_smulPoly`), so `equiv_iff_eq_of_Z_eq` upgrades an equality
-- of point classes to one of triples, and the two classes agree because both represent
-- `(2 * n) • (X, Y)`.
lemma dblXYZ_smulField : dblXYZ pointedCurve (smulField n) = smulField (2 * n) := by
  obtain rfl | hn := eq_or_ne n 0
  · rw [mul_zero, dblXYZ_of_Z_eq_zero nonsingular_smulField.1 (by simp), smulField_zero]
    simp
  refine (equiv_iff_eq_of_Z_eq ?_ (polyToField_ψ_ne_zero (mul_ne_zero two_ne_zero hn))).mp
    (Quotient.exact ?_)
  -- `equiv_iff_eq_of_Z_eq` compares two `Z` components; `dblXYZ_Z` rewrites the left one and
  -- `smulField_Z` the right.
  · rw [dblXYZ_Z, smulField_Z, ← dblZ_smulPoly, ← map_dblZ polyToField (smulPoly n)]
    simp only [map_polyToField]
  · have h2 : ((2 : ℤ) • (n • Jacobian.point)).point = ⟦dblXYZ pointedCurve (smulField n)⟧ := by
      rw [two_zsmul, Point.add_point, zsmul_point_eq_smulField, addMap_eq, add_self]
    exact h2.symm.trans <|
      (congrArg Point.point (mul_zsmul Jacobian.point 2 n).symm).trans zsmul_point_eq_smulField

/-- The doubling identity over the universal **ring**, where it is a statement about polynomials
modulo the Weierstrass polynomial rather than about rational functions. -/
-- `Universal.Ring` embeds in `Universal.Field`, so the field statement implies this one; the two
-- sides are compared coordinatewise through `Function.Injective.comp_left`.
lemma dblXYZ_smulRing : dblXYZ curveRing (smulRing n) = smulRing (2 * n) := by
  refine (IsFractionRing.injective Universal.Ring Universal.Field).comp_left ?_
  beta_reduce
  rw [← map_dblXYZ]
  simp only [algebraMap_comp_smulRing]
  exact dblXYZ_smulField

/-- **The `Z`-coordinate of Mathlib's Jacobian addition formula at `(φₘ, ωₘ, ψₘ)` and
`(φₙ, ωₙ, ψₙ)` is `ψₙ₊ₘψₙ₋ₘ`**, again already in the polynomial ring. -/
-- The certificate is the elliptic-sequence relation of the universal `ψ` family at `(n, m, 1)`.
-- `linear_combination` is unavailable over `Poly`: instance search gives up on the triple-nested
-- `(MvPolynomial Coeff ℤ)[X][Y]` and reports no `IsRightCancelAdd`, so the certificate is
-- discharged through `sub_eq_zero` and `ring` instead.
lemma addZ_smulPoly : addZ (smulPoly m) (smulPoly n) = curve.ψ (n + m) * curve.ψ (n - m) := by
  have key := curve.isEllipticNet_ψ.isEllipticSequence n m 1
  simp only [IsEllipticNet.rel, add_zero, ψ_one, mul_one] at key
  symm
  rw [← sub_eq_zero, ← key, addZ]
  simp only [smulPoly, fin3_def_ext, WeierstrassCurve.φ]
  ring

/-- **Negating the index negates the point**: the triple at `-n` is Mathlib's Jacobian negation of
the triple at `n`, rescaled by `-1`. -/
-- Coordinatewise, so that each coordinate's rule is visible: `φ_neg`, `ω_neg` and `ψ_neg`. The
-- `(-1)ᵏ` factors are cleared by `ring` rather than `simp`, because instance search finds no
-- `HasDistribNeg Poly` and the sign simp set therefore does not fire here.
@[simp] lemma smulPoly_neg : smulPoly (-n) = (-1 : Poly) • neg curvePoly (smulPoly n) := by
  -- `fin_cases` leaves the index as `⟨i, ⋯⟩` rather than the numeral, which `simp only` with
  -- explicit `Matrix.cons_val_*` lemmas cannot match; the default `simp` set can, via the
  -- `Fin.reduceFinMk` simproc, after which the tuple projections and `ring` finish all three.
  funext i
  fin_cases i <;> simp [smulPoly, smul_fin3, neg, negY, φ_neg, ψ_neg] <;> ring

/-- The negation rule over the universal ring. -/
@[simp] lemma smulRing_neg :
    smulRing (-n) = (-1 : Universal.Ring) • neg curveRing (smulRing n) := by
  simp_rw [smulRing, smulPoly_neg, comp_smul, ← WeierstrassCurve.Jacobian.map_neg, map_neg,
    map_one]
  rfl

/-- The negation rule over the universal field. -/
-- Obtained from `smulRing_neg` rather than from `smulPoly_neg` directly: `algebraMap_comp_smulRing`
-- lands the composite on `smulField` on the nose, where routing through `polyToField` would leave
-- a `curvePoly.map polyToField` to discharge.
@[simp] lemma smulField_neg :
    smulField (-n) = (-1 : Universal.Field) • neg pointedCurve (smulField n) := by
  rw [← algebraMap_comp_smulRing, smulRing_neg, comp_smul, ← WeierstrassCurve.Jacobian.map_neg,
    algebraMap_comp_smulRing, map_neg, map_one]
  rfl

/-- **Mathlib's Jacobian addition formula at `(φₘ : ωₘ : ψₘ)` and `(φₙ : ωₙ : ψₙ)` returns
`(φₙ₊ₘ : ωₙ₊ₘ : ψₙ₊ₘ)`, scaled by `ψₙ₋ₘ`.** The scaling is genuine: `addXYZ` is homogeneous, and
the representative it produces is the canonical triple only up to that factor. -/
-- Three cases. At `m = n` the formula degenerates to `(0, 0, 0)` and so does the right-hand side,
-- since `ψ₀ = 0`. At `n = -m` the second triple is the negation of the first, so `addXYZ_neg`
-- applies and both sides are the point at infinity scaled by `ψ₂ₘ`. Otherwise both sides have
-- `Z`-coordinate `ψₙ₊ₘψₙ₋ₘ ≠ 0` and represent `(n + m) • (X, Y)`, exactly as in `dblXYZ_smulField`.
lemma addXYZ_smulField :
    addXYZ pointedCurve (smulField m) (smulField n) =
      polyToField (curve.ψ (n - m)) • smulField (n + m) := by
  obtain rfl | h := eq_or_ne m n
  · rw [sub_self, ψ_zero, map_zero, addXYZ_self nonsingular_smulField.1, smul_fin3]
    simp
  obtain rfl | ne_neg := eq_or_ne n (-m)
  · rw [← one_smul Universal.Field (smulField m), smulField_neg, neg_add_cancel, addXYZ_smul,
      one_mul, neg_one_sq, addXYZ_neg nonsingular_smulField.1, one_smul,
      show (-m - m : ℤ) = -(2 * m) by ring, ψ_neg, map_neg polyToField, ← dblZ_smulPoly,
      ← map_dblZ polyToField (smulPoly m), smulField_zero]
    simp only [map_polyToField]
  refine (equiv_iff_eq_of_Z_eq ?_ ?_).mp (Quotient.exact ?_)
  -- Same shape as `dblXYZ_smulField`, with a scaled right-hand side. Mathlib's Jacobian action is
  -- *weighted* — `smul_fin3 : u • P = ![u ^ 2 * P x, u ^ 3 * P y, u * P z]` — so the `Z` component
  -- takes a single factor of `u`, which is the third component of `smul_fin3_ext`.
  · rw [addXYZ_Z,
      (smul_fin3_ext (smulField (n + m)) (polyToField (curve.ψ (n - m)))).2.2, smulField_Z]
    have hF := congrArg polyToField (addZ_smulPoly (m := m) (n := n))
    simp only [addZ, smulPoly, smulField, Function.comp_def, fin3_def_ext, map_sub polyToField,
      map_mul polyToField, map_pow polyToField] at hF ⊢
    linear_combination hF
  -- The nonvanishing side-goal is that same scaled projection, rewritten the same way.
  · rw [(smul_fin3_ext (smulField (n + m)) (polyToField (curve.ψ (n - m)))).2.2, smulField_Z]
    exact mul_ne_zero (polyToField_ψ_ne_zero (by omega)) (polyToField_ψ_ne_zero (by omega))
  · have hne : ¬ smulField m ≈ smulField n := fun hequiv ↦ h <| zsmul_point_injective <|
      Point.ext_iff.mpr <| by
        rw [zsmul_point_eq_smulField, zsmul_point_eq_smulField]
        exact Quotient.sound hequiv
    have hadd : (m • Jacobian.point + n • Jacobian.point).point
        = ⟦addXYZ pointedCurve (smulField m) (smulField n)⟧ := by
      rw [Point.add_point, zsmul_point_eq_smulField, zsmul_point_eq_smulField, addMap_eq,
        add_of_not_equiv hne]
    rw [smul_eq _ (polyToField_ψ_ne_zero (sub_ne_zero_of_ne h.symm)).isUnit,
      ← zsmul_point_eq_smulField, add_comm, add_zsmul, hadd]

/-- **The addition identity over the universal ring.** `addXYZ` carries the triples at `m` and `n`
to the triple at `n + m`, scaled by `ψₙ₋ₘ`: an equality in `Universal.Ring`, not merely of the
points the triples represent. The scaling factor is genuine — `addXYZ` is homogeneous, so the
representative it returns is the canonical triple only up to that factor. -/
-- By the same fraction-field injection as `dblXYZ_smulRing`.
lemma addXYZ_smulRing :
    addXYZ curveRing (smulRing m) (smulRing n) =
      AdjoinRoot.mk curve.polynomial (curve.ψ (n - m)) • smulRing (n + m) := by
  refine (IsFractionRing.injective Universal.Ring Universal.Field).comp_left ?_
  beta_reduce
  rw [← map_addXYZ, comp_smul, ← polyToField_apply]
  simp only [algebraMap_comp_smulRing]
  exact addXYZ_smulField

end WeierstrassCurve.Universal.Jacobian

namespace WeierstrassCurve

open Universal WeierstrassCurve.Jacobian

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x y : R}

variable (x y) in
/-- The division polynomials of `W` evaluated at a point `(x, y)`, as a Jacobian triple
`(φₙ(x,y), ωₙ(x,y), ψₙ(x,y))`. The definition needs only a commutative ring. **Over a field**, and
for a nonsingular `(x, y)`, these are the Jacobian coordinates of `n • (x, y)` — that reading is
`zsmul_point_eq_smulEval` below, which assumes `[Field F]`, and it is not claimed over a
general `R`. -/
abbrev smulEval (n : ℤ) : Fin 3 → R := evalEval x y ∘ ![W.φ n, W.ω n, W.ψ n]

/-- `smulEval` at `0` is `(1, 1, 0)`, the Jacobian triple of the point at infinity. -/
@[simp] lemma smulEval_zero : smulEval W x y 0 = ![1, 1, 0] := by
  simp [smulEval, comp_fin3, evalEval]

/-- `smulEval` at `1` is `(x, y, 1)`: the point `(x, y)` itself, in Jacobian coordinates. -/
@[simp] lemma smulEval_one : smulEval W x y 1 = ![x, y, 1] := by
  simp [smulEval, comp_fin3, evalEval]

variable {W} (eqn : Affine.Equation W x y)

namespace Universal

/-- **`smulEval` is the specialization of `smulRing`**: the universal triple `(φₙ, ωₙ, ψₙ)`,
pushed along the homomorphism a point of `W` induces, is that point's evaluated triple. This is
what turns each identity over `curveRing` into the same identity for `W` at `(x, y)`. -/
@[simp] lemma ringEval_comp_smulRing (n : ℤ) :
    ringEval eqn ∘ Jacobian.smulRing n = smulEval W x y n := by
  -- Coordinatewise, each coordinate being `ringEval_mk` followed by the matching `evalEval_*`.
  -- `fin_cases` leaves the index as `⟨i, ⋯⟩` rather than a numeral, so `simp only` with explicit
  -- `Matrix.cons_val_*` lemmas cannot match it; the default `simp` set reduces it through the
  -- `Fin.reduceFinMk` simproc, and the three coordinates then close uniformly.
  funext i
  fin_cases i <;> simp [Jacobian.smulRing, smulEval, ringEval_mk, evalEval_φ, evalEval_ω,
    evalEval_ψ]

end Universal

/-- **`smulEval` at `-n`**: negating the index negates the triple, in the same `(-1) • neg` form
as `smulPoly_neg`, `smulRing_neg` and `smulField_neg`. This is an identity of polynomial
evaluations and needs no equation on `(x, y)`. -/
@[simp] lemma smulEval_neg (n : ℤ) :
    smulEval W x y (-n) = (-1 : R) • Jacobian.neg W (smulEval W x y n) := by
  funext i
  fin_cases i <;> (simp [smulEval, smul_fin3, Jacobian.neg, Jacobian.negY, φ_neg, ψ_neg]; try ring)

include eqn in
/-- **The doubling formula for a concrete curve**: `dblXYZ_smulRing` specialized along the point
`(x, y)` of `W`. -/
lemma dblXYZ_smulEval (n : ℤ) : dblXYZ W (smulEval W x y n) = smulEval W x y (2 * n) := by
  simp_rw [← Universal.ringEval_comp_smulRing eqn, ← Jacobian.dblXYZ_smulRing, ← map_dblXYZ,
    map_ringEval]

include eqn in
/-- **The addition formula for a concrete curve**: `addXYZ_smulRing` specialized along `(x, y)`,
scaling factor and all. -/
lemma addXYZ_smulEval (m n : ℤ) :
    addXYZ W (smulEval W x y m) (smulEval W x y n) =
      evalEval x y (W.ψ (n - m)) • smulEval W x y (n + m) := by
  -- The scaling factor is a bare `ψ`, not a triple, so it needs the third coordinate of
  -- `ringEval_comp_smulRing` on its own — `congr_fun … 2` is that projection. Kept as a local
  -- `have` rather than a named lemma: this is its only use.
  have hψ : ∀ k : ℤ, Universal.ringEval eqn (AdjoinRoot.mk _ (curve.ψ k)) = evalEval x y (W.ψ k) :=
    fun k ↦ congr_fun (Universal.ringEval_comp_smulRing eqn k) 2
  simp_rw [← Universal.ringEval_comp_smulRing eqn, ← hψ]
  rw [← comp_smul, ← Jacobian.addXYZ_smulRing, ← map_addXYZ]
  simp_rw [map_ringEval]

end WeierstrassCurve

namespace WeierstrassCurve

open Universal WeierstrassCurve.Jacobian

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

/-- **The integer multiples of a nonsingular rational point are given by the division
polynomials.** For every `n`, the Jacobian coordinates of `n • (x, y)` on a Weierstrass curve over
a field are `(φₙ(x,y) : ωₙ(x,y) : ψₙ(x,y))`.

Stated for a nonsingular `(x, y)` on a curve over a field, with no hypothesis on `n` and none on
the characteristic. -/
-- This is the theorem the whole universal development exists to prove, and it holds that
-- generally because its ingredients do: the doubling, addition and negation identities the
-- induction consumes are equalities in the universal coordinate ring `Universal.Ring` —
-- polynomials in `A₁,⋯,A₆,X,Y` taken modulo the Weierstrass polynomial — and specialize along
-- `ringEval` to any point on any curve. Only the third coordinates (`dblZ_smulPoly`,
-- `addZ_smulPoly`) and the negation rule `smulPoly_neg` hold already over `Poly`, before that
-- quotient. The theorem is an induction over those identities, not a specialization of one.
-- Even-odd strong induction on `n ≥ 0`, then `Int.negInduction` for the sign. The base cases
-- `n = 0` and `n = 1` are `(1 : 1 : 0)` and `(x : y : 1)`. The even step writes `2 * (m + 1) • P`
-- through Mathlib's `add_self` and `dblXYZ_smulEval`; the odd step writes
-- `(m + 1) • P + (m + 2) • P` through `add_of_not_equiv` and `addXYZ_smulEval`. The two
-- summands are distinct because their difference is `P`, which is a nonzero affine point — not
-- because `P` is non-torsion, which this theorem does not assume. The negative case rescales by
-- `-1`, which is `smulRing_neg` specialized along the point.
theorem zsmul_point_eq_smulEval {x y : F} (h : Affine.Nonsingular W x y) (n : ℤ) :
    (n • Point.fromAffine (Affine.Point.some _ _ h)).point = ⟦smulEval W x y n⟧ := by
  induction n using Int.negInduction with
  | nat n =>
    refine n.strong_induction_on fun n ih ↦ ?_
    obtain _ | _ | n := n
    · rw [Nat.cast_zero, zero_smul, smulEval_zero]
      rfl
    · rw [Nat.cast_one, one_smul, smulEval_one]
      rfl
    obtain ⟨n, rfl | rfl⟩ := n.even_or_odd'
    · rw [show (2 * n + 1 + 1 : ℕ) = 2 * (n + 1) by omega, Nat.cast_mul, mul_smul, natCast_zsmul,
        two_nsmul, Point.add_point, ih _ (by omega), addMap_eq, add_self, dblXYZ_smulEval h.1]
      rfl
    · rw [show 2 * n + 1 + 1 + 1 = (n + 1) + (n + 1 + 1) by omega, Nat.cast_add, add_smul]
      have hne : (↑(n + 1) : ℤ) • Point.fromAffine (Affine.Point.some _ _ h) ≠
          (↑(n + 1 + 1) : ℤ) • Point.fromAffine (Affine.Point.some _ _ h) := by
        rw [ne_comm, ← sub_ne_zero, ← sub_smul]
        push_cast
        simp only [add_sub_cancel_left, one_smul]
        exact Point.fromAffine_some_ne_zero h
      have hnequiv : ¬ (smulEval W x y ↑(n + 1) ≈ smulEval W x y ↑(n + 1 + 1)) := by
        intro hequiv
        refine hne (Point.ext_iff.mpr ?_)
        rw [ih (n + 1) (by omega), ih (n + 1 + 1) (by omega)]
        exact Quotient.sound hequiv
      have hcast : ((n + 1 + 1 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
      -- `addXYZ_smulEval` at the adjacent indices scales by `ψ` of the gap, which is `ψ 1 = 1`;
      -- the three rewrites after it discharge that factor.
      rw [Point.add_point, ih (n + 1) (by omega), ih (n + 1 + 1) (by omega), addMap_eq,
        add_of_not_equiv hnequiv, hcast, addXYZ_smulEval h.1, add_sub_cancel_left,
        WeierstrassCurve.ψ_one, Polynomial.evalEval_one, one_smul]
      congrm(⟦W.smulEval x y ?_⟧)
      ring
  | neg ih n =>
    simp_rw [_root_.neg_smul, Point.neg_point, ih n, eq_comm]
    refine Quotient.sound ⟨-1, ?_⟩
    simp_rw [smulEval_neg]
    rfl

/-- If `ψ₂` vanishes at `(x, y)` then `2 • P = 0`: the point equals its own negation, so adding
it to itself lands at infinity. Field-local — no base ring is involved.

Stated for the Jacobian point, matching the rest of the torsion API and
`evalEval_ψ_eq_zero_of_zsmul_eq_zero`. The affine group law is defined by cases and so needs
`DecidableEq`, but only inside the proof, where `classical` supplies it; the statement does not. -/
theorem two_zsmul_eq_zero_of_evalEval_ψ₂_eq_zero {x y : F}
    (hns : W.toAffine.Nonsingular x y) (hψ : W.ψ₂.evalEval x y = 0) :
    (2 : ℤ) • Jacobian.Point.fromAffine (Affine.Point.some _ _ hns) = 0 := by
  classical
  rw [WeierstrassCurve.ψ₂, Affine.evalEval_polynomialY] at hψ
  have hy : y = W.toAffine.negY x y := by simp only [Affine.negY]; linear_combination hψ
  have haff : (2 : ℕ) • (Affine.Point.some _ _ hns) = 0 := by
    rw [two_nsmul]; exact Affine.Point.add_self_of_Y_eq hy
  have h := congrArg (Jacobian.Point.toAffineAddEquiv W).symm haff
  rw [map_nsmul, map_zero] at h
  rw [← natCast_zsmul] at h
  exact_mod_cast h

/-- **A torsion point is a root of its division polynomial.** If `n • P = 0` in the Jacobian
point group, then `ψₙ` vanishes at `P`.

This is where `zsmul_point_eq_smulEval` is consumed: it identifies `n • P` with the class of
`(φₙ(x,y) : ωₙ(x,y) : ψₙ(x,y))`, and a Jacobian class is the point at infinity exactly when its
`Z`-coordinate vanishes. -/
theorem evalEval_ψ_eq_zero_of_zsmul_eq_zero {x y : F}
    (hns : W.toAffine.Nonsingular x y) (n : ℤ)
    (htors : n • (Jacobian.Point.fromAffine (Affine.Point.some _ _ hns)) = 0) :
    (W.ψ n).evalEval x y = 0 := by
  have heval := zsmul_point_eq_smulEval W hns n
  have hzero := Jacobian.Point.zero_point (W' := W.toJacobian)
  rw [Jacobian.Point.ext_iff] at htors
  rw [heval, hzero] at htors
  exact (Jacobian.Z_eq_zero_of_equiv (Quotient.exact htors)).mpr rfl

end WeierstrassCurve

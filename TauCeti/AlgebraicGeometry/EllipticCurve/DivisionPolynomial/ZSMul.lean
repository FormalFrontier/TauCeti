/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Universal

/-!
# Coordinates of scalar multiplication on the universal curve

The Nagell–Lutz route expresses `n • (X, Y)` on the universal curve through the division
polynomials: the affine `X`-coordinate is `φₙ/ψₙ²` and the `Y`-coordinate is `ωₙ/ψₙ³`, as
elements of `Universal.Field`. This file defines those two rational functions, `smulX` and
`smulY` — the identification with `n • point` itself is proved in the scalar-multiplication
development, not here — and develops the `smulX` calculus that identification consumes: values
at `0`, `1` and `2`, the offset `ψₙ₊₁ψₙ₋₁/ψₙ²` from the `X`-coordinate, evenness in `n`,
nonvanishing, the difference `smulX m - smulX n` as a single quotient, and the separation
statement `smulX m = smulX n ↔ m = n ∨ m = -n`. `smulY`'s own sign rule is here too: negating
a nonzero index negates the point, so `smulY (-n)` is the `negY` of `(smulX n, smulY n)`.

The second half of the file turns that calculus on the pair `(smulX 1, smulY 1)`, which is the
distinguished point `(X, Y)` itself. The vertical gap `smulY n - negY (smulX n) (smulY n)` is
`ψ₂ₙ/ψₙ⁴`, hence nonzero, so `smulY n` never equals the `negY` of its own pair; at `n = 1` the gap
is `ψ₂`, which selects the tangent branch of Mathlib's `Affine.slope` and gives the tangent slope
`slopeOne` the closed form `-Wₓ/ψ₂`. Feeding that slope to Mathlib's affine addition formula sends
`(smulX 1, smulY 1)` to `(smulX 2, smulY 2)`: `addX … = smulX 2` and `addY … = smulY 2`.

## Main definitions

* `WeierstrassCurve.Universal.Affine.smulX`: the rational function `φₙ/ψₙ²`.
* `WeierstrassCurve.Universal.Affine.smulY`: the rational function `ωₙ/ψₙ³`.
* `WeierstrassCurve.Universal.Affine.slopeOne`: the slope of the tangent at `(X, Y)`.

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
  is `ψ₂ₙ/ψₙ⁴`, whence `smulY_ne_negY` — the gap never vanishes for `n ≠ 0` — and its `n = 1` case
  `smulY_one_ne_negY`.
* `WeierstrassCurve.Universal.Affine.slopeOne_eq_neg_div`: the tangent slope at `(X, Y)` is
  `-Wₓ/ψ₂`, the ratio of the two partial derivatives of the Weierstrass polynomial.
* `WeierstrassCurve.Universal.Affine.addX_smul_one_smul_one`,
  `.addY_smul_one_smul_one`: doubling `(X, Y)` along that tangent with Mathlib's affine addition
  formula returns `(smulX 2, smulY 2)` — the base case of the scalar-multiplication induction.

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
`smulY_one_sub_negY` (`:233`), `smulY_one_ne_negY` (`:237`), `slopeOne` (`:241`),
`slopeOne_eq_neg_div` (`:244`), `addX_smul_one_smul_one` (`:261`) and `addY_smul_one_smul_one`
(`:277`), with the same `ψᵤ` respelling and one added equation lemma, `slopeOne_def`.

One statement is generalised rather than transcribed. The source proves only `smulY_one_ne_negY`
(`:237`); here `smulY_ne_negY` states it for every `n ≠ 0`, which `smulY_sub_negY` already gives —
the gap `ψ₂ₙ/ψₙ⁴` is a quotient of nonzero elements — and the source's statement is recovered as
the `n = 1` case.

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

Two further departures. Mathlib's `Affine.slope` is defined by cases and `Universal.Field` carries
no `DecidableEq`; the source supplies one with a namespace-wide
`attribute [local instance] Classical.propDecidable`, narrowed here to `open scoped Classical in`
on `slopeOne` and `slopeOne_def`, the only two declarations whose statements mention `slope`.
And the map-direction problem recorded above for `smulX_eq` recurs at every proof in the block.
Measured against the `unusedSimpArgs` linter at this pin: bare `map_sub` and `map_neg` fire at no
site, while bare `map_mul`, `map_add`, `map_pow` and `map_ofNat` fire at all of them — the
unexposed instances are `Sub` and `Neg`. Each `map_*` names its hom regardless, for uniformity
with the rest of the file. Naming alone is not enough in the last three proofs, which state their
polynomial-level certificate as a `have` and map it with `congrArg polyToField`, the shape
`smulX_eq` uses: `polyToField_apply` is `@[simp]` here, so `field_simp` shatters
`polyToField (C X)` into `algebraMap _ _ (AdjoinRoot.of _ X)` while leaving
`polyToField curve.polynomialX` folded, and the two sides of the goal then share no atoms.

`smulX_sub_sub_smulX_add` (`:196`) is still deliberately not ported: its only consumer at the pin
is `smulX_add` (`:300`), the addition formula for two distinct multiples, which ships with a later
slice.
-/

public section

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Universal.Affine

variable {m n : ℤ}

/-- The rational function `φₙ/ψₙ²` in the universal field, which the scalar-multiplication
development identifies as the affine `X`-coordinate of `n • (X, Y)` on the universal curve —
that identification is proved there, not here. -/
def smulX (n : ℤ) : Universal.Field :=
  polyToField (curve.φ n) / polyToField (curve.ψ n) ^ 2

/-- The rational function `ωₙ/ψₙ³` in the universal field, which the scalar-multiplication
development identifies as the affine `Y`-coordinate of `n • (X, Y)` on the universal curve —
that identification is proved there, not here. -/
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
  have key := isEllipticSequence_polyToField_ψ n m 1
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

/-- The gap at the distinguished point itself is `ψ₂`: at `n = 1` the numerator `ψ₂ₙ` is `ψ₂` and
the denominator `ψₙ⁴` is `1`. -/
lemma smulY_one_sub_negY :
    smulY 1 - pointedCurve.toAffine.negY (smulX 1) (smulY 1) = polyToField (curve.ψ 2) := by
  rw [smulY_sub_negY one_ne_zero, mul_one, ψ_one, map_one, one_pow, div_one]

/-- **`smulY n` never equals the `negY` of its own pair, for `n ≠ 0`.** The gap computed above is
`ψ₂ₙ/ψₙ⁴`, a quotient of nonzero elements. -/
lemma smulY_ne_negY (h0 : n ≠ 0) :
    smulY n ≠ pointedCurve.toAffine.negY (smulX n) (smulY n) := by
  rw [← sub_ne_zero, smulY_sub_negY h0]
  exact div_ne_zero (polyToField_ψ_ne_zero (by omega))
    (pow_ne_zero _ (polyToField_ψ_ne_zero h0))

/-- **The `n = 1` case**, at the distinguished point itself: this is what selects the tangent
branch of `Affine.slope` in `slopeOne_eq_neg_div`. -/
lemma smulY_one_ne_negY : smulY 1 ≠ pointedCurve.toAffine.negY (smulX 1) (smulY 1) :=
  smulY_ne_negY one_ne_zero

open scoped Classical in
/-- The slope of the tangent line to `pointedCurve` at its distinguished point `(X, Y)`: Mathlib's
`Affine.slope` at the coincident pair `(X, Y), (X, Y)`. `Universal.Field` carries no `DecidableEq`
instance and `Affine.slope` is defined by cases, hence the classical one. -/
def slopeOne : Universal.Field :=
  pointedCurve.toAffine.slope (smulX 1) (smulX 1) (smulY 1) (smulY 1)

open scoped Classical in
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
  rw [slopeOne_def, Affine.slope_of_Y_ne rfl smulY_one_ne_negY, smulY_one_sub_negY, h,
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
doubling step the later identification of `n • (X, Y)` runs through — that identification itself
is proved in the scalar-multiplication development, not here. -/
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

end WeierstrassCurve.Universal.Affine

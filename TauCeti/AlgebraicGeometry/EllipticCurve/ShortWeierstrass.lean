/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms

/-!
# The short Weierstrass curve `y² = x³ + Ax + B`

Mathlib carries short Weierstrass form as a *predicate*, `WeierstrassCurve.IsShortNF`, asserting
`a₁ = a₂ = a₃ = 0` of a curve one already has, together with the invariants that follow from it
(`Δ_of_isShortNF`, `j_of_isShortNF`, and the `b`- and `c`-families). What it does not carry is the
*constructor*: the curve built from a chosen pair of coefficients. Statements phrased over an
explicit `y² = x³ + Ax + B` — the classical form of the Nagell–Lutz theorem among them — need that
constructor, so it is supplied here, with the `IsShortNF` instance that connects it to everything
Mathlib already proves.

All five coefficients are stated as `@[simp]` lemmas, in the `Zero` section. They are not
redundant with Mathlib's `a₁_of_isShortNF` family: that family needs the `IsShortNF` instance,
which needs `CommRing`, so at `Zero R` generality it is unavailable and `simp` cannot otherwise
reduce a projection of the opaque constructor. Every other fact about `shortCurve` — the `b`- and
`c`-invariants, `Δ` and `j` — is inherited through the instance rather than restated.

## Main definitions

* `WeierstrassCurve.shortCurve`: the curve `y² = x³ + Ax + B`, over any `Zero`.

## Main results

* `WeierstrassCurve.instIsShortNFShortCurve`: it is in short normal form, which is what
  makes Mathlib's `*_of_isShortNF` family apply to it.
* `WeierstrassCurve.map_shortCurve`: short form is preserved by a ring hom, and the
  coefficients transport. Mathlib has no `IsShortNF`-under-`map` instance, so this is what lets a
  curve over `ℤ` be base changed to `ℚ` and stay recognisably short.
* `WeierstrassCurve.baseChange_shortCurve`: the same for a base change, which is the spelling
  consumers actually hold. It follows definitionally from `map_shortCurve`, but `simp` does not
  automatically unfold `baseChange`, so that lemma never fires on this spelling by itself.
* `WeierstrassCurve.shortCurve_equation_iff`: a point lies on it exactly when
  `y² = x³ + Ax + B`.

The classical discriminant `-16(4A³ + 27B²)` is *not* restated: it is Mathlib's `Δ_of_isShortNF`,
which the instance below makes applicable and the coefficient lemmas reduce.

This is a prerequisite of the Nagell–Lutz milestone of
`TauCetiRoadmap/EllipticCurves/README.md`, Layer 6, item "The torsion subgroup and Nagell–Lutz",
whose classical statement is about this curve and its discriminant.

## Provenance

Adapted from the AINTLIB `NagellLutz` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0,
`main @ 1c1c74664e40071c2c2165bc55ca2616a67ccd6b`),
`LutzNagell/LutzNagellTheorem/ShortWeierstrass.lean`: `shortCurveZ` (`:30`), `shortCurveQ` (`:34`),
`shortCurveQ_equation_iff` (`:58`) and `shortCurveZ_delta` (`:63`, not ported — see above).

Three departures. The source fixes `ℤ` and `ℚ`; here the construction needs only `Zero R`
(`WeierstrassCurve` is a bare structure), and `map_shortCurve` relates the two — so the `ℤ → ℚ`
pair of the classical statement is one definition plus a base change, not two definitions.
The source's ten
`@[simp]` coefficient lemmas — `shortCurve{Z,Q}_a₁` through `_a₆` — collapse to five, one per
coefficient, because the ℤ and ℚ copies become one general statement that `map_shortCurve`
transports to any base change. And `shortCurveZ_delta` is not ported at all: it is exactly
Mathlib's `Δ_of_isShortNF`, `W.Δ = -16 * (4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2)`, which the coefficient
lemmas above already reduce at `shortCurve A B`.
-/

public section

namespace WeierstrassCurve

section Zero

variable {R : Type*} [Zero R] (A B : R)

/-- The short Weierstrass curve `y² = x³ + Ax + B`. Only `Zero R` is needed to write it down;
`WeierstrassCurve` is a bare structure and the three vanishing coefficients are the only
requirement. -/
def shortCurve : WeierstrassCurve R where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := A
  a₆ := B

@[simp] lemma shortCurve_a₁ : (shortCurve A B).a₁ = 0 := (rfl)

@[simp] lemma shortCurve_a₂ : (shortCurve A B).a₂ = 0 := (rfl)

@[simp] lemma shortCurve_a₃ : (shortCurve A B).a₃ = 0 := (rfl)

@[simp] lemma shortCurve_a₄ : (shortCurve A B).a₄ = A := (rfl)

@[simp] lemma shortCurve_a₆ : (shortCurve A B).a₆ = B := (rfl)

end Zero

variable {R S : Type*} [CommRing R] [CommRing S] (A B : R)

/-- `shortCurve A B` is in short normal form. This instance is the point of the definition: it
hands the curve to Mathlib's whole `*_of_isShortNF` family, so every invariant — the `b`- and
`c`-families, `Δ` and `j` — comes for free rather than being restated here. -/
instance : (shortCurve A B).IsShortNF := ⟨(rfl), (rfl), (rfl)⟩

/-- A ring hom carries `shortCurve` to `shortCurve` on the images of the coefficients. Mathlib has
no instance propagating `IsShortNF` along `map`, so this is what keeps a base change — `ℤ → ℚ` in
the classical Nagell–Lutz statement — recognisably in short form. -/
@[simp] lemma map_shortCurve (f : R →+* S) : (shortCurve A B).map f = shortCurve (f A) (f B) := by
  ext <;> simp [shortCurve, WeierstrassCurve.map]

/-- The same statement for a base change, which is the spelling consumers actually meet.
`baseChange` *is* `map (algebraMap R S)` by definition, which is why the proof below is just
`map_shortCurve` at that hom.

It is nonetheless worth stating and tagging `@[simp]`: `simp` does not automatically unfold
`baseChange`, which carries no simp lemma of its own, so `map_shortCurve` never fires on a
`baseChange` spelling. This lemma is that missing normalisation step, not a wrapper to name by
hand. -/
@[simp] lemma baseChange_shortCurve [Algebra R S] :
    (shortCurve A B).baseChange S = shortCurve (algebraMap R S A) (algebraMap R S B) :=
  map_shortCurve A B _

/-- A point lies on `y² = x³ + Ax + B` exactly when it satisfies that equation. -/
@[simp] lemma shortCurve_equation_iff (x y : R) :
    (shortCurve A B).toAffine.Equation x y ↔ y ^ 2 = x ^ 3 + A * x + B := by
  rw [Affine.equation_iff]
  simp [shortCurve]

end WeierstrassCurve

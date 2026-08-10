/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.LinearAlgebra.Dimension.Localization

/-!
# The function field of a Weierstrass curve has degree two over `R(x)`

Mathlib gives the coordinate ring `R[W]` a power basis `{1, Y}` over `R[X]`, and defines the
function field `R(W)` as its fraction field. It says nothing about `R(W)` as an extension of the
rational function field. The algebra structure for that pair *is* Mathlib's
`FractionRing.liftAlgebra`, but deliberately not an instance — for a general target it collides
with the identity structure on `FractionRing R[X]` itself — so the degree cannot be stated without
introducing it. This file exports it as an instance and proves the degree.

## Main results

* `WeierstrassCurve.Affine.moduleFinite_coordinateRing`: the coordinate ring is a finite
  `R[X]`-module — the companion of Mathlib's `Module.Free` instance, which Mathlib has only as a
  lemma, so instance search cannot reach it.
* `WeierstrassCurve.Affine.finrank_coordinateRing`: the coordinate ring's `Module.finrank` over
  `R[X]` is two, needing only `[Nontrivial R]` — which discharges the `StrongRankCondition R[X]`
  that `Module.finrank` wants, through `commRing_strongRankCondition`.
* `WeierstrassCurve.Affine.algebraFractionRingFunctionField`: the `R(x)`-algebra structure on
  `R(W)`, over any integral domain. Exporting it is enough to bring Mathlib's own
  `FractionRing.liftAlgebra` API to bear on this pair — the tower `R[X] ⊆ R(x) ⊆ R(W)` is then
  found by instance search, and the induced map is
  `FractionRing.algebraMap_liftAlgebra R[X] W.FunctionField`; neither needs restating here.
* `WeierstrassCurve.Affine.finrank_functionField`: `[R(W) : L] = 2` for any fraction field `L` of
  `R[X]` — so it serves `RatFunc R` as well as `FractionRing R[X]`.
* `WeierstrassCurve.Affine.finiteDimensional_functionField`: the extension is finite-dimensional
  over the same arbitrary `L`, which `finrank = 2` does not give by instance search.

Exporting the algebra instance is safe here for the reason Mathlib withholds it in general: the
collision is with the identity structure on `FractionRing R[X]`, and `R(W)` is a *quadratic*
extension, so the two can never coincide. The degree itself is Mathlib's
`IsFractionRing.finrank_eq` — `L` and `R(W)` are fraction rings of `R[X]` and `R[W]`, so their
degrees agree — with no algebraicity, finiteness or base-change hypothesis.

## Roadmap

The Hasse strand of `TauCetiRoadmap/EllipticCurves/README.md`, Layer 3. The degree of the Frobenius
isogeny is computed from the tower `K(W) ⊇ K(x) ⊇ K(x^q)`, where the outer degrees are this `2` and
the inner degree is `q`; the roadmap calls the Frobenius "the key input to Layer 3". It is also
Layer 0 infrastructure: the roadmap's §"What Mathlib already has (consume)" lists
`Affine.FunctionField` as consumed, and this is a complement to that API rather than a
reimplementation of it.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.

## Provenance

Ported from the AINTLIB `HasseWeil` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0, pinned by
that roadmap at `dev/hasse-weil @ 513e83879e2f`), `HasseWeil/FrobeniusIsogeny.lean`: the
declarations `coordinateRing_finite`, `finrank_coordinateRing_eq_two`, its anonymous
`Algebra (FractionRing K[X]) K(W)` instance, and `finrank_functionField_eq_two`.
`finiteDimensional_functionField` is not in the source.

Changes from the source. They are stated there inside a file that also builds the Frobenius
isogeny; here they are separated out, since the degree of `R(W)` over the rational function field
is a fact about the curve and not about any isogeny. The source states everything over a field;
here the coordinate-ring half needs only a nontrivial commutative ring and the function-field half
an integral domain, which is all either argument uses, and the degree is stated over an arbitrary
fraction field of `R[X]` rather than over `FractionRing R[X]` alone.

The source's remaining declarations are **not** ported, each being reachable without them: its
`Module K[X] K[W]`, `IsScalarTower K[X] K(x) K(W)`, `Algebra.IsIntegral K[X] K[W]` and two
`FaithfulSMul` instances are all found by instance search (`algebraMap_poly_injective` is now an
instance in `Affine/Point.lean`, and Mathlib has `FaithfulSMul.algebraMap_injective`); and its
`isBaseChange_coordToFunc`, with the two private localization instances beneath it, is not needed
at all — Mathlib's `IsFractionRing.finrank_eq` states the degree equality outright, and Mathlib has
deprecated its own base-change-flavoured version in favour of it.
-/

public section

open Polynomial

open scoped nonZeroDivisors

namespace WeierstrassCurve.Affine

section CommRing

variable {R : Type*} [CommRing R] (W : WeierstrassCurve.Affine R)

/-- **The coordinate ring is a finite `R[X]`-module.** -/
-- Mathlib registers `Module.Free R[X] R[W]` off the same basis (`Affine/Point.lean`) but not
-- `Module.Finite`, which it has only as the lemma `Polynomial.Monic.finite_adjoinRoot`; instance
-- search cannot reach a lemma. Its consumers in this repository are the two Dedekind theorems of
-- `Affine/CoordinateRing.lean` and `isIntegral_pullback_of_isIntegral_X` in
-- `Isogeny/FunctionField.lean`, each of which used to re-derive it from the basis by hand.
instance moduleFinite_coordinateRing : Module.Finite R[X] W.CoordinateRing :=
  .of_basis (CoordinateRing.basis W)

/-- **The coordinate ring has rank two over `R[X]`.** `Nontrivial R` is what `Module.finrank`
needs: it gives `StrongRankCondition R[X]` through `commRing_strongRankCondition`. -/
@[simp]
lemma finrank_coordinateRing [Nontrivial R] :
    Module.finrank R[X] W.CoordinateRing = 2 :=
  (Module.finrank_eq_card_basis (CoordinateRing.basis W)).trans (Fintype.card_fin 2)

end CommRing

section Domain

variable {R : Type*} [CommRing R] [IsDomain R] (W : WeierstrassCurve.Affine R)

/-- **The rational function field `R(x)` acts on the function field `R(W)`.** Mathlib keeps
`FractionRing.liftAlgebra` out of the instance graph because it collides with the identity
structure when the target *is* `FractionRing R[X]`; `R(W)` is a quadratic extension of `R(x)`, so
that collision cannot arise for this pair and the instance is exported. -/
noncomputable instance algebraFractionRingFunctionField :
    Algebra (FractionRing R[X]) W.FunctionField :=
  FractionRing.liftAlgebra R[X] W.FunctionField

/-- **The function field of a Weierstrass curve is a quadratic extension of the rational function
field.** Stated for an arbitrary fraction field `L` of `R[X]`, so that it serves `RatFunc R` as
well as `FractionRing R[X]`; the latter is found by instance search through
`algebraFractionRingFunctionField`. -/
@[simp]
theorem finrank_functionField (L : Type*) [Field L] [Algebra R[X] L] [IsFractionRing R[X] L]
    [Algebra L W.FunctionField] [IsScalarTower R[X] L W.FunctionField] :
    Module.finrank L W.FunctionField = 2 := by
  -- `L` and `R(W)` are fraction rings of `R[X]` and `R[W]`, so their degrees agree.
  rw [IsFractionRing.finrank_eq R[X] L W.CoordinateRing W.FunctionField, finrank_coordinateRing]

/-- The function field is finite-dimensional over any fraction field of `R[X]`. `finrank = 2` does
not give this by instance search, and downstream norm/trace/separability arguments need it. -/
instance finiteDimensional_functionField (L : Type*) [Field L] [Algebra R[X] L]
    [IsFractionRing R[X] L] [Algebra L W.FunctionField] [IsScalarTower R[X] L W.FunctionField] :
    FiniteDimensional L W.FunctionField :=
  .of_finrank_pos (by simp)

end Domain

end WeierstrassCurve.Affine

end

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.PowerTower
public import Mathlib.FieldTheory.Finite.Basic

/-!
# The finite-field Frobenius tower of a Weierstrass function field

For a finite field `K` with `q` elements and a Weierstrass curve `W`, this file compares the
general power tower `K(x^q) ⊆ K(x) ⊆ K(W)` with the subfield `K(W)^q` of `q`-th powers and
computes `[K(W) : K(W)^q] = q`.

The argument runs through a third field. Inside `K(W)` sit the image of the rational function
field `K(x)` and, inside that, the image `K(x^q)` of its own subfield of `q`-th powers, which lies
below `K(W)^q` as well. Along `K(x^q) ⊆ K(x) ⊆ K(W)` the degrees are `q` and `2`, so
`[K(W) : K(x^q)] = 2q`. Along `K(x^q) ⊆ K(W)^q ⊆ K(W)` the first degree is again `2`, because
raising to the `q`-th power embeds the pair `K(x) ⊆ K(W)` as `K(x^q) ⊆ K(W)^q` and so preserves
its relative degree. Comparing the two routes gives `2 · [K(W) : K(W)^q] = 2q`.

## Main result

* `WeierstrassCurve.Affine.finrank_fieldRange_frobeniusAlgHom`: `[K(W) : K(W)^q] = q`.

`K(W)^q` is not given a name of its own: it is the field range of
`FiniteField.frobeniusAlgHom K W.FunctionField` throughout, which is the expression
`TauCeti.Isogeny.degree` — a `finrank` over a `fieldPullback.fieldRange` — is taken over, so a
consumer needs no rewriting to reach it.

No degree here needs `W` to be elliptic: these are degrees of `K(W)` over embedded subfields, and
the Weierstrass equation alone gives the power basis.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, **Layer 1**, the Frobenius isogeny — "the key input to
Layer 3". That isogeny and its degree already exist, as `TauCeti.Isogeny.frobeniusIsogeny` and
`TauCeti.Isogeny.degree_frobeniusIsogeny : (frobeniusIsogeny W).degree = Nat.card F`, where
`Isogeny.degree φ := Module.finrank φ.fieldPullback.fieldRange W₁.FunctionField`. The subfield
`K(W)^q` here is the field range that degree is taken over, so
`finrank_fieldRange_frobeniusAlgHom` is the field-theoretic input
`degree_frobeniusIsogeny` is transported from, stated in the same `Nat.card K`.

Nothing here defines an isogeny, a `fieldPullback` or a `degree`: this file is purely the
field theory that `Isogeny/Frobenius.lean` consumes.

## Provenance

Ported from the AINTLIB `HasseWeil` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0, pinned by
that roadmap at `dev/hasse-weil @ 513e83879e2f`), `HasseWeil/FrobeniusIsogeny.lean`, the `private`
declarations `finrank_over_frobenius_image` and `frobenius_finrank_functionField`. The source's
`frobFracRange`, `frobFracRange_le_frobRange` and `finrank_frobFracRange_functionField` are the
finite-field model of the exponent-generic tower, which lives in
`Affine/FunctionField/PowerTower.lean` and carries their credit; what remains here is the
specialisation of that tower to the `q`-power map.

Changes from the source. They are `private` there, inside the file that builds the Frobenius
isogeny, and work over `FractionRing K[X]`; a large part of their length is spent transporting the
degree of the rational function field over its `q`-th powers across `FractionRing K[X] ≃+*
RatFunc K`. That passage is not needed here:
`TauCeti.RatFunc.finrank_adjoin_X_pow` is stated for `RatFunc K`, and
`_root_.WeierstrassCurve.Affine.finrank_functionField` for an arbitrary fraction field of `K[X]`,
so both factors are already available over `RatFunc K`. The source also builds its towers by hand,
out of `(IntermediateField.inclusion h).toRingHom.toAlgebra` and an
`IsScalarTower.of_algebraMap_eq`, and needs `backward.isDefEq.respectTransparency false` for the
resulting `rfl`; and it transports `[K(W)^q : K(x^q)] = 2` across an explicitly constructed
isomorphism of the two towers. All of that is Mathlib's relative degree
`IntermediateField.relfinrank` here: `relfinrank_map_map` says a relative degree is unchanged when
both fields are carried along an embedding — used once for the embedding of `K(x)` into `K(W)` and
once for the `q`-power map — and `relfinrank_mul_finrank_top` is the tower law. Neither needs a
hand-built scalar tower, so no `set_option` is required. The source's commuting square
`frobeniusAlgHom_comp_comm` of the `q`-power map with the embedding of the rational function field
is not needed either: `ratFuncAdjoinXPowRange_eq_map_ratFuncRange` asks only for the value of the
embedding at the affine coordinate, which is `FiniteField.coe_frobeniusAlgHom`.
-/

public section

open Polynomial WeierstrassCurve IntermediateField

open scoped RatFunc

namespace WeierstrassCurve.Affine

variable {K : Type*} [Field K] (W : WeierstrassCurve.Affine K)

variable [Finite K]

/-- The `q`-power map of `K(W)` raises the affine coordinate to the `q`-th power: the input the
general power tower asks for. -/
private theorem frobeniusAlgHom_apply_X :
    letI := Fintype.ofFinite K
    (_root_.FiniteField.frobeniusAlgHom K W.FunctionField)
        (algebraMap K[X] W.FunctionField X) =
      algebraMap K[X] W.FunctionField X ^ Nat.card K := by
  let _ := Fintype.ofFinite K
  rw [_root_.FiniteField.coe_frobeniusAlgHom, Nat.card_eq_fintype_card]

/-- **`[K(W) : K(W)^q] = q`.** The tower `K(x^q) ⊆ K(W)^q ⊆ K(W)` has degrees `2` and
`[K(W) : K(W)^q]`, with product `2q`. Stated over the field range of the `q`-power map itself,
which is the form `TauCeti.Isogeny.degree` — a `finrank` over a `fieldPullback.fieldRange` — is
taken over. -/
@[simp]
theorem finrank_fieldRange_frobeniusAlgHom :
    letI := Fintype.ofFinite K
    Module.finrank (_root_.FiniteField.frobeniusAlgHom K W.FunctionField).fieldRange
      W.FunctionField = Nat.card K := by
  let _ := Fintype.ofFinite K
  exact finrank_fieldRange_of_apply_X_eq_pow W _ (frobeniusAlgHom_apply_X W)

end WeierstrassCurve.Affine

end

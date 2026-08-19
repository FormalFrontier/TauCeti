/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Finrank
public import TauCeti.FieldTheory.RatFunc.Frobenius
public import Mathlib.FieldTheory.Relrank

/-!
# The function field of a curve over its subfield of `q`-th powers

Let `K` be a finite field with `q` elements and `W` a Weierstrass curve over `K`. This file
computes the degree of the function field `K(W)` over its subfield `K(W)^q` of `q`-th powers: it
is `q`.

The argument runs through a third field. Inside `K(W)` sit the image of the rational function
field `K(x)` and, inside that, the image `K(x^q)` of its own subfield of `q`-th powers, which lies
below `K(W)^q` as well. Along `K(x^q) ⊆ K(x) ⊆ K(W)` the degrees are `q` and `2`, so
`[K(W) : K(x^q)] = 2q`. Along `K(x^q) ⊆ K(W)^q ⊆ K(W)` the first degree is again `2`, because
raising to the `q`-th power embeds the pair `K(x) ⊆ K(W)` as `K(x^q) ⊆ K(W)^q` and so preserves
its relative degree. Comparing the two routes gives `2 · [K(W) : K(W)^q] = 2q`.

## Main results

* `TauCeti.WeierstrassCurve.Affine.finrank_frobeniusRatFuncRange`: `[K(W) : K(x^q)] = 2 * q`.
* `TauCeti.WeierstrassCurve.Affine.relfinrank_fieldRange_frobeniusAlgHom`: `[K(W)^q : K(x^q)] = 2`.
* `TauCeti.WeierstrassCurve.Affine.finrank_fieldRange_frobeniusAlgHom`: `[K(W) : K(W)^q] = q`.

`K(W)^q` is not given a name of its own: it is the field range of
`FiniteField.frobeniusAlgHom K W.FunctionField` throughout, which is the expression the seeded
`Isogeny.degree` — a `finrank` over a `fieldPullback.fieldRange` — is taken over, so a consumer
needs no rewriting to reach it.

No degree here needs `W` to be elliptic: they are degrees of `K(W)` over embedded subfields, and
the Weierstrass equation alone gives the power basis.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, **Layer 1**, the Frobenius isogeny — "the key input to
Layer 3", seeded as `frobeniusIsogeny` with `degree_frobeniusIsogeny : … = Nat.card F`, where
`Isogeny.degree φ := Module.finrank φ.fieldPullback.fieldRange W₁.FunctionField`. The subfield
`K(W)^q` here is the field range that seeded degree is taken over, so
`finrank_fieldRange_frobeniusAlgHom` is that theorem's field-theoretic content, available before
any isogeny exists and stated in the same `Nat.card K`.

Nothing here defines an isogeny, a `fieldPullback` or a `degree`; the seeded declarations stay
untouched for whoever builds Layer 1's isogeny API.

## Provenance

Ported from the AINTLIB `HasseWeil` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0, pinned by
that roadmap at `dev/hasse-weil @ 513e83879e2f`), `HasseWeil/FrobeniusIsogeny.lean`, the `private`
declarations `frobFracRange` — the model for `frobeniusRatFuncRange` — together with
`frobeniusAlgHom_comp_comm`, `finrank_frobFracRange_functionField`, `frobFracRange_le_frobRange`,
`finrank_over_frobenius_image` and `frobenius_finrank_functionField`. The commuting square of the
`q`-power map with the embedding of the rational function field, inside
`relfinrank_fieldRange_frobeniusAlgHom`, is `frobeniusAlgHom_comp_comm`.

Changes from the source. They are `private` there, inside the file that builds the Frobenius
isogeny, and work over `FractionRing K[X]`; a large part of their length is spent transporting the
degree of the rational function field over its `q`-th powers across `FractionRing K[X] ≃+*
RatFunc K`. That passage is not needed here:
`TauCeti.FiniteField.finrank_fieldRange_frobeniusAlgHom_ratFunc` is stated for `RatFunc K`, and
`_root_.WeierstrassCurve.Affine.finrank_functionField` for an arbitrary fraction field of `K[X]`,
so both factors are already available over `RatFunc K`. The source also builds its towers by hand,
out of `(IntermediateField.inclusion h).toRingHom.toAlgebra` and an
`IsScalarTower.of_algebraMap_eq`, and needs `backward.isDefEq.respectTransparency false` for the
resulting `rfl`; and it transports `[K(W)^q : K(x^q)] = 2` across an explicitly constructed
isomorphism of the two towers. All of that is Mathlib's relative degree
`IntermediateField.relfinrank` here: `relfinrank_map_map` says a relative degree is unchanged when
both fields are carried along an embedding — used once for the embedding of `K(x)` into `K(W)` and
once for the `q`-power map — and `relfinrank_mul_finrank_top` is the tower law. Neither needs a
hand-built scalar tower, so no `set_option` is required.
-/

public section

open Polynomial WeierstrassCurve IntermediateField

open scoped RatFunc

namespace TauCeti

namespace WeierstrassCurve.Affine

variable {K : Type*} [Field K] (W : _root_.WeierstrassCurve.Affine K)

variable [Finite K]

/-- The image of `K(x^q)`, the `q`-th powers of the rational function field, inside `K(W)`. -/
noncomputable def frobeniusRatFuncRange : IntermediateField K W.FunctionField :=
  letI := Fintype.ofFinite K
  (_root_.FiniteField.frobeniusAlgHom K (RatFunc K)).fieldRange.map
    (IsScalarTower.toAlgHom K (RatFunc K) W.FunctionField)

/-- The defining equation of `frobeniusRatFuncRange`: it is the image in `K(W)` of the field range
of the `q`-power map on `K(x)`. This is the form that carries it along `IntermediateField.map`
lemmas. -/
theorem frobeniusRatFuncRange_eq_map :
    letI := Fintype.ofFinite K
    frobeniusRatFuncRange W =
      (_root_.FiniteField.frobeniusAlgHom K (RatFunc K)).fieldRange.map
        (IsScalarTower.toAlgHom K (RatFunc K) W.FunctionField) := by
  rw [frobeniusRatFuncRange]

/-- An element of `K(W)` lies in the copy of `K(x^q)` exactly when it is the image there of a
`q`-th power from the rational function field. -/
@[simp]
theorem mem_frobeniusRatFuncRange {z : W.FunctionField} :
    z ∈ frobeniusRatFuncRange W ↔ ∃ r : RatFunc K,
      IsScalarTower.toAlgHom K (RatFunc K) W.FunctionField (r ^ Nat.card K) = z := by
  let _ := Fintype.ofFinite K
  rw [frobeniusRatFuncRange_eq_map, AlgHom.map_fieldRange]
  simp [AlgHom.mem_fieldRange, Nat.card_eq_fintype_card]

/-- `K(x^q)` sits inside `K(x)`, both read inside `K(W)`: they are the images of `K(x)^q ≤ ⊤`. -/
theorem frobeniusRatFuncRange_le_ratFuncRange :
    frobeniusRatFuncRange W ≤ _root_.WeierstrassCurve.Affine.ratFuncRange W := by
  rw [frobeniusRatFuncRange_eq_map, _root_.WeierstrassCurve.Affine.ratFuncRange_eq_map]
  exact IntermediateField.map_mono _ le_top

/-- **`[K(x) : K(x^q)] = q`**, read inside `K(W)`: the copy of the rational function field is of
degree `q` over the copy of its subfield of `q`-th powers. Embedding `K(x)` into `K(W)` does not
change this relative degree. -/
@[simp]
theorem relfinrank_frobeniusRatFuncRange :
    relfinrank (frobeniusRatFuncRange W) (_root_.WeierstrassCurve.Affine.ratFuncRange W) =
      Nat.card K := by
  let _ := Fintype.ofFinite K
  rw [frobeniusRatFuncRange_eq_map, _root_.WeierstrassCurve.Affine.ratFuncRange_eq_map,
    relfinrank_map_map, relfinrank_top_right,
    TauCeti.FiniteField.finrank_fieldRange_frobeniusAlgHom_ratFunc, Nat.card_eq_fintype_card]

/-- **`[K(W) : K(x^q)] = 2q`.** The tower `K(x^q) ⊆ K(x) ⊆ K(W)` has degrees `q` and `2`. -/
@[simp]
theorem finrank_frobeniusRatFuncRange :
    Module.finrank (frobeniusRatFuncRange W) W.FunctionField = 2 * Nat.card K := by
  have htower := relfinrank_mul_finrank_top (frobeniusRatFuncRange_le_ratFuncRange W)
  rw [relfinrank_frobeniusRatFuncRange W,
    _root_.WeierstrassCurve.Affine.finrank_ratFuncRange W] at htower
  rw [← htower, Nat.mul_comm]

/-- Raising to the `q`-th power commutes with embedding a rational function into `K(W)`. -/
private theorem frobeniusAlgHom_comp_toAlgHom :
    letI := Fintype.ofFinite K
    (_root_.FiniteField.frobeniusAlgHom K W.FunctionField).comp
        (IsScalarTower.toAlgHom K (RatFunc K) W.FunctionField) =
      (IsScalarTower.toAlgHom K (RatFunc K) W.FunctionField).comp
        (_root_.FiniteField.frobeniusAlgHom K (RatFunc K)) := by
  let _ := Fintype.ofFinite K
  ext r
  simp [_root_.FiniteField.frobeniusAlgHom_apply]

/-- **`K(x^q)` is the image of `K(x)` under the `q`-power map of `K(W)`.** Raising to the `q`-th
power commutes with embedding a rational function, so the copy of `K(x)^q` inside `K(W)` is what
the `q`-power map of the whole function field does to the copy of `K(x)`. This is the interaction
between the two subfields; both degree computations below go through it. -/
theorem frobeniusRatFuncRange_eq_map_ratFuncRange :
    letI := Fintype.ofFinite K
    frobeniusRatFuncRange W = (_root_.WeierstrassCurve.Affine.ratFuncRange W).map
      (_root_.FiniteField.frobeniusAlgHom K W.FunctionField) := by
  let _ := Fintype.ofFinite K
  rw [_root_.WeierstrassCurve.Affine.ratFuncRange_eq_map, frobeniusRatFuncRange_eq_map,
    AlgHom.fieldRange_eq_map, IntermediateField.map_map, IntermediateField.map_map,
    frobeniusAlgHom_comp_toAlgHom W]

/-- `K(x^q)` sits inside `K(W)^q`, the `q`-th powers of the whole function field: a `q`-th power
of a rational function is a `q`-th power. -/
theorem frobeniusRatFuncRange_le_frobeniusFieldRange :
    letI := Fintype.ofFinite K
    frobeniusRatFuncRange W ≤
      (_root_.FiniteField.frobeniusAlgHom K W.FunctionField).fieldRange := by
  let _ := Fintype.ofFinite K
  rw [frobeniusRatFuncRange_eq_map_ratFuncRange W, AlgHom.fieldRange_eq_map]
  exact IntermediateField.map_mono _ le_top

/-- **`[K(W)^q : K(x^q)] = 2`.** Raising `K(x) ⊆ K(W)` to the `q`-th power is an embedding of the
pair, so the relative degree `2` of `finrank_ratFuncRange` is unchanged. -/
@[simp]
theorem relfinrank_fieldRange_frobeniusAlgHom :
    letI := Fintype.ofFinite K
    relfinrank (frobeniusRatFuncRange W)
      (_root_.FiniteField.frobeniusAlgHom K W.FunctionField).fieldRange = 2 := by
  let _ := Fintype.ofFinite K
  rw [frobeniusRatFuncRange_eq_map_ratFuncRange W, AlgHom.fieldRange_eq_map, relfinrank_map_map,
    relfinrank_top_right, _root_.WeierstrassCurve.Affine.finrank_ratFuncRange]

/-- **`[K(W) : K(W)^q] = q`.** The tower `K(x^q) ⊆ K(W)^q ⊆ K(W)` has degrees `2` and
`[K(W) : K(W)^q]`, with product `2q`. Stated over the field range of the `q`-power map itself,
which is the form the seeded `Isogeny.degree` — a `finrank` over a `fieldPullback.fieldRange` —
is taken over. -/
@[simp]
theorem finrank_fieldRange_frobeniusAlgHom :
    letI := Fintype.ofFinite K
    Module.finrank (_root_.FiniteField.frobeniusAlgHom K W.FunctionField).fieldRange
      W.FunctionField = Nat.card K := by
  let _ := Fintype.ofFinite K
  have htower := relfinrank_mul_finrank_top (frobeniusRatFuncRange_le_frobeniusFieldRange W)
  rw [relfinrank_fieldRange_frobeniusAlgHom W, finrank_frobeniusRatFuncRange W] at htower
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) htower

end WeierstrassCurve.Affine

end TauCeti

end

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import TauCeti.FieldTheory.Finite.FrobeniusFixed

/-!
# The points of a Weierstrass curve fixed by the `q`-power map

For a finite field `K` with `q` elements and a field extension `L`, Mathlib's
`WeierstrassCurve.Affine.Point.map` carries the `q`-power `K`-algebra map
`FiniteField.frobeniusAlgHom K L` to an endomorphism of the `L`-points of a Weierstrass curve `W`
base changed to `L`. This file identifies the points it fixes:

`map (frobeniusAlgHom K L) P = P ↔ P ∈ Set.range (baseChange K L)`,

the points coming from the `K`-points, and counts them — the fixed locus has exactly
`Nat.card (W⁄K).Point` elements, `baseChange` being injective.

This is the point-level counterpart of
`TauCeti.FiniteField.pow_card_eq_self_iff_mem_range_algebraMap`, which says the same of a single
coordinate, and is proved from it one coordinate at a time.

## Main results

* `WeierstrassCurve.Affine.Point.map_frobeniusAlgHom_eq_self_iff_mem_range_baseChange`: the
  fixed points are the base-changed ones.
* `WeierstrassCurve.Affine.Point.ncard_setOf_map_frobeniusAlgHom_eq_self`: the fixed locus has
  `Nat.card (W⁄K).Point` elements.

Neither statement assumes `L` algebraically closed, and neither needs a `Fintype` instance on the
point types: `Nat.card` and `Set.ncard` are defined without one. Finiteness nonetheless *holds*
where it matters — `K` is finite, so the `K`-points are, and the fixed locus is in bijection with
them — while the ambient `L`-point type may well be infinite.

Layer 3 of `TauCetiRoadmap/EllipticCurves/README.md` fixes the fixed points of the `q`-power
Frobenius as the model of record for the points over an extension in its zeta-function
milestone, and asks for "the comparison with the base-change-to-a-chosen-extension model, and
invariance of the count under the noncanonical field equivalences" as separate named lemmas.
The two results below are that comparison, and the count it carries, for a single `q`-power
step and an arbitrary extension `L / K`.

## Relation to the Frobenius isogeny

`TauCetiRoadmap/EllipticCurves/README.md` Layer 3 warns that the equation-level Frobenius
`(x, y) ↦ (x ^ q, y ^ q)` is a *private computation*, and that "Layer 1 is the sole public notion
of isogeny". Accordingly **no Frobenius endomorphism of points is defined here.** Both statements
are about Mathlib's `Affine.Point.map` applied to Mathlib's `FiniteField.frobeniusAlgHom`; no new
notion is introduced that could compete with Layer 1's `TauCeti.Isogeny.frobeniusIsogeny`, already
on `main`. The roadmap records that the two are to be identified by a named comparison lemma —
"the Frobenius isogeny induces `(x, y) ↦ (x ^ q, y ^ q)` on points" — which is a separate
milestone and is not attempted here.

## Provenance

Ported from the AINTLIB `HasseWeil` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0, pinned by
that roadmap at `dev/hasse-weil @ 513e83879e2f`),
`HasseWeil/Curves/FrobeniusFixedPoint.lean` (repository path
`projects/HasseWeil/HasseWeil/Curves/FrobeniusFixedPoint.lean`), declarations
`geomFrobeniusPoint_fixed_iff_mem_range_includePointBC`,
`fixedLocus_geomFrobenius_eq_range_includePointBC` and
`ncard_fixedLocus_geomFrobenius_eq_pointCount`.

The source's other sixteen declarations are **not** ported: some are already available, in
Mathlib or on `main`, and the rest are omitted deliberately, for the reasons given below. Its
`geomFrobeniusPointFun` and `geomFrobeniusPoint` are both
`Affine.Point.map (frobeniusAlgHom K L)`. Its `includePointBC` is not quite that map: it is the
source's own ring-homomorphism transport applied to `algebraMap K L`, which `main` already carries
as `TauCeti.WeierstrassCurve.Affine.Point.mapAlong`, itself ported from the source's own import
`HasseWeil/EC/AffinePointMap.lean`, and whose `mapAlong_eq_map` identifies it with Mathlib's
`Affine.Point.baseChange K L`, used here directly.
Its `includePointBC_injective` is `Affine.Point.map_injective`; its `geomFrobRingHom`,
`geomFrobRingHom_apply` and `map_geomFrob_baseChange_eq_self` belong to an earlier approach the
source itself abandoned and are unreachable from its final chain; and the `_zero` and `_some`
computation rules for both maps are Mathlib's `Affine.Point.map_zero` and `map_some`,
while the two `_apply` lemmas unfold bundles this file does not build. The source's
`oneSubGeomFrobHom` and its two kernel lemmas are likewise not reproduced: they bundle `1 - π` as
an equation-level endomorphism, which is what the roadmap paragraph above forbids in a public
statement, and their content is `sub_eq_zero` away from the fixed-point form kept here.

Changes from the source. `L` is an arbitrary field extension rather than `AlgebraicClosure K`, and
no `Fintype` instance on the points is assumed, `Nat.card` and `Set.ncard` needing none. The
source's docstrings describe its cardinality result as "a `sorry` stub"; that is stale prose at
this pin — the file contains no `sorry` token in any proof — and is not carried across.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, V.1.1.
-/

public section

namespace WeierstrassCurve.Affine.Point

variable {K L : Type*} [Field K] [Fintype K] [Field L] [DecidableEq L] [Algebra K L]
  (W : WeierstrassCurve K)

/-- **A point over an extension of a finite field is fixed by the `q`-power map exactly when it
comes from the base field**, where `q` is the cardinality of the base.

This is `TauCeti.FiniteField.pow_card_eq_self_iff_mem_range_algebraMap` applied to each coordinate,
the point at infinity being fixed and base changed from the point at infinity. -/
@[simp]
theorem map_frobeniusAlgHom_eq_self_iff_mem_range_baseChange [DecidableEq K]
    (P : (W.baseChange L).toAffine.Point) :
    Affine.Point.map (W' := W) (FiniteField.frobeniusAlgHom K L) P = P ↔
      P ∈ Set.range (Affine.Point.baseChange (W' := W) K L) := by
  rcases P with _ | ⟨x, y, h⟩
  · exact iff_of_true (Affine.Point.map_zero _) ⟨0, Affine.Point.map_zero _⟩
  · rw [Affine.Point.map_some, Affine.Point.some.injEq]
    simp only [FiniteField.coe_frobeniusAlgHom]
    rw [TauCeti.FiniteField.pow_card_eq_self_iff_mem_range_algebraMap,
      TauCeti.FiniteField.pow_card_eq_self_iff_mem_range_algebraMap]
    constructor
    · rintro ⟨⟨x₀, rfl⟩, ⟨y₀, rfl⟩⟩
      refine ⟨Affine.Point.some x₀ y₀ ((W.toAffine.baseChange_nonsingular
        (f := Algebra.ofId K L) (FaithfulSMul.algebraMap_injective K L) x₀ y₀).mp h), ?_⟩
      -- `baseChange` is `map (Algebra.ofId K L)`, so this is its `some` computation rule.
      rw [Affine.Point.map_some]
      simp only [Algebra.ofId_apply]
    · rintro ⟨_ | ⟨x₀, y₀, h₀⟩, hQ⟩
      -- `baseChange` fixes the point at infinity definitionally, but `rcases` leaves the
      -- constructor `zero` rather than `0`, so name that reduction before discriminating.
      · refine absurd hQ ?_
        change (Affine.Point.zero : (W.baseChange L).toAffine.Point) ≠ Affine.Point.some x y h
        simp
      · rw [Affine.Point.map_some, Affine.Point.some.injEq] at hQ
        exact ⟨⟨x₀, hQ.1⟩, ⟨y₀, hQ.2⟩⟩

/-- **The `q`-power map fixes exactly `Nat.card W.toAffine.Point` of the `L`-points.**

Immediate from `map_frobeniusAlgHom_eq_self_iff_mem_range_baseChange` and injectivity of
`Affine.Point.map`. No `Fintype` instance on the point types is needed, and both sides are finite
regardless, `K` being finite, even when the ambient `L`-point type is not. -/
theorem ncard_setOf_map_frobeniusAlgHom_eq_self : {P : (W.baseChange L).toAffine.Point |
        Affine.Point.map (W' := W) (FiniteField.frobeniusAlgHom K L) P = P}.ncard =
      Nat.card W.toAffine.Point := by
  classical
  have hset : {P : (W.baseChange L).toAffine.Point |
      Affine.Point.map (W' := W) (FiniteField.frobeniusAlgHom K L) P = P} =
      Set.range (Affine.Point.baseChange (W' := W) K L) :=
    Set.ext fun P => map_frobeniusAlgHom_eq_self_iff_mem_range_baseChange W P
  rw [hset]
  exact Set.ncard_range_of_injective (Affine.Point.map_injective _)

end WeierstrassCurve.Affine.Point

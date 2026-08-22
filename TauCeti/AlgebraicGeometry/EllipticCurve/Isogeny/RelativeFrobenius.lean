/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.PowerTower
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.RelativeFrobenius
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Separability

/-!
# The relative Frobenius isogeny

When `p > 1` (equivalently, when `F` has positive characteristic), raising to the `p`-th power is a
ring endomorphism of `F` but not an `F`-algebra map, so it does not turn a Weierstrass curve into an
endomorphism of itself unless `F` is a prime field. When `p = 1`, the characteristic-zero case, this
map is the identity. In either case it gives a map to the **Frobenius twist** `W⁽ᵖ⁾`, whose
`a`-invariants are the `p`-th powers of those of `W`: Mathlib's
`W.map (frobenius F p)`, with `WeierstrassCurve.map_a₁` and its siblings for the coefficient
description and `WeierstrassCurve.map_map` for iteration. The **relative Frobenius**
`F_{W/F} : W → W⁽ᵖ⁾` is then an honest `F`-morphism, the one that reads `(x, y) ↦ (xᵖ, yᵖ)` on
points.

Contravariantly, that is the `F`-algebra map out of the coordinate ring of the twist sending the
two coordinates of `W⁽ᵖ⁾` to the `p`-th powers of the coordinates of `W`. It is well defined
because the Weierstrass polynomial of the twist is the image of that of `W` under the coefficient
Frobenius, so substituting `p`-th powers into it produces the `p`-th power of the Weierstrass
polynomial of `W`, which vanishes on the coordinate ring. The resulting map lands in
`W.CoordinateRing`, not merely in `W.FunctionField`: relative Frobenius is a morphism of affine
curves.

Over a finite field the `q`-power map is already an `F`-algebra map, and
`TauCeti.Isogeny.frobeniusIsogeny` is the resulting self-isogeny. The construction here is the
one that survives over an arbitrary — in particular imperfect — base, at the cost of a moving
target.

That coordinate-ring map is an input from `Affine/RelativeFrobenius.lean`, which declares it as
`CoordinateRing.relativeFrobenius` together with its factorisation `relativeFrobenius_comp_map` of
the `p`-power map of `W.CoordinateRing` into Mathlib's semilinear base-change map followed by an
`F`-linear one; the pointedness of the isogeny below and its pure inseparability are both read off
that factorisation.

## Main definitions

* `TauCeti.Isogeny.relativeFrobeniusPullback`: the coordinate-ring map read into
  `W.FunctionField`, a `TauCeti.CoordinatePullback`.
* `TauCeti.Isogeny.relativeFrobeniusIsogeny`: the relative Frobenius isogeny
  `W → W.map (frobenius F p)`.

## Main results

* `TauCeti.Isogeny.isPurelyInseparable_relativeFrobeniusIsogeny`: the relative Frobenius is
  purely inseparable (Silverman II.2.11(b)); every element of `F(W)` has its `p`-th power in the
  pulled-back copy of `F(W⁽ᵖ⁾)`.
* `TauCeti.Isogeny.degree_relativeFrobeniusIsogeny`: its degree is `p` (Silverman II.2.11(c)),
  with `TauCeti.Isogeny.separableDegree_relativeFrobeniusIsogeny` and
  `TauCeti.Isogeny.inseparableDegree_relativeFrobeniusIsogeny` splitting that as `1 · p`.

The degree is the shared tower comparison
`WeierstrassCurve.Affine.finrank_fieldRange_of_apply_X_eq_pow`, applied to the pullback: over the
copy of `F(xᵖ)` inside `F(W)`, that copy sits below `F(x)` with relative degree `p` and below the
pulled-back `F(W⁽ᵖ⁾)` with relative degree `2`, while `[F(W) : F(x)] = 2`. The finite-field
`WeierstrassCurve.Affine.finrank_fieldRange_frobeniusAlgHom` is the same lemma applied to the
`q`-power map.

No result here needs `W` to be elliptic, matching the isogeny API it extends; Mathlib's
`WeierstrassCurve.instIsEllipticMap` supplies `(W.map (frobenius F p)).IsElliptic` for a consumer
that does want it.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, **Layer 1**, the milestone "Relative Frobenius, a
milestone and not a one-liner" (`README.md:429`), which asks for "the **Frobenius twist** `W^{(p)}`
with its coefficient description and base-change API" — Mathlib's `WeierstrassCurve.map` along
`frobenius`, consumed rather than redefined — and "the **relative Frobenius** `F_{W/K} : W →
W^{(p)}` with its function-field pullback". Its point-level formula, the iterated twists
`W^{(p^r)}` with iterated relative Frobenius, the factorisation `φ = φ_sep ∘ F_{W/K}^r` of
AEC II.2.12, and Verschiebung remain.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.11, whose N.B. is the
  reason this file exists: over an imperfect `F`, parts (b) and (c) (pure inseparability and
  degree `p`) survive unchanged, but part (a), the identification `φ* F(W⁽ᵖ⁾) = F(W)ᵖ`, does not.
  Accordingly only the containment `F(W)ᵖ ⊆ φ* F(W⁽ᵖ⁾)` is proved here, as
  `TauCeti.Isogeny.pow_mem_fieldRange_relativeFrobeniusIsogeny`, which is all pure
  inseparability needs. Over a finite, hence perfect, base there is no gap, and
  `Isogeny/Frobenius.lean` identifies the pullback with the `q`-power map outright
  (`fieldPullback_frobeniusIsogeny`).

## Provenance

Not a port. The pinned sources of this roadmap build only the **absolute** `q`-power Frobenius of
a curve over a finite field (AINTLIB's `HasseWeil/FrobeniusIsogeny.lean`, already migrated as
`TauCeti.Isogeny.frobeniusIsogeny` and
`WeierstrassCurve.Affine.finrank_fieldRange_frobeniusAlgHom`); the relative Frobenius over
an arbitrary base, and the twist it maps to, appear in none of them.
The degree computation reuses the migrated tower argument of
`TauCeti/AlgebraicGeometry/EllipticCurve/Affine/FunctionField/PowerTower.lean`, which carries the
AINTLIB credit for it, and whose `ratFuncAdjoinXPowRange` API rests on
`TauCeti.RatFunc.finrank_adjoin_X_pow` from `TauCeti/FieldTheory/RatFunc/PowerTower.lean`.
-/

public section

open Polynomial WeierstrassCurve

namespace TauCeti

open WeierstrassCurve.Affine

namespace Isogeny

/-! ### The relative Frobenius isogeny -/

variable {F : Type*} [Field F] (p : ℕ) [ExpChar F p] (W : WeierstrassCurve.Affine F)

/-- **The relative Frobenius pullback**: `CoordinateRing.relativeFrobenius` read into the
function field of `W`. -/
noncomputable def relativeFrobeniusPullback :
    CoordinatePullback W (W.map (frobenius F p)) :=
  (IsScalarTower.toAlgHom F W.CoordinateRing W.FunctionField).comp
    (CoordinateRing.relativeFrobenius p W)

/-- The relative Frobenius pullback is the coordinate-ring map followed by the embedding of
`W.CoordinateRing` in its fraction field. -/
@[simp]
theorem relativeFrobeniusPullback_apply (z : (W.map (frobenius F p)).CoordinateRing) :
    relativeFrobeniusPullback p W z =
      algebraMap W.CoordinateRing W.FunctionField
        (CoordinateRing.relativeFrobenius p W z) := by
  rw [relativeFrobeniusPullback, AlgHom.comp_apply, IsScalarTower.toAlgHom_apply]

/-- **The relative Frobenius maps the point at infinity to the point at infinity.** Every element
of `W.CoordinateRing` is a `p`-th root of an element pulled back from the twist, hence integral
over the pulled-back coordinate ring. -/
theorem mapsInfinity_relativeFrobeniusPullback :
    (relativeFrobeniusPullback p W).MapsInfinity := by
  refine CoordinatePullback.mapsInfinity_of_pow (relativeFrobeniusPullback p W)
    (expChar_pos F p) fun z ↦ ?_
  exact ⟨_root_.WeierstrassCurve.Affine.CoordinateRing.map W (frobenius F p) z, by
    rw [relativeFrobeniusPullback_apply,
      CoordinateRing.relativeFrobenius_map, map_pow]⟩

/-- **The relative Frobenius isogeny** `F_{W/F} : W → W⁽ᵖ⁾`. -/
noncomputable def relativeFrobeniusIsogeny : Isogeny W (W.map (frobenius F p)) where
  pullback := relativeFrobeniusPullback p W
  mapsInfinity := mapsInfinity_relativeFrobeniusPullback p W

/-- The relative Frobenius isogeny's pullback is `relativeFrobeniusPullback`. -/
@[simp]
theorem relativeFrobeniusIsogeny_pullback :
    (relativeFrobeniusIsogeny p W).pullback = relativeFrobeniusPullback p W := (rfl)

/-- The function-field pullback of a base-changed coordinate function is its `p`-th power.

**Deliberately not `@[simp]`.** Its left-hand side is already dismantled by the `@[simp]` chain
`Isogeny.fieldPullback_algebraMap`, `relativeFrobeniusIsogeny_pullback`,
`relativeFrobeniusPullback_apply` and `CoordinateRing.relativeFrobenius_map`, so tagging it fails
`simpNF`; it is stated because it is the field-level form the pure-inseparability argument below
quotes. -/
theorem fieldPullback_relativeFrobeniusIsogeny_coordinateRingMap (z : W.CoordinateRing) :
    (relativeFrobeniusIsogeny p W).fieldPullback
        (algebraMap (W.map (frobenius F p)).CoordinateRing
          (W.map (frobenius F p)).FunctionField
          (_root_.WeierstrassCurve.Affine.CoordinateRing.map W (frobenius F p) z)) =
      algebraMap W.CoordinateRing W.FunctionField z ^ p := by
  rw [Isogeny.fieldPullback_algebraMap, relativeFrobeniusIsogeny_pullback,
    relativeFrobeniusPullback_apply, CoordinateRing.relativeFrobenius_map,
    map_pow]

/-- **`F(W)ᵖ` lies in the pulled-back copy of `F(W⁽ᵖ⁾)`.** A quotient of two coordinate functions
has its `p`-th power the quotient of two pullbacks. -/
theorem pow_mem_fieldRange_relativeFrobeniusIsogeny (z : W.FunctionField) :
    z ^ p ∈ (relativeFrobeniusIsogeny p W).fieldPullback.fieldRange := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := W.CoordinateRing) z
  rw [div_pow]
  exact div_mem ⟨_, fieldPullback_relativeFrobeniusIsogeny_coordinateRingMap p W a⟩
    ⟨_, fieldPullback_relativeFrobeniusIsogeny_coordinateRingMap p W b⟩

/-- **The relative Frobenius isogeny is purely inseparable** (Silverman II.2.11(b)). -/
instance isPurelyInseparable_relativeFrobeniusIsogeny :
    IsPurelyInseparable (relativeFrobeniusIsogeny p W).fieldPullback.fieldRange
      W.FunctionField := by
  rw [isPurelyInseparable_iff_pow_mem _ p]
  exact fun z ↦ ⟨1, by simpa using pow_mem_fieldRange_relativeFrobeniusIsogeny p W z⟩

/-! ### The degree -/

section Degree

/-- **The relative Frobenius pullback sends the affine coordinate of the twist to `xᵖ`.** -/
@[simp]
theorem fieldPullback_relativeFrobeniusIsogeny_X :
    (relativeFrobeniusIsogeny p W).fieldPullback
        (algebraMap F[X] (W.map (frobenius F p)).FunctionField X) =
      algebraMap F[X] W.FunctionField X ^ p := by
  rw [IsScalarTower.algebraMap_apply F[X] (W.map (frobenius F p)).CoordinateRing
      (W.map (frobenius F p)).FunctionField,
    Isogeny.fieldPullback_algebraMap]
  simp [IsScalarTower.algebraMap_apply F[X] W.CoordinateRing]

/-- **The relative Frobenius isogeny has degree `p`** (Silverman II.2.11(c)). This is the tower
comparison `WeierstrassCurve.Affine.finrank_fieldRange_of_apply_X_eq_pow`, whose only input is the
value of the pullback at the affine coordinate: both `F(x)` and the pulled-back `F(W⁽ᵖ⁾)` sit
between `F(xᵖ)` and `F(W)`, of relative degrees `p` and `2` over it, and `[F(W) : F(x)] = 2` as
well, so the two towers give `2 · deg = p · 2`. -/
@[simp]
theorem degree_relativeFrobeniusIsogeny : (relativeFrobeniusIsogeny p W).degree = p := by
  rw [Isogeny.degree_def]
  exact _root_.WeierstrassCurve.Affine.finrank_fieldRange_of_apply_X_eq_pow W _
    (fieldPullback_relativeFrobeniusIsogeny_X p W)

end Degree

/-- **The relative Frobenius isogeny has separable degree one**, as pure inseparability
requires.

**Deliberately not `@[simp]`.** The `isPurelyInseparable_relativeFrobeniusIsogeny` instance
already lets the `@[simp]` lemma `separableDegree_eq_one_of_isPurelyInseparable` close this goal,
so tagging it fails `simpNF` with `simp can prove this`; it is stated as the named specialisation
a consumer quotes, exactly as `separableDegree_frobeniusIsogeny` is for the absolute Frobenius. -/
theorem separableDegree_relativeFrobeniusIsogeny :
    (relativeFrobeniusIsogeny p W).separableDegree = 1 :=
  separableDegree_eq_one_of_isPurelyInseparable (relativeFrobeniusIsogeny p W)

/-- **The relative Frobenius isogeny carries its whole degree `p` in the inseparable part.**

**Deliberately not `@[simp]`.** Its left-hand side is already rewritten to `p` by the `@[simp]`
pair `inseparableDegree_eq_degree_of_isPurelyInseparable` and `degree_relativeFrobeniusIsogeny`,
so tagging it fails `simpNF`; it is stated for the same reason as
`separableDegree_relativeFrobeniusIsogeny` above. -/
theorem inseparableDegree_relativeFrobeniusIsogeny :
    (relativeFrobeniusIsogeny p W).inseparableDegree = p := by
  rw [inseparableDegree_eq_degree_of_isPurelyInseparable, degree_relativeFrobeniusIsogeny]

end Isogeny

end TauCeti

end

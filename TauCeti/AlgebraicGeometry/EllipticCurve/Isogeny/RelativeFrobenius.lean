/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Finrank
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Separability
public import TauCeti.FieldTheory.RatFunc.Frobenius
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.FieldTheory.Relrank

/-!
# The relative Frobenius isogeny

Over a field `F` of exponential characteristic `p`, raising to the `p`-th power is a ring
endomorphism of `F` but not an `F`-algebra map, so it does not turn a Weierstrass curve into an
endomorphism of itself unless `F` is a prime field. What it does give is a map to the **Frobenius
twist** `W⁽ᵖ⁾`, the curve whose `a`-invariants are the `p`-th powers of those of `W`: Mathlib's
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

## Main definitions

* `TauCeti.Isogeny.relativeFrobeniusCoordinateHom`: the relative Frobenius as an `F`-algebra map
  `(W.map (frobenius F p)).CoordinateRing →ₐ[F] W.CoordinateRing`.
* `TauCeti.Isogeny.relativeFrobeniusPullback`: the same map read into `W.FunctionField`, a
  `TauCeti.CoordinatePullback`.
* `TauCeti.Isogeny.relativeFrobeniusIsogeny`: the relative Frobenius isogeny
  `W → W.map (frobenius F p)`.

## Main results

* `TauCeti.Isogeny.relativeFrobeniusCoordinateHom_comp_map`: composing the relative Frobenius
  with Mathlib's base-change map `W.CoordinateRing →+* (W.map (frobenius F p)).CoordinateRing`
  gives the absolute Frobenius of `W.CoordinateRing`. This is the factorisation of the `p`-power
  map into a semilinear map followed by an `F`-linear one, and both the pointedness of the
  isogeny and its pure inseparability are read off it.
* `TauCeti.Isogeny.isPurelyInseparable_relativeFrobeniusIsogeny`: the relative Frobenius is
  purely inseparable (Silverman II.2.11(b)); every element of `F(W)` has its `p`-th power in the
  pulled-back copy of `F(W⁽ᵖ⁾)`.
* `TauCeti.Isogeny.degree_relativeFrobeniusIsogeny`: its degree is `p` (Silverman II.2.11(c)),
  with `TauCeti.Isogeny.separableDegree_relativeFrobeniusIsogeny` and
  `TauCeti.Isogeny.inseparableDegree_relativeFrobeniusIsogeny` splitting that as `1 · p`.

The degree is computed exactly as
`TauCeti.WeierstrassCurve.Affine.finrank_fieldRange_frobeniusAlgHom` computes the finite-field
one, by comparing two towers over the copy of `F(xᵖ)` inside `F(W)`:
that copy sits below `F(x)` with relative degree `p`, and below the pulled-back `F(W⁽ᵖ⁾)` with
relative degree `2`, while `[F(W) : F(x)] = 2`.

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

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.

## Provenance

Not a port. The pinned sources of this roadmap build only the **absolute** `q`-power Frobenius of
a curve over a finite field (AINTLIB's `HasseWeil/FrobeniusIsogeny.lean`, already migrated as
`TauCeti.Isogeny.frobeniusIsogeny` and
`TauCeti.WeierstrassCurve.Affine.finrank_fieldRange_frobeniusAlgHom`); the relative Frobenius over
an arbitrary base, and the twist it maps to, appear in none of them.
The degree computation reuses the migrated tower argument of
`TauCeti/AlgebraicGeometry/EllipticCurve/Affine/FrobeniusTower.lean` in the form
`TauCeti.RatFunc.finrank_adjoin_X_pow`, which is stated over an arbitrary field and exponent
there precisely so that it serves both.
-/

public section

open Polynomial WeierstrassCurve

namespace TauCeti

variable {F : Type*} [Field F] (p : ℕ) [ExpChar F p] (W : WeierstrassCurve.Affine F)

/-- The coordinate ring of a Weierstrass curve has the same exponential characteristic as the
base field, which is what raising to the `p`-th power there needs to be a ring homomorphism. -/
instance expChar_coordinateRing : ExpChar W.CoordinateRing p :=
  ExpChar.of_injective_algebraMap' F p

namespace Isogeny

/-! ### The relative Frobenius on coordinate rings -/

/-- Substituting `(xᵖ, yᵖ)` into the Weierstrass polynomial of the twist gives zero: it is the
`p`-th power of the Weierstrass polynomial of `W`, evaluated at `(x, y)`. -/
private theorem eval₂_relativeFrobenius_eq_zero :
    Polynomial.eval₂ ((AdjoinRoot.of W.polynomial).comp (expand F p).toRingHom)
      (AdjoinRoot.root W.polynomial ^ p) (W.map (frobenius F p)).polynomial = 0 := by
  -- The coefficient map of the twist, followed by substitution of `X ^ p`, is the absolute
  -- Frobenius of the coordinate ring restricted to `F[X]`.
  have hcomp : ((AdjoinRoot.of W.polynomial).comp (expand F p).toRingHom).comp
      (mapRingHom (frobenius F p)) =
      (frobenius W.CoordinateRing p).comp (AdjoinRoot.of W.polynomial) := by
    refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_ <;> simp [frobenius_def, ← map_pow]
  rw [WeierstrassCurve.Affine.map_polynomial, Polynomial.eval₂_map, hcomp,
    show (AdjoinRoot.root W.polynomial ^ p)
      = frobenius W.CoordinateRing p (AdjoinRoot.root W.polynomial) from rfl,
    ← Polynomial.hom_eval₂, AdjoinRoot.eval₂_root, map_zero]

/-- **The relative Frobenius on coordinate rings**: the `F`-algebra map out of the coordinate ring
of the Frobenius twist `W⁽ᵖ⁾` that sends its two coordinates to the `p`-th powers of the
coordinates of `W`. -/
noncomputable def relativeFrobeniusCoordinateHom :
    (W.map (frobenius F p)).CoordinateRing →ₐ[F] W.CoordinateRing :=
  { AdjoinRoot.lift ((AdjoinRoot.of W.polynomial).comp (expand F p).toRingHom)
      (AdjoinRoot.root W.polynomial ^ p) (eval₂_relativeFrobenius_eq_zero p W) with
    commutes' := fun c ↦ by
      rw [IsScalarTower.algebraMap_apply F F[X] (W.map (frobenius F p)).CoordinateRing,
        IsScalarTower.algebraMap_apply F F[X] W.CoordinateRing]
      simp [AdjoinRoot.algebraMap_eq] }

/-- The relative Frobenius substitutes `X ^ p` into a polynomial in the affine coordinate. -/
@[simp]
theorem relativeFrobeniusCoordinateHom_of (g : F[X]) :
    relativeFrobeniusCoordinateHom p W (AdjoinRoot.of (W.map (frobenius F p)).polynomial g) =
      AdjoinRoot.of W.polynomial (expand F p g) :=
  AdjoinRoot.lift_of (eval₂_relativeFrobenius_eq_zero p W)

/-- The relative Frobenius sends the second coordinate of the twist to `y ^ p`. -/
@[simp]
theorem relativeFrobeniusCoordinateHom_root :
    relativeFrobeniusCoordinateHom p W (AdjoinRoot.root (W.map (frobenius F p)).polynomial) =
      AdjoinRoot.root W.polynomial ^ p :=
  AdjoinRoot.lift_root (eval₂_relativeFrobenius_eq_zero p W)

/-- **The absolute Frobenius factors through the twist.** Mathlib's base-change map
`W.CoordinateRing →+* (W.map (frobenius F p)).CoordinateRing` is semilinear over the coefficient
Frobenius; composing the relative Frobenius with it recovers the `p`-power map of
`W.CoordinateRing`. Everything else in this file is a consequence of this identity. -/
theorem relativeFrobeniusCoordinateHom_comp_map :
    (relativeFrobeniusCoordinateHom p W).toRingHom.comp
        (_root_.WeierstrassCurve.Affine.CoordinateRing.map W (frobenius F p)) =
      frobenius W.CoordinateRing p := by
  refine AdjoinRoot.ringHom_ext (Polynomial.ringHom_ext (fun a ↦ ?_) ?_) ?_ <;>
    simp [_root_.WeierstrassCurve.Affine.CoordinateRing.map, frobenius_def, ← map_pow]

/-- The pointwise form of `relativeFrobeniusCoordinateHom_comp_map`. -/
@[simp]
theorem relativeFrobeniusCoordinateHom_map (z : W.CoordinateRing) :
    relativeFrobeniusCoordinateHom p W
      (_root_.WeierstrassCurve.Affine.CoordinateRing.map W (frobenius F p) z) = z ^ p := by
  simpa [frobenius_def] using
    congrArg (fun f : W.CoordinateRing →+* W.CoordinateRing ↦ f z)
      (relativeFrobeniusCoordinateHom_comp_map p W)

/-! ### The relative Frobenius isogeny -/

/-- **The relative Frobenius pullback**: `relativeFrobeniusCoordinateHom` read into the function
field of `W`. -/
noncomputable def relativeFrobeniusPullback :
    CoordinatePullback W (W.map (frobenius F p)) :=
  (IsScalarTower.toAlgHom F W.CoordinateRing W.FunctionField).comp
    (relativeFrobeniusCoordinateHom p W)

/-- The relative Frobenius pullback is the coordinate-ring map followed by the embedding of
`W.CoordinateRing` in its fraction field. -/
@[simp]
theorem relativeFrobeniusPullback_apply (z : (W.map (frobenius F p)).CoordinateRing) :
    relativeFrobeniusPullback p W z =
      algebraMap W.CoordinateRing W.FunctionField (relativeFrobeniusCoordinateHom p W z) := by
  rw [relativeFrobeniusPullback, AlgHom.comp_apply, IsScalarTower.toAlgHom_apply]

/-- **The relative Frobenius maps the point at infinity to the point at infinity.** Every element
of `W.CoordinateRing` is a `p`-th root of an element pulled back from the twist, hence integral
over the pulled-back coordinate ring. -/
theorem mapsInfinity_relativeFrobeniusPullback :
    (relativeFrobeniusPullback p W).MapsInfinity := by
  rw [CoordinatePullback.mapsInfinity_iff]
  let _ := (relativeFrobeniusPullback p W).toRingHom.toAlgebra
  intro z
  refine IsIntegral.of_pow (n := p) (expChar_pos F p) ?_
  have h : algebraMap W.CoordinateRing W.FunctionField z ^ p =
      algebraMap (W.map (frobenius F p)).CoordinateRing W.FunctionField
        (_root_.WeierstrassCurve.Affine.CoordinateRing.map W (frobenius F p) z) := by
    rw [RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      relativeFrobeniusPullback_apply, relativeFrobeniusCoordinateHom_map, map_pow]
  rw [h]
  exact isIntegral_algebraMap

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
`relativeFrobeniusPullback_apply` and `relativeFrobeniusCoordinateHom_map`, so tagging it fails
`simpNF`; it is stated because it is the field-level form the pure-inseparability argument
below quotes. -/
theorem fieldPullback_relativeFrobeniusIsogeny_map (z : W.CoordinateRing) :
    (relativeFrobeniusIsogeny p W).fieldPullback
        (algebraMap (W.map (frobenius F p)).CoordinateRing
          (W.map (frobenius F p)).FunctionField
          (_root_.WeierstrassCurve.Affine.CoordinateRing.map W (frobenius F p) z)) =
      algebraMap W.CoordinateRing W.FunctionField z ^ p := by
  rw [Isogeny.fieldPullback_algebraMap, relativeFrobeniusIsogeny_pullback,
    relativeFrobeniusPullback_apply, relativeFrobeniusCoordinateHom_map, map_pow]

/-- **`F(W)ᵖ` lies in the pulled-back copy of `F(W⁽ᵖ⁾)`.** A quotient of two coordinate functions
has its `p`-th power the quotient of two pullbacks. -/
theorem pow_mem_fieldRange_relativeFrobeniusIsogeny (z : W.FunctionField) :
    z ^ p ∈ (relativeFrobeniusIsogeny p W).fieldPullback.fieldRange := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := W.CoordinateRing) z
  rw [div_pow]
  exact div_mem ⟨_, fieldPullback_relativeFrobeniusIsogeny_map p W a⟩
    ⟨_, fieldPullback_relativeFrobeniusIsogeny_map p W b⟩

/-- **The relative Frobenius isogeny is purely inseparable** (Silverman II.2.11(b)). -/
instance isPurelyInseparable_relativeFrobeniusIsogeny :
    IsPurelyInseparable (relativeFrobeniusIsogeny p W).fieldPullback.fieldRange
      W.FunctionField := by
  rw [isPurelyInseparable_iff_pow_mem _ p]
  exact fun z ↦ ⟨1, by simpa using pow_mem_fieldRange_relativeFrobeniusIsogeny p W z⟩

/-! ### The degree -/

section Degree

open scoped _root_.RatFunc

/-- The affine coordinate of `W`, read as the image of the rational function `X`. -/
private theorem toAlgHom_ratFunc_X :
    IsScalarTower.toAlgHom F (_root_.RatFunc F) W.FunctionField _root_.RatFunc.X =
      algebraMap F[X] W.FunctionField X := by
  rw [IsScalarTower.toAlgHom_apply, ← _root_.RatFunc.algebraMap_X,
    ← IsScalarTower.algebraMap_apply F[X] (_root_.RatFunc F) W.FunctionField]

/-- **The relative Frobenius pullback sends the affine coordinate of the twist to `xᵖ`.** -/
@[simp]
theorem fieldPullback_relativeFrobeniusIsogeny_X :
    (relativeFrobeniusIsogeny p W).fieldPullback
        (algebraMap F[X] (W.map (frobenius F p)).FunctionField X) =
      algebraMap F[X] W.FunctionField X ^ p := by
  rw [IsScalarTower.algebraMap_apply F[X] (W.map (frobenius F p)).CoordinateRing
      (W.map (frobenius F p)).FunctionField,
    Isogeny.fieldPullback_algebraMap, relativeFrobeniusIsogeny_pullback,
    relativeFrobeniusPullback_apply, AdjoinRoot.algebraMap_eq,
    relativeFrobeniusCoordinateHom_of, Polynomial.expand_X, map_pow, map_pow,
    ← AdjoinRoot.algebraMap_eq, ← IsScalarTower.algebraMap_apply F[X] W.CoordinateRing]

/-- The copy of `F(xᵖ)` inside `F(W)` is the image of the rational function field of the twist:
the two descriptions of the field the tower argument below is anchored at. -/
private theorem map_adjoin_ratFunc_X_pow :
    (IntermediateField.adjoin F {(_root_.RatFunc.X : _root_.RatFunc F) ^ p}).map
        (IsScalarTower.toAlgHom F (_root_.RatFunc F) W.FunctionField) =
      (_root_.WeierstrassCurve.Affine.ratFuncRange (W.map (frobenius F p))).map
        (relativeFrobeniusIsogeny p W).fieldPullback := by
  rw [_root_.WeierstrassCurve.Affine.ratFuncRange_eq_map, IntermediateField.map_map,
    ← _root_.RatFunc.adjoin_X, IntermediateField.adjoin_map, IntermediateField.adjoin_map]
  congr 1
  simp only [Set.image_singleton, AlgHom.coe_comp, Function.comp_apply, map_pow,
    toAlgHom_ratFunc_X, fieldPullback_relativeFrobeniusIsogeny_X]

/-- **The relative Frobenius isogeny has degree `p`** (Silverman II.2.11(c)). Both `F(x)` and the
pulled-back `F(W⁽ᵖ⁾)` sit between `F(xᵖ)` and `F(W)`, of relative degrees `p` and `2` over it;
since `[F(W) : F(x)] = 2` as well, the two towers give `2 · deg = p · 2`. -/
@[simp]
theorem degree_relativeFrobeniusIsogeny : (relativeFrobeniusIsogeny p W).degree = p := by
  set M : IntermediateField F W.FunctionField :=
    (IntermediateField.adjoin F {(_root_.RatFunc.X : _root_.RatFunc F) ^ p}).map
      (IsScalarTower.toAlgHom F (_root_.RatFunc F) W.FunctionField) with hM
  set L := (relativeFrobeniusIsogeny p W).fieldPullback.fieldRange with hL
  have hMrat : IntermediateField.relfinrank M
      (_root_.WeierstrassCurve.Affine.ratFuncRange W) = p := by
    rw [hM, _root_.WeierstrassCurve.Affine.ratFuncRange_eq_map,
      IntermediateField.relfinrank_map_map, IntermediateField.relfinrank_top_right,
      TauCeti.RatFunc.finrank_adjoin_X_pow]
  have hML : IntermediateField.relfinrank M L = 2 := by
    rw [hM, map_adjoin_ratFunc_X_pow, hL, AlgHom.fieldRange_eq_map,
      IntermediateField.relfinrank_map_map, IntermediateField.relfinrank_top_right,
      _root_.WeierstrassCurve.Affine.finrank_ratFuncRange]
  have hle : M ≤ _root_.WeierstrassCurve.Affine.ratFuncRange W := by
    rw [hM, _root_.WeierstrassCurve.Affine.ratFuncRange_eq_map]
    exact IntermediateField.map_mono _ le_top
  have hle' : M ≤ L := by
    rw [hM, map_adjoin_ratFunc_X_pow, hL, AlgHom.fieldRange_eq_map]
    exact IntermediateField.map_mono _ le_top
  have h₁ := IntermediateField.relfinrank_mul_finrank_top hle
  have h₂ := IntermediateField.relfinrank_mul_finrank_top hle'
  rw [hMrat, _root_.WeierstrassCurve.Affine.finrank_ratFuncRange] at h₁
  rw [hML] at h₂
  rw [Isogeny.degree_def, ← hL]
  omega

end Degree

/-- **The relative Frobenius isogeny has separable degree one**, as pure inseparability
requires. -/
theorem separableDegree_relativeFrobeniusIsogeny :
    (relativeFrobeniusIsogeny p W).separableDegree = 1 :=
  separableDegree_eq_one_of_isPurelyInseparable (relativeFrobeniusIsogeny p W)

/-- **The relative Frobenius isogeny carries its whole degree `p` in the inseparable part.** -/
theorem inseparableDegree_relativeFrobeniusIsogeny :
    (relativeFrobeniusIsogeny p W).inseparableDegree = p := by
  rw [inseparableDegree_eq_degree_of_isPurelyInseparable, degree_relativeFrobeniusIsogeny]

end Isogeny

end TauCeti

end

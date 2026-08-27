/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.XSubT
public import TauCeti.AlgebraicGeometry.EllipticCurve.NormalForms

/-!
# Base change of the étale algebra, and the local condition of `2`-descent

Let `W : y² = f(x) = x³ + a₂x² + a₄x + a₆` be an elliptic curve in characteristic `≠ 2` normal
form over a field `K`, with étale algebra `A = K[X]⧸⟨f⟩` and descent map
`μ : W(K) → M = Aˣ/(Aˣ)²`, as set up in
`TauCeti/AlgebraicGeometry/EllipticCurve/MordellWeil/XSubT.lean`.

Everything in that construction base-changes along a field extension `L/K` — in the arithmetic
application `L` is a completion of `K`. This file builds that base change and uses it to define
the **local condition** at `L`: the subgroup

`W.localCondition L : Subgroup W.M`

of square classes whose image in `(W⁄L).M` lies in the image of the local descent map `μ_L`. The
`2`-Selmer group of `W` is cut out of `W.M` by these conditions at all completions of `K`, so
`localCondition` is the object every later descent statement is phrased in.

## Main definitions

* `WeierstrassCurve.Affine.mapA`: the base-change homomorphism `K[X]⧸⟨f⟩ →+* L[X]⧸⟨f⟩` of étale
  algebras.
* `WeierstrassCurve.Affine.localRes`: the induced map `W.M →* (W⁄L).M` on square classes.
* `WeierstrassCurve.Affine.pointMap`: the base-change homomorphism `W(K) →+ W(L)` on points.
* `WeierstrassCurve.Affine.localCondition`: the local `2`-descent condition at `L`.

## Main statements

* `WeierstrassCurve.Affine.localRes_μX` and `WeierstrassCurve.Affine.localRes_comp_μ`: the
  descent map is natural under base change — restricting square classes after the global `μ` is
  applying the local `μ` after the base change of points.
* `WeierstrassCurve.Affine.range_μ_le_localCondition`: the image of the global descent map
  satisfies the local condition at every extension field. This is what makes `localCondition` a
  *condition*: it is a constraint the classes coming from `W(K)` are known to satisfy, so the
  intersection of the local conditions bounds `W(K)/2W(K)` from above.

## Implementation notes

Square classes are spelled `W.M`, the quotient of `W.Aˣ` by the range of `powMonoidHom 2`,
following `XSubT.lean`; the source uses a local abbreviation `Units.modPow` for the same group,
which is not a Mathlib declaration and which TauCeti deliberately does not carry, so that the
repository has a single spelling of square classes. Accordingly `localRes` is built from
`QuotientGroup.map` rather than from the source's `Units.modPow.map`.

`pointMap` is Mathlib's `WeierstrassCurve.Affine.Point.map` and is not a new construction: the
only content is the alignment of `W` with `W⁄K`, which `baseChange_self` supplies and
Mathlib's `AddEquiv.cast` transports along.

## Provenance

Adapted, with the author's proofs, from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, pinned by
`TauCetiRoadmap/EllipticCurves/README.md` at `66889eada51a`),
`EllipticCurves/SelmerGroup.lean` lines 85-295, which are that file's `BaseChange` section up to
the local condition and its compatibility with `μ`.

This advances `TauCetiRoadmap/EllipticCurves/README.md`, Layer 6 (README:813-820), whose
"Explicit `2`-descent (core, this layer)" bullet names "the local conditions" as the first item
to migrate.
-/

public section

open Polynomial

namespace WeierstrassCurve

namespace Affine

section CommRing

variable {R : Type*} [CommRing R] (W : Affine R)

/-- Base changing along the identity algebra map returns the curve itself. Stated over a
commutative ring: it is a formal `map` identity and uses nothing about `R` beyond its ring
structure. -/
@[simp]
lemma baseChange_self : (W⁄R).toAffine = W := by
  -- `WeierstrassCurve.baseChange` (Weierstrass.lean:236) is a plain `def` and Mathlib exposes no
  -- unfolding lemma for it, so this one definitional step cannot be replaced by an API rewrite.
  -- It must be `change` rather than `show`: the step rewrites the goal rather than restating it,
  -- which is exactly what `linter.style.show` requires. Everything after it is a named rewrite.
  change W.map (algebraMap R R) = W
  rw [show algebraMap R R = RingHom.id R from Algebra.algebraMap_self]
  exact W.map_id

section Map

variable {S : Type*} [CommRing S] (σ : R →+* S)

lemma map_f : (W.map σ).toAffine.f = W.f.map σ := by
  simp only [f, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_X,
    Polynomial.map_C, map_a₂, map_a₄, map_a₆]

lemma eval_map_f (x : R) : (W.map σ).toAffine.f.eval (σ x) = σ (W.f.eval x) := by
  rw [map_f, Polynomial.eval_map, Polynomial.eval₂_at_apply]

lemma map_fCofactor (x : R) : (W.fCofactor x).map σ = (W.map σ).toAffine.fCofactor (σ x) := by
  simp only [fCofactor, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_mul,
    Polynomial.map_X, Polynomial.map_C, map_a₂, map_a₄, map_add, map_mul, map_pow]

end Map

section Algebra

variable (S : Type*) [CommRing S] [Algebra R S]

lemma eval_baseChange_f (x : R) :
    (W⁄S).toAffine.f.eval (algebraMap R S x) = algebraMap R S (W.f.eval x) :=
  W.eval_map_f (algebraMap R S) x

lemma baseChange_fCofactor (x : R) :
    (W.fCofactor x).map (algebraMap R S) = (W⁄S).toAffine.fCofactor (algebraMap R S x) :=
  W.map_fCofactor (algebraMap R S) x

lemma baseChange_f : (W⁄S).toAffine.f = W.f.map (algebraMap R S) :=
  W.map_f (algebraMap R S)

end Algebra

end CommRing

variable {K : Type*} [Field K] (W : Affine K)

section BaseChange

variable (L : Type*) [Field L] [Algebra K L]

/-- The base-change homomorphism `K[X]⧸⟨f⟩ →+* L[X]⧸⟨f⟩` of étale algebras, as an instance of
`AdjoinRoot.map` (so that its API — `map_of`, `map_root`, `map_comp_map`, `mapRingEquiv` —
applies directly). -/
noncomputable def mapA : W.A →+* (W⁄L).toAffine.A :=
  AdjoinRoot.map (algebraMap K L) W.f (W⁄L).toAffine.f (W.baseChange_f L).dvd

@[simp]
lemma mapA_mk (p : K[X]) :
    W.mapA L (AdjoinRoot.mk W.f p) = AdjoinRoot.mk (W⁄L).toAffine.f (p.map (algebraMap K L)) :=
  AdjoinRoot.map_mk _ _

/-- The base-change map on square classes of units of the étale algebra. -/
noncomputable def localRes : W.M →* (W⁄L).toAffine.M :=
  QuotientGroup.map _ _ (Units.map (W.mapA L).toMonoidHom) <| by
    rintro _ ⟨u, rfl⟩
    exact ⟨Units.map (W.mapA L).toMonoidHom u, by simp [powMonoidHom]⟩

@[simp]
lemma localRes_mk (u : W.Aˣ) :
    W.localRes L (QuotientGroup.mk u) = QuotientGroup.mk (Units.map (W.mapA L).toMonoidHom u) :=
  QuotientGroup.map_mk _ _ _ _ u

/-- The base-change map on square classes, on the class of a unit given as `IsUnit a`. -/
-- Deliberately NOT `@[simp]`: the left-hand side is not in simp-normal form, because
-- `localRes_mk` rewrites `W.localRes L ↑ha.unit` first, so the attribute could never fire —
-- tagging it is what failed the simp-NF lint on this branch. It is for explicit `rw` at the
-- `localRes_μX` call sites below.
lemma localRes_unit {a : W.A} (ha : IsUnit a) :
    W.localRes L (ha.unit : W.M) = ((ha.map (W.mapA L)).unit : (W⁄L).toAffine.M) := by
  rw [localRes_mk]
  exact congrArg _ (Units.ext rfl)

section PointMap

open scoped Classical in
/-- Transporting an affine point along an equality of curves carries its coordinates unchanged.

The transport itself is Mathlib's `AddEquiv.cast`, which is `Equiv.cast (congrArg _ h)` bundled
as an `AddEquiv`; this is the one fact about it that mentions `Point.some`, and Mathlib has no
lemma of that shape because `Point` is not one of its indexed families. -/
private lemma cast_point_some {W₁ W₂ : Affine K} (h : W₁ = W₂) {x y : K}
    (hp : W₁.Nonsingular x y) :
    AddEquiv.cast (M := fun W' : Affine K => W'.Point) h (Point.some x y hp) =
      Point.some x y (h ▸ hp) := by
  subst h; rfl

open scoped Classical in
/-- The base-change homomorphism on points, `W(K) →+ W(L)`: Mathlib's
`WeierstrassCurve.Affine.Point.map`, aligned with the plain base change `W⁄L` via
`baseChange_self`. -/
noncomputable def pointMap : W.Point →+ (W⁄L).toAffine.Point :=
  (Point.map (W' := W) (Algebra.ofId K L)).comp
    (AddEquiv.cast (M := fun W' : Affine K => W'.Point) W.baseChange_self.symm).toAddMonoidHom

open scoped Classical in
/-- The base-change map on an affine point carries its coordinates along `algebraMap K L`. -/
@[simp]
lemma pointMap_some {x y : K} (h : W.Nonsingular x y) : W.pointMap L (Point.some x y h) =
      Point.some (W' := (W⁄L).toAffine) (algebraMap K L x) (algebraMap K L y)
        (show (W⁄L).toAffine.Nonsingular (algebraMap K L x) (algebraMap K L y) from
          (W.map_nonsingular (algebraMap K L).injective x y).mpr h) := by
  -- The type ascription above is load-bearing: `map_nonsingular` produces the nonsingularity
  -- proof at `W.map (algebraMap K L)`, and although `W⁄L` is a reducible abbreviation for
  -- exactly that, the elaborator does not unfold it at `instances` transparency, so the two
  -- identically-printing types do not unify without being told the target.
  rw [pointMap, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, cast_point_some,
    Point.map_some]
  rfl

end PointMap

variable [W.IsElliptic] [W.IsCharNeTwoNF]

instance : (W⁄L).IsElliptic := inferInstanceAs (W.map (algebraMap K L)).IsElliptic

open scoped Classical in
/-- The local `2`-descent condition at the extension field `L` of `K` (in the applications,
`L` is a completion of `K`): the subgroup of square classes in the étale algebra of `W`
whose image over `L` comes from an `L`-point of the curve. -/
noncomputable def localCondition : Subgroup W.M :=
  ((μ (W := (W⁄L).toAffine)).range).comap (W.localRes L)

open scoped Classical in
@[simp]
lemma mem_localCondition_iff {m : W.M} :
    m ∈ W.localCondition L ↔ W.localRes L m ∈ (μ (W := (W⁄L).toAffine)).range :=
  Subgroup.mem_comap

open scoped Classical in
/-- The local restriction map is compatible with the `x - T` maps: the square class of
`x - T` restricts to that of `σ(x) - T`, and likewise for the modified class at a
`2`-torsion `x`-coordinate. -/
theorem localRes_μX (x : K) :
    W.localRes L (W.μX x) = μX (W := (W⁄L).toAffine) (algebraMap K L x) := by
  rcases eq_or_ne (W.f.eval x) 0 with hx | hx
  · have hxL : (W⁄L).toAffine.f.eval (algebraMap K L x) = 0 := by
      rw [W.eval_baseChange_f, hx, map_zero]
    rw [μX_of_eval_f_eq_zero hxL, μX_of_eval_f_eq_zero hx, localRes_unit]
    refine congrArg _ (Units.ext ?_)
    rw [IsUnit.unit_spec, IsUnit.unit_spec]
    simp only [mapA_mk, Polynomial.map_add,
      Polynomial.map_sub, Polynomial.map_C, Polynomial.map_X, W.baseChange_fCofactor]
  · have hxL : (W⁄L).toAffine.f.eval (algebraMap K L x) ≠ 0 := by
      rw [W.eval_baseChange_f]
      exact fun h0 ↦ hx ((map_eq_zero _).mp h0)
    rw [μX_of_eval_f_ne_zero hxL, μX_of_eval_f_ne_zero hx, localRes_unit]
    refine congrArg _ (Units.ext ?_)
    rw [IsUnit.unit_spec, IsUnit.unit_spec]
    simp only [mapA_mk, Polynomial.map_sub,
      Polynomial.map_C, Polynomial.map_X]


open scoped Classical in
/-- Naturality of the descent map under base change: restricting square classes after the
global `μ` is applying the local `μ` after the base change of points. -/
theorem localRes_comp_μ : (W.localRes L).comp (μ (W := W)) =
      (μ (W := (W⁄L).toAffine)).comp (AddMonoidHom.toMultiplicative (W.pointMap L)) := by
  refine MonoidHom.ext fun P' ↦ ?_
  obtain ⟨P, rfl⟩ := Multiplicative.ofAdd.surjective P'
  simp only [MonoidHom.comp_apply, AddMonoidHom.toMultiplicative_apply_apply, toAdd_ofAdd,
    μ_apply]
  cases P with
  | zero =>
      rw [← Point.zero_def, μ₀_zero, map_one, map_zero (W.pointMap L),
        μ₀_zero (W := (W⁄L).toAffine)]
  | some x y hP =>
      rw [μ₀_some, W.pointMap_some L hP, μ₀_some (W := (W⁄L).toAffine), W.localRes_μX L x]

open scoped Classical in
/-- The image of the global descent map `μ` satisfies the local condition at every extension
field: this is formal from the naturality `localRes_comp_μ`. -/
theorem range_μ_le_localCondition : (μ (W := W)).range ≤ W.localCondition L := by
  rw [localCondition, ← Subgroup.map_le_iff_le_comap, MonoidHom.map_range, localRes_comp_μ]
  rintro _ ⟨P, rfl⟩
  exact ⟨_, rfl⟩

end BaseChange

end Affine

end WeierstrassCurve

end

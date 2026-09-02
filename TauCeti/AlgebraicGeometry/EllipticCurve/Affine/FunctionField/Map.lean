/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.CoordinateRingMap
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.GenericPoint

/-!
# The function field along a homomorphism of the base field

Mathlib carries a Weierstrass curve along a ring homomorphism `f : R →+* S` (`WeierstrassCurve.map`)
and carries its coordinate ring along with it (`CoordinateRing.map`, injective when `f` is). This
file carries the *function* field: for `f : F →+* K` a homomorphism of fields, `F(W)` embeds into
`K(W.map f)`.

There is nothing to choose. `F(W)` is the fraction field of the domain `F[W]`, and `F[W]` lands
in the field `K(W.map f)` injectively, so the embedding is the unique extension of that
composite across fractions — `IsFractionRing.lift`. What the file records is how the embedding
meets everything else: the two coordinates, the scalars, and composition of base maps.

The scalar compatibility `map_algebraMap` is the load-bearing one. Read as an equality of ring
homomorphisms out of `F` it says the square

```text
    F  ──────────────▸  K
    │                   │
    ▾                   ▾
  F(W)  ────────────▸  K(W.map f)
```

commutes, and `map_map_algebraMap` is that square applied to the coefficients of a second curve:
a curve `W₂` over `F` base-changed to `F(W₁)` and then carried along the embedding is the same
curve as `W₂.map f` base-changed to `K(W₁.map f)`. That equality is what lets a point of `W₂`
over `F(W₁)` — equivalently, by the universal property in `Isogeny/Basic.lean`, a coordinate
pullback — be pushed to a point of `W₂.map f` over `K(W₁.map f)`.

The homomorphism of base fields is an arbitrary `f : F →+* K`, not an `algebraMap`. Base change
along a field extension is the case `f = algebraMap F K`, while an automorphism `f = σ` gives the
semilinear transport of `F(W)` to the function field of the conjugate curve `W.map σ`. The latter
is the raw material for a Galois action but is not itself one: the target is `K(W.map σ)`, not
`K(W)`, so an action would additionally need the identification `W.map σ = W` for a curve defined
over the fixed field together with its coherence laws, and none of that is built into the
statements here. A single map covers both readings, and neither is built in.

## Main definitions

* `WeierstrassCurve.Affine.FunctionField.map`: the embedding `F(W) → K(W.map f)`.

## Main results

* `WeierstrassCurve.Affine.FunctionField.map_algebraMap_coordinateRing`: it restricts to
  `CoordinateRing.map` on the coordinate ring, which is what pins it down.
* `WeierstrassCurve.Affine.FunctionField.map_algebraMap` and
  `WeierstrassCurve.Affine.FunctionField.map_comp_algebraMap`: it is compatible with the scalars,
  in element and in composed form.
* `WeierstrassCurve.Affine.FunctionField.map_genericX` and
  `WeierstrassCurve.Affine.FunctionField.map_genericY`: it sends the generic point of `W` to the
  generic point of `W.map f`.
* `WeierstrassCurve.Affine.FunctionField.map_id`,
  `WeierstrassCurve.Affine.FunctionField.map_map`, and its homomorphism-level companion
  `map_comp_map`: functoriality in `f`.
* `WeierstrassCurve.Affine.FunctionField.map_map_algebraMap`: the commuting square above, at the
  level of a second curve base-changed to the function field.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, **Layer 0.5** (README:369), whose first milestone
(README:376-378) asks for "base change of Weierstrass equations, coordinate rings, function
fields, points, and isogenies". This is the function-field entry of that list; the isogeny entry
is `Isogeny/BaseChange.lean`, which is what consumes everything here.
-/

public section

open Polynomial

open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine

variable {F K L : Type*} [Field F] [Field K] [Field L]

namespace FunctionField

variable (W : WeierstrassCurve.Affine F) (f : F →+* K)

/-- The coordinate ring of `W` sits inside the function field of `W.map f`, injectively: the
composite of Mathlib's `CoordinateRing.map` with the embedding of a domain in its fraction field.
This is the map `FunctionField.map` extends. -/
private theorem algebraMap_comp_map_injective : Function.Injective
    ((algebraMap (W.map f).CoordinateRing (W.map f).FunctionField).comp
      (CoordinateRing.map W f)) :=
  (FaithfulSMul.algebraMap_injective _ _).comp (CoordinateRing.map_injective f.injective)

/-- **The function field carried along a homomorphism of the base field.** `F(W)` is the fraction
field of `F[W]`, which lands injectively in the field `K(W.map f)`, so there is exactly one
extension of that map across fractions. -/
noncomputable def map : W.FunctionField →+* (W.map f).FunctionField :=
  IsFractionRing.lift (algebraMap_comp_map_injective W f)

/-- **`FunctionField.map` restricts to `CoordinateRing.map`**, which is the property that
determines it. -/
@[simp]
theorem map_algebraMap_coordinateRing (z : W.CoordinateRing) :
    map W f (algebraMap W.CoordinateRing W.FunctionField z) =
      algebraMap (W.map f).CoordinateRing (W.map f).FunctionField (CoordinateRing.map W f z) :=
  IsFractionRing.lift_algebraMap (algebraMap_comp_map_injective W f) z

/-- **`FunctionField.map` is compatible with the scalars**: a constant of `F` goes to the
corresponding constant of `K`. -/
@[simp]
theorem map_algebraMap (a : F) :
    map W f (algebraMap F W.FunctionField a) =
      algebraMap K (W.map f).FunctionField (f a) := by
  rw [IsScalarTower.algebraMap_apply F W.CoordinateRing W.FunctionField,
    map_algebraMap_coordinateRing, CoordinateRing.map_algebraMap,
    ← IsScalarTower.algebraMap_apply]

/-- **`FunctionField.map` is compatible with the scalars**, in composed form: the square with
`f` along the top and the two constant embeddings down the sides commutes. -/
theorem map_comp_algebraMap :
    (map W f).comp (algebraMap F W.FunctionField) =
      (algebraMap K (W.map f).FunctionField).comp f :=
  RingHom.ext <| map_algebraMap W f

/-- `FunctionField.map` sends the generic `x`-coordinate to the generic `x`-coordinate. -/
@[simp]
theorem map_genericX : map W f W.genericX = (W.map f).genericX := by
  rw [genericX_def, genericX_def, map_algebraMap_coordinateRing]
  exact congr_arg _ (CoordinateRing.map_of_X W f)

/-- `FunctionField.map` sends the generic `y`-coordinate to the generic `y`-coordinate. -/
@[simp]
theorem map_genericY : map W f W.genericY = (W.map f).genericY := by
  rw [genericY_def, genericY_def, map_algebraMap_coordinateRing]
  exact congr_arg _ (CoordinateRing.map_root W f)

/-- **`FunctionField.map` along the identity is the identity.** -/
@[simp]
theorem map_id : map W (RingHom.id F) = RingHom.id W.FunctionField :=
  IsFractionRing.ringHom_ext (A := W.CoordinateRing) fun z ↦ by
    rw [map_algebraMap_coordinateRing, CoordinateRing.map_id]
    rfl

/-- **`FunctionField.map` is functorial.** As for `CoordinateRing.map_comp_map`, the curve equality
`(W.map f).map g = W.map (g.comp f)` holds definitionally, so no transport appears. -/
theorem map_comp_map (g : K →+* L) :
    (map (W.map f) g).comp (map W f) = map W (g.comp f) :=
  IsFractionRing.ringHom_ext (A := W.CoordinateRing) fun z ↦ by
    rw [RingHom.comp_apply, map_algebraMap_coordinateRing, map_algebraMap_coordinateRing]
    rw [← RingHom.comp_apply (CoordinateRing.map (W.map f) g), CoordinateRing.map_comp_map]
    exact (map_algebraMap_coordinateRing W (g.comp f) z).symm

/-- **Pointwise functoriality of `FunctionField.map`.** -/
@[simp]
theorem map_map (g : K →+* L) (z : W.FunctionField) :
    map (W.map f) g (map W f z) = map W (g.comp f) z :=
  RingHom.congr_fun (map_comp_map W f g) z

variable (W₂ : WeierstrassCurve.Affine F)

/-- **The commuting square, carried on the coefficients of a second curve.** A curve `W₂` over `F`
base-changed to the function field of `W`, then carried along `FunctionField.map W f`, is
`W₂.map f` base-changed to the function field of `W.map f`.

This is what makes a point of `W₂` over `F(W)` — equivalently a coordinate pullback — push
forward along `f`. -/
theorem map_map_algebraMap :
    (W₂.map (algebraMap F W.FunctionField)).map (map W f) =
      (W₂.map f).map (algebraMap K (W.map f).FunctionField) :=
  congrArg (fun g : F →+* (W.map f).FunctionField ↦ W₂.map g) (map_comp_algebraMap W f)

end FunctionField

end WeierstrassCurve.Affine

end

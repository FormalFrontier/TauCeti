/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.FunctionField
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.TautologicalPoint

/-!
# The tautological point is the generic point, pushed along the pullback

The tautological point of an isogeny `φ : W₁ ⟶ W₂` is the point of `W₂` over `F(W₁)` whose
coordinates are the pullbacks of the two coordinate functions of `W₂`. Those pullbacks are the
images of the generic coordinates of `W₂` under the function-field map `φ^*`, so the tautological
point is nothing but the generic point of `W₂` transported along `φ^*` by Mathlib's
`WeierstrassCurve.Affine.Point.map`.

The transport is an `AddMonoidHom` and is functorial, so the tautological point of a composite
`ψ ∘ φ` is the tautological point of `ψ` transported along `φ^*`. This expresses a composite of
pullbacks as a statement in the group `W₃⁄F(W₁)`, which is how `[m] ∘ [n] = [m n]` is proved in
`MulByInt/Comp.lean`.

## Main results

* `TauCeti.Isogeny.tautologicalPoint_eq_map_genericPoint`: the tautological point of `φ` is the
  generic point of `W₂` transported along `φ^*`.
* `TauCeti.Isogeny.tautologicalPoint_comp`: the tautological point of a composite `ψ ∘ φ` is the
  tautological point of `ψ` transported along `φ^*`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.
-/

public section

open Polynomial

open WeierstrassCurve.Affine

open scoped Polynomial.Bivariate

namespace TauCeti

open _root_.WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W₁ W₂ W₃ : WeierstrassCurve.Affine F}

namespace Isogeny

variable [W₂.IsElliptic]

/-- **The tautological point is the generic point transported along the pullback.** The
coordinates of the tautological point of `φ` are the images of the generic coordinates of `W₂`
under the function-field map `φ^*`, which is exactly what `Point.map` does to the generic
point. -/
theorem tautologicalPoint_eq_map_genericPoint (φ : Isogeny W₁ W₂) :
    φ.pullback.tautologicalPoint = Point.map φ.fieldPullback (genericPoint W₂) := by
  refine Point.eq_of_coords (CoordinatePullback.tautologicalPoint_ne_zero _) ?_ ?_ ?_
  · rw [genericPoint_eq_some, Point.map_some]
    exact Point.some_ne_zero _
  · rw [CoordinatePullback.xCoord_tautologicalPoint, Point.xCoord_map, xCoord_genericPoint,
      genericX_def, φ.fieldPullback_algebraMap, AdjoinRoot.mk_C]
  · rw [CoordinatePullback.yCoord_tautologicalPoint, Point.yCoord_map, yCoord_genericPoint,
      genericY_def, φ.fieldPullback_algebraMap, AdjoinRoot.mk_X]

variable [W₃.IsElliptic]

omit [W₂.IsElliptic] in
/-- **The tautological point of a composite**: transporting the tautological point of `ψ` along
`φ^*` gives the tautological point of `ψ ∘ φ`. This is functoriality of `Point.map` read through
the previous identification. -/
-- Not `@[simp]`: `Isogeny.comp_pullback` is itself `@[simp]`, so it rewrites this left-hand side
-- to `(φ.fieldPullback.comp ψ.pullback).tautologicalPoint` before this rule could fire, and
-- `simpNF` rejects the pair.
theorem tautologicalPoint_comp (ψ : Isogeny W₂ W₃) (φ : Isogeny W₁ W₂) :
    (ψ.comp φ).pullback.tautologicalPoint =
      Point.map φ.fieldPullback ψ.pullback.tautologicalPoint := by
  rw [tautologicalPoint_eq_map_genericPoint, tautologicalPoint_eq_map_genericPoint,
    comp_fieldPullback, Point.map_map]

end Isogeny

end TauCeti

end

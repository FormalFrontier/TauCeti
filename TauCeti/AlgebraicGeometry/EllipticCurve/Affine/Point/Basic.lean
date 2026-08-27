/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Eliminating the constructors of an affine point

`WeierstrassCurve.Affine.Point` is a two-constructor inductive type: the point at infinity, and an
affine point together with a nonsingularity certificate. Ruling out the first constructor and
naming the data of the second is a step that recurs wherever a point is known to be nonzero.

This file packages that step as an existential, which is the form that reads best when the point
is a compound term such as `n • P`: `obtain` names the coordinates, the nonsingularity certificate
and the identifying equation in one line, with no separate generalisation to arrange.

## Main results

* `WeierstrassCurve.Affine.Point.exists_eq_some_of_ne_zero`: a nonzero affine point is `.some`,
  in a form that applies to a compound point.
-/

public section

namespace WeierstrassCurve.Affine.Point

variable {F : Type*} [CommRing F] {E : WeierstrassCurve F}

/-- **A nonzero affine point is `.some`.** The case split on `Affine.Point`'s two constructors,
packaged as an existential: one `obtain` yields the coordinates, the nonsingularity certificate,
and the equation identifying the point with `.some` of them — the last being what consumers go on
to rewrite with. -/
theorem exists_eq_some_of_ne_zero {P : Affine.Point E.toAffine} (hP : P ≠ 0) :
    ∃ x y, ∃ hns : E.toAffine.Nonsingular x y, P = .some _ _ hns := by
  rcases P with _ | ⟨_, _, hns⟩
  · exact absurd rfl hP
  · exact ⟨_, _, hns, rfl⟩

end WeierstrassCurve.Affine.Point

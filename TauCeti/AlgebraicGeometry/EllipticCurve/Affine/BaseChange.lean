/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic

/-!
# Base change of affine elliptic curves

Mathlib carries ellipticity through `WeierstrassCurve.map`. This module exposes the same instance
for the canonical affine base-change spelling `W⁄A`, so consumers of the point and function-field
base-change APIs do not have to unfold that abbreviation to recover the instance.

This is infrastructure for the base-change lane of
`TauCetiRoadmap/EllipticCurves/README.md`, Layer 0.5.
-/

public section

open _root_.WeierstrassCurve

namespace TauCeti.WeierstrassCurve.Affine

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  {W : _root_.WeierstrassCurve.Affine R} [W.IsElliptic]

/-- **Base change preserves ellipticity**, in the `(W⁄A).toAffine` spelling used by the affine
point API. -/
instance instIsEllipticBaseChange : (W⁄A).toAffine.IsElliptic :=
  inferInstanceAs (W.map (algebraMap R A)).IsElliptic

end TauCeti.WeierstrassCurve.Affine

end

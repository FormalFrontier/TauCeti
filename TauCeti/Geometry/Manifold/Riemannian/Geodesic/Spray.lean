/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.CoordinateChange

/-!
# The geodesic spray

The geodesic spray of a connection is the vector field `S` on the tangent bundle whose integral
curves are the velocity lifts of geodesics.  At a point `z = ⟨x, v⟩` of the tangent bundle its
value is the pair `(v, -Γ_x (v, v))`, where `Γ_x` is the model-space Christoffel map of the
connection in the tangent-bundle trivialization centred at the base point `x` of `z`: the first
component re-states the velocity, the second encodes the acceleration the connection prescribes.

For this local formula to define a global vector field, the Christoffel map must transform
correctly when the tangent-bundle trivialization, equivalently the tangent-bundle chart, is
changed.  The supporting tangent-chart API is in
`TauCeti.Geometry.Manifold.VectorBundle.Tangent`, and the Christoffel transformation law is in
`TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.CoordinateChange`.

## References

* [Geodesics, the exponential map, and the Hopf--Rinow theorem roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HopfRinow/README.md),
  Layer 1, "The geodesic spray".
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 3, §2.
* J. M. Lee, *Introduction to Riemannian Manifolds*, GTM 176, 2018, Ch. 4.
-/

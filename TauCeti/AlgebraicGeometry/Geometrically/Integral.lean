/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# Geometrically integral morphisms

Mathlib's `AlgebraicGeometry.GeometricallyIntegral` records that the property is stable under base
change, but has nothing about isomorphisms. This file adds the missing base case:

* `AlgebraicGeometry.geometricallyIntegral_of_isIso`: an isomorphism of schemes is geometrically
  integral.

No external mathematics is vendored; the proof reuses Mathlib's stability of the isomorphism
morphism property under pullback and the integrality of a scheme isomorphic to an integral one.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

/-- An isomorphism of schemes is geometrically integral.

Every base change of an isomorphism is an isomorphism, so the fibre product of `f` with a morphism
`Spec L ⟶ Y` is isomorphic to `Spec L`, which is integral because `L` is a field. -/
lemma geometricallyIntegral_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    GeometricallyIntegral f := by
  constructor
  intro L _ y Z fst snd h
  have : IsIso snd :=
    (MorphismProperty.isomorphisms Scheme).of_isPullback h (inferInstanceAs (IsIso f))
  exact IsIntegral.of_isIso (inv snd)

end AlgebraicGeometry

end TauCeti

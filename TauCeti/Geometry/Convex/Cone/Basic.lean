/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.LinearAlgebra.Prod

/-!
# Salience of images and products of cones

Mathlib's `ConvexCone.Salient` records that a convex cone contains no line. This file proves the
two closure properties of salience that concern standard cone constructions: the image under an
injective linear map, and the product of two pointed cones. Neither statement involves a lattice,
so both belong to the generic convex-cone API rather than to any consumer of it.

## Main declarations

* `ConvexCone.Salient.map`: the image of a salient convex cone under an injective linear map is
  salient.
* `ConvexCone.Salient.prod`: a product of salient pointed cones is salient.
-/

public section

namespace ConvexCone.Salient

variable {R V V' : Type*} [Semiring R] [PartialOrder R] [AddCommGroup V] [AddCommGroup V']
  [Module R V] [Module R V']

/-- The image of a salient convex cone under an injective linear map is salient. -/
theorem map {C : ConvexCone R V} {g : V →ₗ[R] V'} (hC : C.Salient)
    (hg : Function.Injective g) : (C.map g).Salient := by
  rintro _ ⟨x, hx, rfl⟩ hne hneg
  obtain ⟨y, hy, hgy⟩ := hneg
  have hyx : y = -x := hg (by rw [map_neg]; exact hgy)
  exact hC x hx (fun h ↦ hne (by simp [h])) (hyx ▸ hy)

/-- A product of salient pointed cones is salient. -/
theorem prod [IsOrderedRing R] {σ : PointedCone R V} {τ : PointedCone R V'}
    (hσ : (σ : ConvexCone R V).Salient) (hτ : (τ : ConvexCone R V').Salient) :
    ((σ.prod τ : PointedCone R (V × V')) : ConvexCone R (V × V')).Salient := by
  rintro ⟨x, y⟩ ⟨hx, hy⟩ hne ⟨hnx, hny⟩
  rcases eq_or_ne x 0 with rfl | hx0
  · exact hτ y hy (fun h ↦ hne (by simp [h])) hny
  · exact hσ x hx hx0 hnx

end ConvexCone.Salient

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Isogenies of Weierstrass curves

An isogeny between affine Weierstrass curves over a field is represented contravariantly by a
pullback from the target coordinate ring to the source function field. The pullback is required to
send the source point at infinity to the target point at infinity. Algebraically, this means that
the source coordinate ring is integral over the image of the target coordinate ring.

This file introduces that data and its identity element. The integrality condition installs the
algebra structure induced by the chosen pullback only locally: different pullbacks generally give
different algebra structures on the same function field, so registering one globally would create
a typeclass diamond.

## Main definitions

* `TauCeti.CoordinatePullback`: the contravariant coordinate-ring map of a morphism.
* `TauCeti.CoordinatePullback.MapsInfinity`: the integrality condition expressing pointedness.
* `TauCeti.Isogeny`: a coordinate pullback satisfying `MapsInfinity`.
* `TauCeti.Isogeny.id`: the identity isogeny.

This is the opening milestone of Layer 1 of the elliptic-curves roadmap. The definition is the
coordinate-ring form of D. Angdinata's function-field definition of an isogeny. The geometric
interpretation follows Silverman, *The Arithmetic of Elliptic Curves*, II.2.4. No ellipticity or
normality assumption is needed to state the data.
-/

public section

namespace TauCeti

open WeierstrassCurve.Affine

variable {F : Type*} [Field F]

/-- A contravariant pullback from the target coordinate ring to the source function field. -/
abbrev CoordinatePullback (W₁ W₂ : WeierstrassCurve.Affine F) : Type _ :=
  W₂.CoordinateRing →ₐ[F] W₁.FunctionField

namespace CoordinatePullback

/-- The source point at infinity maps to the target point at infinity: every element of the
source coordinate ring is integral over the target coordinate ring acting through `pullback`.

The algebra structure induced by `pullback` is deliberately local to the definition. -/
def MapsInfinity {W₁ W₂ : WeierstrassCurve.Affine F}
    (pullback : CoordinatePullback W₁ W₂) : Prop :=
  letI := pullback.toRingHom.toAlgebra
  ∀ x : W₁.CoordinateRing,
    algebraMap W₁.CoordinateRing W₁.FunctionField x ∈
      integralClosure W₂.CoordinateRing W₁.FunctionField

/-- A coordinate pullback maps infinity to infinity exactly when the source coordinate ring is
integral over the target coordinate ring acting through the pullback. -/
@[simp]
theorem mapsInfinity_iff {W₁ W₂ : WeierstrassCurve.Affine F}
    (pullback : CoordinatePullback W₁ W₂) :
    pullback.MapsInfinity ↔ ∀ x : W₁.CoordinateRing,
      @IsIntegral W₂.CoordinateRing W₁.FunctionField _ _ pullback.toRingHom.toAlgebra
        (algebraMap W₁.CoordinateRing W₁.FunctionField x) :=
  Iff.rfl

/-- A coordinate pullback maps infinity to infinity if a fixed positive power of every source
coordinate function is pulled back from the target. -/
theorem mapsInfinity_of_pow {W₁ W₂ : WeierstrassCurve.Affine F}
    (pullback : CoordinatePullback W₁ W₂) {n : ℕ} (hn : 0 < n)
    (h : ∀ z : W₁.CoordinateRing, ∃ w : W₂.CoordinateRing,
      pullback w = algebraMap W₁.CoordinateRing W₁.FunctionField z ^ n) :
    pullback.MapsInfinity := by
  rw [mapsInfinity_iff]
  let _ := pullback.toRingHom.toAlgebra
  intro z
  obtain ⟨w, hw⟩ := h z
  refine IsIntegral.of_pow hn ?_
  rw [← hw]
  rw [← AlgHom.coe_toRingHom, ← RingHom.algebraMap_toAlgebra pullback.toRingHom]
  exact isIntegral_algebraMap

/-- The identity coordinate pullback, embedding a coordinate ring into its fraction field. -/
noncomputable def id (W : WeierstrassCurve.Affine F) : CoordinatePullback W W :=
  IsScalarTower.toAlgHom F W.CoordinateRing W.FunctionField

/-- The identity coordinate pullback is the canonical embedding into the function field. -/
@[simp]
theorem id_apply (W : WeierstrassCurve.Affine F) (x : W.CoordinateRing) :
    id W x = algebraMap W.CoordinateRing W.FunctionField x := by
  unfold id
  exact IsScalarTower.toAlgHom_apply F W.CoordinateRing W.FunctionField x

/-- The identity coordinate pullback maps infinity to infinity. -/
@[simp]
theorem mapsInfinity_id (W : WeierstrassCurve.Affine F) :
    ∀ x : W.CoordinateRing,
      @IsIntegral W.CoordinateRing W.FunctionField _ _ (id W).toRingHom.toAlgebra
        (algebraMap W.CoordinateRing W.FunctionField x) := by
  have h : (id W).toRingHom.toAlgebra =
      (inferInstance : Algebra W.CoordinateRing W.FunctionField) := by
    apply Algebra.algebra_ext
    intro x
    rw [RingHom.algebraMap_toAlgebra]
    exact id_apply W x
  rw [h]
  exact fun _ ↦ isIntegral_algebraMap

end CoordinatePullback

/-- The pullback data of a nonzero isogeny between affine Weierstrass curves.

The `mapsInfinity` field is the algebraic form of pointedness. Injectivity and finiteness of the
induced extension are the next results in the isogeny development; they are consequences of this
condition rather than additional structure fields. -/
@[ext]
structure Isogeny (W₁ W₂ : WeierstrassCurve.Affine F) where
  /-- The contravariant map out of the target coordinate ring. -/
  pullback : CoordinatePullback W₁ W₂
  /-- The source point at infinity maps to the target point at infinity. -/
  mapsInfinity : pullback.MapsInfinity

namespace Isogeny

/-- The identity isogeny. -/
noncomputable def id (W : WeierstrassCurve.Affine F) : Isogeny W W where
  pullback := CoordinatePullback.id W
  mapsInfinity := (CoordinatePullback.mapsInfinity_iff _).2
    (CoordinatePullback.mapsInfinity_id W)

@[simp]
theorem id_pullback (W : WeierstrassCurve.Affine F) : (id W).pullback = CoordinatePullback.id W :=
  (rfl)

end Isogeny

end TauCeti

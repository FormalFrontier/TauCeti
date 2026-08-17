/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Polarization data for quadratic spaces

This file packages the decomposition used to construct spinor modules: two isotropic subspaces
in a left- and right-nondegenerate polar pairing and an orthogonal remainder embedded in the
scalar line.

## Main definition

* `TauCeti.SpinPolarizationData` records the decomposition and its consumer-facing coordinates.

## References

* [Tau Ceti Roadmap](https://github.com/TauCetiProject/TauCetiRoadmap), Representation Theory /
  Spin Representations, Layer 4, "The spin module".
-/

public section

namespace TauCeti

universe u v

/-- The decomposition data used by the exterior model of a spin representation. -/
@[ext]
structure SpinPolarizationData {K : Type u} [CommRing K] {V : Type v}
    [AddCommGroup V] [Module K V] (Q : QuadraticForm K V) where
  /-- The isotropic subspace used for exterior multiplication. -/
  W : Submodule K V
  /-- The complementary isotropic subspace used for contraction. -/
  W' : Submodule K V
  /-- The orthogonal remainder, embedded in the scalar line by `lineCoordinate`. -/
  line : Submodule K V
  /-- The direct-sum coordinates of the quadratic space. -/
  decompositionEquiv : ((W × W') × line) ≃ₗ[K] V
  /-- The decomposition equivalence adds the three components in the ambient module. -/
  decompositionEquiv_apply :
    ∀ x, decompositionEquiv x = (x.1.1 : V) + x.1.2 + x.2
  /-- The first summand is isotropic. -/
  isotropic_W : ∀ x : W, Q x = 0
  /-- The second summand is isotropic. -/
  isotropic_W' : ∀ y : W', Q y = 0
  /-- The polar form identifies the second summand with the dual of the first. -/
  pairingEquiv : W' ≃ₗ[K] Module.Dual K W
  /-- The pairing equivalence is evaluation by the polar form. -/
  pairingEquiv_apply :
    ∀ (y : W') (x : W), pairingEquiv y x = QuadraticMap.polar Q x y
  /-- The polar pairing has trivial left radical. -/
  pairing_separatingLeft :
    ∀ x : W, (∀ y : W', QuadraticMap.polar Q x y = 0) → x = 0
  /-- The coordinate on the at-most-one-dimensional remainder. -/
  lineCoordinate : line →ₗ[K] K
  /-- The remainder embeds in the scalar line through its coordinate. -/
  lineCoordinate_injective : Function.Injective lineCoordinate
  /-- The quadratic form on the remainder is the square of its coordinate. -/
  lineCoordinate_sq : ∀ z : line, lineCoordinate z * lineCoordinate z = Q z
  /-- The remainder is orthogonal to the first isotropic summand. -/
  line_orthogonal_W :
    ∀ z : line, ∀ x : W, QuadraticMap.polar Q z x = 0
  /-- The remainder is orthogonal to the second isotropic summand. -/
  line_orthogonal_W' :
    ∀ z : line, ∀ y : W', QuadraticMap.polar Q z y = 0

attribute [simp, grind =] SpinPolarizationData.decompositionEquiv_apply
  SpinPolarizationData.isotropic_W SpinPolarizationData.isotropic_W'
  SpinPolarizationData.pairingEquiv_apply SpinPolarizationData.lineCoordinate_sq
  SpinPolarizationData.line_orthogonal_W SpinPolarizationData.line_orthogonal_W'

namespace SpinPolarizationData

/-- Recover the three components of a vector assembled from polarization coordinates. -/
@[simp, grind =]
theorem decompositionEquiv_symm_apply {K : Type u} [CommRing K] {V : Type v}
    [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
    (x : P.W) (y : P.W') (z : P.line) :
    P.decompositionEquiv.symm ((x : V) + (y : V) + (z : V)) = ((x, y), z) := by
  apply P.decompositionEquiv.injective
  rw [P.decompositionEquiv.apply_symm_apply, P.decompositionEquiv_apply]

/-- A vector of the first isotropic summand has only that coordinate. -/
@[simp, grind =]
theorem decompositionEquiv_symm_coe_W {K : Type u} [CommRing K] {V : Type v}
    [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
    (x : P.W) : P.decompositionEquiv.symm (x : V) = ((x, 0), 0) := by
  simpa using P.decompositionEquiv_symm_apply x 0 0

/-- A vector of the second isotropic summand has only that coordinate. -/
@[simp, grind =]
theorem decompositionEquiv_symm_coe_W' {K : Type u} [CommRing K] {V : Type v}
    [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
    (y : P.W') : P.decompositionEquiv.symm (y : V) = ((0, y), 0) := by
  simpa using P.decompositionEquiv_symm_apply 0 y 0

/-- A vector of the orthogonal remainder has only that coordinate. -/
@[simp, grind =]
theorem decompositionEquiv_symm_coe_line {K : Type u} [CommRing K] {V : Type v}
    [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
    (z : P.line) : P.decompositionEquiv.symm (z : V) = ((0, 0), z) := by
  simpa using P.decompositionEquiv_symm_apply 0 0 z

/-- The polar pairing has trivial right radical. -/
theorem pairing_separatingRight {K : Type u} [CommRing K] {V : Type v}
    [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
    (y : P.W') (hy : ∀ x : P.W, QuadraticMap.polar Q x y = 0) : y = 0 := by
  apply P.pairingEquiv.injective
  ext x
  simp only [P.pairingEquiv_apply, hy x, map_zero, LinearMap.zero_apply]

end SpinPolarizationData

end TauCeti

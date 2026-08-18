/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
-- Private: `Subspace.dual_finrank_eq`, `Module.finrank_prod` and
-- `LinearMap.finrank_le_finrank_of_injective` occur only inside the proofs of the dimension
-- count; none is named by an exported statement.
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Polarization data for quadratic spaces

This file packages the decomposition used to construct spinor modules: two isotropic subspaces
in a left- and right-nondegenerate polar pairing and an orthogonal remainder embedded in the
scalar line.

Over a field the decomposition also counts dimensions: the two isotropic summands are dual to each
other, so equidimensional, and the remainder embeds in the scalar line, so is at most a line.
Hence `dim V = 2 · dim W + dim line` with `dim line ≤ 1`, and the parity of `dim V` decides which,
giving `dim W = l` both in dimension `2l` (type `Dₗ`) and in dimension `2l + 1` (type `Bₗ`).

## Main definition

* `TauCeti.SpinPolarizationData` records the decomposition and its consumer-facing coordinates.

## Main results

* `TauCeti.SpinPolarizationData.finrank_eq`: `dim V = 2 · dim W + dim line`, with
  `TauCeti.SpinPolarizationData.finrank_W'` and
  `TauCeti.SpinPolarizationData.finrank_line_le_one` supplying its two ingredients.
* `TauCeti.SpinPolarizationData.finrank_W_of_finrank_eq_two_mul` and
  `TauCeti.SpinPolarizationData.finrank_W_of_finrank_eq_two_mul_add_one`: `dim W = l` in dimension
  `2l` and in dimension `2l + 1`.

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

section Dimension

open Module

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q)

/-- **The two isotropic summands of a polarization are equidimensional**, because the polar form
identifies the second with the dual of the first. -/
theorem finrank_W' : finrank K P.W' = finrank K P.W :=
  P.pairingEquiv.finrank_eq.trans Subspace.dual_finrank_eq

/-- **The remainder of a polarization is at most a line**: it embeds into the ground field through
its coordinate. -/
theorem finrank_line_le_one : finrank K P.line ≤ 1 := by
  simpa using P.lineCoordinate.finrank_le_finrank_of_injective P.lineCoordinate_injective

variable [FiniteDimensional K V]

/-- **The dimension of a polarized quadratic space**: twice the dimension of the isotropic summand,
plus the dimension of the remainder — which is `0` or `1` by
`TauCeti.SpinPolarizationData.finrank_line_le_one`, so the parity of `finrank K V` decides which. -/
theorem finrank_eq : finrank K V = 2 * finrank K P.W + finrank K P.line := by
  have h := P.decompositionEquiv.finrank_eq
  rw [finrank_prod, finrank_prod, P.finrank_W'] at h
  omega

/-- In **even** dimension `2l` the remainder of a polarization is trivial and the isotropic summand
has dimension `l`. This is the type `Dₗ` case, where the spinor module `⋀·W` has dimension `2ˡ` and
splits into two half-spin subrepresentations. -/
theorem finrank_W_of_finrank_eq_two_mul {l : ℕ} (hV : finrank K V = 2 * l) :
    finrank K P.W = l := by
  have h := P.finrank_eq
  have := P.finrank_line_le_one
  omega

/-- In **odd** dimension `2l + 1` the remainder of a polarization is a line and the isotropic
summand again has dimension `l`. This is the type `Bₗ` case, where the spinor module `⋀·W` has
dimension `2ˡ` and the parity splitting is not one of representations. -/
theorem finrank_W_of_finrank_eq_two_mul_add_one {l : ℕ} (hV : finrank K V = 2 * l + 1) :
    finrank K P.W = l := by
  have h := P.finrank_eq
  have := P.finrank_line_le_one
  omega

end Dimension

end SpinPolarizationData

end TauCeti

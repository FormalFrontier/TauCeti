/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Principal.Basic

/-!
# The abstract Abel-Jacobi divisor class map

This file adds the point-level divisor-class shadow of the Abel-Jacobi map to the formal
Layer A divisor API.  Once the Jacobian is constructed as `Pic⁰(X)`, the Abel-Jacobi morphism
attached to a base point `x₀` sends a point `x` to the degree-zero line bundle
`𝒪_X(x - x₀)` over an algebraically closed field.  For closed points over a non-algebraically
closed field, the weighted-degree-corrected divisor is `x - w(x) x₀`, when `x₀` has residue
degree `1`.

Here the geometry is still abstracted to an `OrderSystem` and an integer-valued weight
`w : X → ℤ`.  We define the formal divisor `[x] - w(x)[x₀]`, prove it has weighted degree zero
when `w x₀ = 1`, and take its divisor class as an element of the abstract `Pic⁰` subgroup
already built in `WeilDivisor.Principal`.  The unweighted specialization recovers
`x ↦ [x] - [x₀]`.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A (`Pic⁰ X = ker deg`) as a
direct prerequisite for Layer F's Abel-Jacobi morphism `aj : X ⟶ Jac X`, while staying at the
formal divisor-class level available before line bundles, the Picard scheme, or the Jacobian
variety exist.  No external mathematics is vendored; this reuses Tau Ceti's `WeilDivisor`,
`OrderSystem.divisorClass`, and `OrderSystem.picZero` API.
-/

@[expose] public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

variable {X G : Type*} [AddCommGroup G]

/-! ### Abel-Jacobi classes in the abstract Picard group -/

namespace OrderSystem

variable (S : OrderSystem X G)

/-- The weighted abstract Abel-Jacobi class of a point.

For a geometric weight `w x = [κ(x) : k]` and a rational base point `x₀` (`w x₀ = 1`), this is
the class of `[x] - w(x)[x₀]` in the abstract weighted-degree-zero Picard group. -/
noncomputable def weightedAbelJacobiClass (w : X → ℤ) (hdeg : S.IsWeightedDegreeZero w)
    {x₀ : X} (hx₀ : w x₀ = 1) (x : X) : picZero w hdeg :=
  ⟨S.divisorClass (weightedPointBaseDifference w x₀ x), by
    rw [divisorClass_mem_picZero]
    exact weightedPointBaseDifference_mem_weightedDegreeZeroSubgroup hx₀ x⟩

/-- Coercing the weighted Abel-Jacobi class to the class group gives the divisor class of the
degree-corrected point divisor. This is the canonical simp form for the subtype coercion. -/
@[simp]
lemma coe_weightedAbelJacobiClass (w : X → ℤ) (hdeg : S.IsWeightedDegreeZero w)
    {x₀ : X} (hx₀ : w x₀ = 1) (x : X) : (S.weightedAbelJacobiClass w hdeg hx₀ x : S.ClassGroup) =
      S.divisorClass (weightedPointBaseDifference w x₀ x) :=
  rfl

/-- The weighted abstract Abel-Jacobi class of the base point is zero. -/
@[simp]
lemma weightedAbelJacobiClass_base (w : X → ℤ) (hdeg : S.IsWeightedDegreeZero w)
    {x₀ : X} (hx₀ : w x₀ = 1) :
    S.weightedAbelJacobiClass w hdeg hx₀ x₀ = 0 := by
  apply Subtype.ext
  simp [weightedAbelJacobiClass, hx₀]

/-- Equality of weighted Abel-Jacobi classes is equality of the corresponding divisor classes. -/
lemma weightedAbelJacobiClass_eq_iff_divisorClass (w : X → ℤ)
    (hdeg : S.IsWeightedDegreeZero w) {x₀ : X} (hx₀ : w x₀ = 1) {x y : X} :
    S.weightedAbelJacobiClass w hdeg hx₀ x = S.weightedAbelJacobiClass w hdeg hx₀ y ↔
      S.divisorClass (weightedPointBaseDifference w x₀ x) =
        S.divisorClass (weightedPointBaseDifference w x₀ y) := by
  constructor
  · intro h
    simpa using congr_arg Subtype.val h
  · intro h
    apply Subtype.ext
    simpa using h

/-- Equality of weighted Abel-Jacobi classes is linear equivalence of the corresponding
degree-corrected point divisors. -/
lemma weightedAbelJacobiClass_eq_iff_linearlyEquivalent (w : X → ℤ)
    (hdeg : S.IsWeightedDegreeZero w) {x₀ : X} (hx₀ : w x₀ = 1) {x y : X} :
    S.weightedAbelJacobiClass w hdeg hx₀ x = S.weightedAbelJacobiClass w hdeg hx₀ y ↔
      S.LinearlyEquivalent (weightedPointBaseDifference w x₀ x)
        (weightedPointBaseDifference w x₀ y) := by
  rw [S.weightedAbelJacobiClass_eq_iff_divisorClass w hdeg hx₀, S.divisorClass_eq_iff]

end OrderSystem

end WeilDivisor

end AlgebraicGeometry

end TauCeti

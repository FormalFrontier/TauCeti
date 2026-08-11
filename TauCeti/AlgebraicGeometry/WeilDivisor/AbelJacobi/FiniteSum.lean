/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.AbelJacobi.Sum.Basic
public import TauCeti.AlgebraicGeometry.WeilDivisor.FiniteSum

/-!
# Abel-Jacobi sums of finite effective divisors

This file connects the formal finite effective divisor constructors from
`TauCeti.AlgebraicGeometry.WeilDivisor.FiniteSum` with the divisor-level Abel-Jacobi sum from
`TauCeti.AlgebraicGeometry.WeilDivisor.AbelJacobi.Sum.Basic`.

For an order system whose principal divisors have weighted degree zero and a weight-one base
point `x₀`, the Abel-Jacobi sum of a finite effective divisor is the corresponding finite sum
of point Abel-Jacobi classes:

`AJ(Σ nₓ[x]) = Σ nₓ • AJ(x)`.

The same statements are provided for finitely supported multiplicities, for a finite set with
external multiplicity function, and for the coefficient-one divisor attached to a finite set.
These are the formal divisor-class normal forms used by the later symmetric-power Abel maps
`D ↦ 𝒪_X(D - d·x₀)` in the Jacobian roadmap.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, "`Pic⁰ X = ker deg` (as
an abstract group)", and supplies a direct prerequisite for the Layer C/D Abel-map lane from
symmetric powers. No external mathematics is vendored; the proofs reuse Tau Ceti's existing
finite divisor constructors and Abel-Jacobi homomorphism API.
-/

public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

variable {X G : Type*} [AddCommGroup G]

namespace OrderSystem

variable (S : OrderSystem X G)

/-! ### Weighted finite effective divisors -/

/-- The weighted Abel-Jacobi sum of a divisor from finitely supported natural multiplicities is
the finite sum of the point Abel-Jacobi classes with those multiplicities. -/
@[simp]
lemma weightedAbelJacobiDivisorClass_ofFinsupp (w : X → ℤ) (h : S.IsWeightedDegreeZero w)
    {x₀ : X} (hx₀ : w x₀ = 1) (m : X →₀ ℕ) :
    S.weightedAbelJacobiDivisorClass w h hx₀ (ofFinsupp m) =
      ∑ x ∈ m.support, (m x : ℤ) • S.weightedAbelJacobiClass w h hx₀ x := by
  rw [ofFinsupp_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [map_zsmul, S.weightedAbelJacobiDivisorClass_ofPoint w h hx₀ x]

/-- The weighted Abel-Jacobi sum of a finite-set divisor with multiplicities is the finite sum
of the point Abel-Jacobi classes with those multiplicities. -/
@[simp]
lemma weightedAbelJacobiDivisorClass_ofFinsetWithMultiplicity (w : X → ℤ)
    (h : S.IsWeightedDegreeZero w) {x₀ : X} (hx₀ : w x₀ = 1) (s : Finset X) (m : X → ℕ) :
    S.weightedAbelJacobiDivisorClass w h hx₀ (ofFinsetWithMultiplicity s m) =
      ∑ x ∈ s, (m x : ℤ) • S.weightedAbelJacobiClass w h hx₀ x := by
  rw [ofFinsetWithMultiplicity_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [map_zsmul, S.weightedAbelJacobiDivisorClass_ofPoint w h hx₀ x]

/-- The weighted Abel-Jacobi sum of a coefficient-one finite-set divisor is the sum of the
point Abel-Jacobi classes over the finite set. -/
@[simp]
lemma weightedAbelJacobiDivisorClass_ofFinset (w : X → ℤ) (h : S.IsWeightedDegreeZero w)
    {x₀ : X} (hx₀ : w x₀ = 1) (s : Finset X) :
    S.weightedAbelJacobiDivisorClass w h hx₀ (ofFinset s) =
      ∑ x ∈ s, S.weightedAbelJacobiClass w h hx₀ x := by
  rw [ofFinset_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [S.weightedAbelJacobiDivisorClass_ofPoint w h hx₀ x]

end OrderSystem

end WeilDivisor

end AlgebraicGeometry

end TauCeti

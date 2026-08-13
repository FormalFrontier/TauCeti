/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.FiniteType
public import TauCeti.Algebra.AlgebraicGroup.AdditiveFrobeniusKernel.Basic
public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Scheme

/-!
# Finite type of the Frobenius kernel

The coordinate ring of `αₚ` is the quotient `k[x] / (xᵖ)`, hence is a finite-type `k`-algebra.
This file records the corresponding instance. It identifies the rank-one symmetric algebra with
the polynomial algebra on a singleton through `TauCeti.AdditiveGroup.coordinateAlgEquiv`, then
uses Mathlib's finite-type instances for multivariate polynomial rings and their quotients.

The instance lets the nonreduced Frobenius kernel participate in properties and categories of
finite-type affine groups, including the geometric unipotence property.

## Main declarations

* `TauCeti.AlphaP.instFiniteTypeCoordinateRing`: `k[x] / (xᵖ)` is finite type over `k`.
-/

public section

namespace TauCeti.AlphaP

universe u

variable {k : Type u} [CommRing k] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- The coordinate ring `k[x] / (xᵖ)` of the Frobenius kernel is a finite-type `k`-algebra. -/
noncomputable instance instFiniteTypeCoordinateRing :
    Algebra.FiniteType k (CoordinateRing (R := k) p) := by
  let : Algebra.FiniteType k (SymmetricAlgebra k k) :=
    Algebra.FiniteType.equiv inferInstance (AdditiveGroup.coordinateAlgEquiv k).symm
  infer_instance

end TauCeti.AlphaP

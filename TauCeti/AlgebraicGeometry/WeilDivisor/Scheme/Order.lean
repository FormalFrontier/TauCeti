/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Basic
public import Mathlib.AlgebraicGeometry.OrderOfVanishing

/-!
# Orders of rational functions at codimension-one points

For a locally Noetherian integral scheme `X`, Mathlib defines the order of vanishing
`Scheme.ord f x : ℤ` of a rational function at a point. This file packages its restriction to
nonzero rational functions at a codimension-one point as an additive homomorphism

`SchemeWeilDivisor.orderAt x : Additive X.functionFieldˣ →+ ℤ`.

This is the local algebraic input for the scheme-theoretic principal-divisor map. Constructing
that map also requires the separate global theorem that a nonzero rational function has nonzero
order at only finitely many codimension-one points; no finiteness assumption is hidden here.

An elementary fact about `Scheme.ord` itself is recorded first: a function regular on `U` has
nonnegative order at every point of `U` (`Scheme.ord_germToFunctionField_nonneg`), that is, it has
no poles where it is defined.

The construction advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, the
"principal divisors" part of "Divisors on a curve". It reuses Mathlib's
`AlgebraicGeometry.Scheme.ord`, `ordHom`, and `ord_eq_unzero_ordHom`; no external
formalization is vendored.
-/

public section

open AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

noncomputable section

namespace Scheme

/-- A regular function on `U` has nonnegative order at every point of `U`: it has no poles where
it is defined. -/
lemma ord_germToFunctionField_nonneg {U : X.Opens} [Nonempty U] (a : Γ(X, U)) {x : X}
    (hx : x ∈ U) : 0 ≤ X.ord (X.germToFunctionField U a) x := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · have h := Scheme.ord_le_smul hx ha (1 : X.functionField)
    let _ : Nonempty (⊤ : X.Opens) := ⟨⟨x, trivial⟩⟩
    -- Naming this proof fixes the open set before elaborating `ord_of_isUnit`.
    have hx_top : x ∈ (⊤ : X.Opens) := by simp
    have h_one : X.ord (1 : X.functionField) x = 0 := by
      simpa using X.ord_of_isUnit (U := ⊤) isUnit_one hx_top
    rwa [Algebra.smul_def, mul_one, RingHom.algebraMap_toAlgebra, h_one] at h

end Scheme

namespace SchemeWeilDivisor

/-- The order of a nonzero rational function at a codimension-one point, as an additive
homomorphism from the additive form of the unit group of the function field. -/
noncomputable def orderAt (x : CodimensionOnePoint X) :
    Additive (X.functionFieldˣ) →+ ℤ :=
  MonoidHom.toAdditiveLeft
    (WithZero.unitsWithZeroEquiv.toMonoidHom.comp
      (Units.map (X.ordHom x x.property).toMonoidHom))

/-- Evaluating `orderAt` gives Mathlib's integer-valued order of vanishing. -/
@[simp]
lemma orderAt_apply (x : CodimensionOnePoint X) (f : Additive X.functionFieldˣ) :
    orderAt x f = X.ord ((Additive.toMul f : X.functionFieldˣ) : X.functionField) x := by
  rw [X.ord_eq_unzero_ordHom x.property
    (Units.ne_zero (Additive.toMul f : X.functionFieldˣ))]
  simp only [orderAt, MonoidHom.toAdditiveLeft_apply_apply, MonoidHom.coe_comp,
    MulEquiv.coe_toMonoidHom, Function.comp_apply, WithZero.unitsWithZeroEquiv_apply]
  congr 1

end SchemeWeilDivisor

end

end AlgebraicGeometry

end TauCeti

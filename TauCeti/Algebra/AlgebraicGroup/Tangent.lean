/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Adjoint
public import TauCeti.Algebra.AlgebraicGroup.Tangent.CounitPoints
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Cotangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Dimension
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Equivariance
public import TauCeti.Algebra.AlgebraicGroup.Tangent.FiniteType
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Map
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Naturality

/-!
# The tangent space at the identity

Aggregator for the tangent-level theory: the counit-valued derivations
(`Tangent.Basic`), the points valued in the counit algebra (`Tangent.CounitPoints`),
their description by the cotangent space
(`Tangent.Cotangent`), finiteness at an identity of finite type
(`Tangent.FiniteType`), tangent dimensions and their invariance under coefficient-field extension
(`Tangent.Dimension`), functoriality in the bialgebra
(`Tangent.DerivationMap`, `Tangent.Map`) and coefficient algebra
(`Tangent.Naturality`), and the adjoint action of the points
(`Tangent.Adjoint`), including equivariance of the differential
(`Tangent.Equivariance`).
The Lie-algebra structure lives in the `Tangent.Lie` aggregator.
-/

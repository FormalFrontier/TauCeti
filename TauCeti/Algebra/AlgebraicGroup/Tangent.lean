/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Adjoint
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Map
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Naturality

/-!
# The tangent space at the identity

Aggregator for the tangent-level theory: the counit-valued derivations
(`Tangent.Basic`), functoriality in the bialgebra (`Tangent.DerivationMap`,
`Tangent.Map`) and coefficient algebra (`Tangent.Naturality`), and the adjoint
action of the points (`Tangent.Adjoint`).
The Lie-algebra structure lives in the `Tangent.Lie` aggregator.
-/

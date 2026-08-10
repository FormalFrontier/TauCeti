/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Basic
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Map
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Naturality

/-!
# The Lie algebra of the tangent space

Directory aggregator: importing this module provides the Lie algebra structure
on counit-valued derivations (`Lie.Basic`), the differential as a Lie algebra
morphism (`Lie.Map`), and the compatibility of the adjoint action with the bracket
(`Lie.Adjoint`) and change of coefficient algebra (`Lie.Naturality`).
-/

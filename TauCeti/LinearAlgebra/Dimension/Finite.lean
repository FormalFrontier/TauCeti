/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Finite modules over finite-dimensional algebras

This file relates finite generation over a finite-dimensional algebra to finite dimensionality over
its base field.
-/

public section

namespace TauCeti

universe u v w

variable (k : Type u) (A : Type v) [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]

/-- **Over a finite-dimensional algebra the finitely generated modules are the finite-dimensional
ones.** -/
theorem finite_iff_finiteDimensional (M : Type w) [AddCommGroup M] [Module A M] [Module k M]
    [IsScalarTower k A M] : Module.Finite A M ↔ FiniteDimensional k M :=
  ⟨fun _ => Module.Finite.trans A M, fun _ => Module.Finite.of_restrictScalars_finite k A M⟩

end TauCeti

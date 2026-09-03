/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Rat

/-!
# Restricting scalars from rational to nonnegative-rational modules

Every module over `ℚ` is a module over `ℚ≥0` by restriction of scalars along
`algebraMap ℚ≥0 ℚ`. This is deliberately not a global instance: Mathlib already builds
`Module ℚ≥0 R` from `DivisionSemiring R`, so a second global path would put two structures on
types such as `ℚ` itself; they agree by `subsingleton_nnrat_module`, but not definitionally.

Consumers activate it where they need it with
`attribute [local instance] TauCeti.moduleNNRat`. The typical use is to obtain Mathlib's
`BinomialRing` instance — which is stated for a `Module ℚ≥0` — on a possibly noncommutative
`ℚ`-algebra such as a universal enveloping algebra, so that `Ring.choose` elaborates there.

## Main definitions

* `TauCeti.moduleNNRat`: the `ℚ≥0`-module structure on a `ℚ`-module.
-/

public section

namespace TauCeti

/-- The nonnegative-rational module structure induced on a rational module. -/
@[instance_reducible]
noncomputable def moduleNNRat {A : Type*} [AddCommMonoid A] [Module ℚ A] : Module ℚ≥0 A :=
  Module.compHom _ (algebraMap ℚ≥0 ℚ)

end TauCeti

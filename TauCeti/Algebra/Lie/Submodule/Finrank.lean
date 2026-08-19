/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Submodule
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# The dimension of a Lie submodule

A Lie submodule and its carrier submodule have the same underlying type, so they have the same
dimension. This file states that definitional equality once, as the bridge that dimension counts
over Lie submodules pass through: the linear-algebra lemmas about dimensions of direct sums are
stated for `Submodule`, while the Lie-theoretic dimension lemmas are stated for `LieSubmodule`.

## Main results

* `TauCeti.finrank_toSubmodule`: a Lie submodule has the dimension of its carrier submodule.
-/

public section

namespace TauCeti

open Module

variable {R L M : Type*} [CommRing R] [LieRing L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M]

/-- The type underlying a Lie submodule is the type underlying its carrier submodule, so the two
have the same dimension. -/
theorem finrank_toSubmodule (N : LieSubmodule R L M) :
    finrank R N.toSubmodule = finrank R N :=
  rfl

end TauCeti

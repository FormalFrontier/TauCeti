/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Jacobson.Semiprimary

/-!
# The radical quotient of a module over a semiprimary ring

A ring is **semiprimary** when its Jacobson radical is nilpotent and the quotient by it is a
semisimple ring. Mathlib records that the ring `R ⧸ Ring.jacobson R` is then semisimple, but not
the module-level consequence: for *any* `R`-module `M`, the radical quotient `M ⧸ J • M` is a
semisimple module. It is a module over `R ⧸ J`, annihilated by `J`, and semisimplicity does not
depend on which of the two rings the scalars are read in.

## Main results

* `TauCeti.isSemisimpleModule_quotient_jacobson_smul_top`: the radical quotient of any module over
  a semiprimary ring is a semisimple module.
-/

public section

namespace TauCeti

universe u v

variable (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M]

/-- **The radical quotient of a module over a semiprimary ring is semisimple.** It is a module over
the semisimple ring `R ⧸ Ring.jacobson R`, and semisimplicity is insensitive to which of the two
rings the scalars are read in. -/
theorem isSemisimpleModule_quotient_jacobson_smul_top [IsSemiprimaryRing R] :
    IsSemisimpleModule R (M ⧸ Ring.jacobson R • (⊤ : Submodule R M)) :=
  (Module.isTorsionBySet_quotient_ideal_smul M (Ring.jacobson R)).isSemisimpleModule_iff.mp
    inferInstance

end TauCeti

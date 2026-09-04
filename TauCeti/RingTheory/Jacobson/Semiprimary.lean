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

Let `I` be a two-sided ideal of `R` with `R ⧸ I` a semisimple ring. Then for *any* `R`-module `M`
the quotient `M ⧸ I • M` is a semisimple module: it is a module over `R ⧸ I`, annihilated by `I`,
and semisimplicity does not depend on which of the two rings the scalars are read in. Nothing about
`I` beyond semisimplicity of the quotient ring enters.

A ring is **semiprimary** when its Jacobson radical is nilpotent and the quotient by it is a
semisimple ring. Mathlib records that the ring `R ⧸ Ring.jacobson R` is then semisimple; the
special case of the above at `I = Ring.jacobson R` is the module-level consequence, that the
radical quotient of any module over a semiprimary ring is semisimple.

## Main results

* `TauCeti.isSemisimpleModule_quotient_smul_top`: `M ⧸ I • M` is a semisimple `R`-module whenever
  `R ⧸ I` is a semisimple ring.
* `TauCeti.isSemisimpleModule_quotient_jacobson_smul_top`: the radical quotient of any module over
  a semiprimary ring is a semisimple module.
-/

public section

namespace TauCeti

universe u v

variable (R : Type u) [Ring R]

/-- **A module quotient by a semisimple ideal multiple is semisimple.** If `R ⧸ I` is a semisimple
ring then `M ⧸ I • M` is a semisimple `R`-module: it is a module over `R ⧸ I`, and semisimplicity
is insensitive to which of the two rings the scalars are read in. -/
theorem isSemisimpleModule_quotient_smul_top (I : Ideal R) [I.IsTwoSided] [IsSemisimpleRing (R ⧸ I)]
    (M : Type v) [AddCommGroup M] [Module R M] :
    IsSemisimpleModule R (M ⧸ I • (⊤ : Submodule R M)) :=
  (Module.isTorsionBySet_quotient_ideal_smul M I).isSemisimpleModule_iff.mp inferInstance

/-- **The radical quotient of a module over a semiprimary ring is semisimple.** The radical
quotient of a semiprimary ring is a semisimple ring, so this is
`TauCeti.isSemisimpleModule_quotient_smul_top` for the Jacobson radical. -/
theorem isSemisimpleModule_quotient_jacobson_smul_top (M : Type v) [AddCommGroup M] [Module R M]
    [IsSemiprimaryRing R] :
    IsSemisimpleModule R (M ⧸ Ring.jacobson R • (⊤ : Submodule R M)) :=
  isSemisimpleModule_quotient_smul_top R (Ring.jacobson R) M

end TauCeti

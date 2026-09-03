/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finiteness of a `ℤ`-submodule read as an additive subgroup

`Submodule.toAddSubgroup` is reducible and keeps the carrier set, so `p` and `p.toAddSubgroup`
have the same elements and the same `ℤ`-module structure. Instance search is nevertheless keyed
on the head symbol, so a `Module.Finite ℤ p` instance is never tried against the goal
`Module.Finite ℤ p.toAddSubgroup`. This file records that transfer once, for every `ℤ`-submodule,
rather than at each lattice presented to an API that reads additive subgroups.

## Main declarations

* `TauCeti.instModuleFiniteToAddSubgroup`: a finitely generated `ℤ`-submodule stays finitely
  generated when read as an additive subgroup.
-/

public section

namespace TauCeti

/-- A finitely generated `ℤ`-submodule is still finitely generated when read as an additive
subgroup, the two being the same type. -/
instance instModuleFiniteToAddSubgroup {M : Type*} [AddCommGroup M] (p : Submodule ℤ M)
    [Module.Finite ℤ p] : Module.Finite ℤ p.toAddSubgroup :=
  inferInstanceAs (Module.Finite ℤ p)

end TauCeti

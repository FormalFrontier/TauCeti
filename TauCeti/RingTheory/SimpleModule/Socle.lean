/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# The socle of a module

The **socle** of a module is the supremum of its simple submodules.  Mathlib already uses the
submodule `sSup {m | IsSimpleModule R m}` as the object measuring how far a module is from being
semisimple — `IsSemisimpleModule.of_sSup_simples_eq_top` and
`sSup_simples_eq_top_iff_isSemisimpleModule` are stated with it — but does not name it.  This file
names it and records the two properties that pin it down: it is itself semisimple, and it contains
every semisimple submodule.  So it is the largest semisimple submodule, and it is everything
exactly when the module is semisimple.

## Main definitions

* `TauCeti.socle`: the supremum of the simple submodules of a module.

## Main results

* `TauCeti.le_socle` and `TauCeti.socle_le`: the defining supremum property.
* `TauCeti.isSemisimpleModule_socle`: the socle is a semisimple module.
* `TauCeti.le_socle_of_isSemisimpleModule`: every semisimple submodule lies in the socle, so the
  socle is the largest semisimple submodule.
* `TauCeti.socle_eq_top_iff`: the socle is everything exactly for a semisimple module.
-/

public section

namespace TauCeti

variable (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]

/-- The socle of a module: the supremum of its simple submodules.  It is the largest semisimple
submodule, by `TauCeti.isSemisimpleModule_socle` and `TauCeti.le_socle_of_isSemisimpleModule`. -/
def socle : Submodule R M :=
  sSup {m : Submodule R M | IsSimpleModule R m}

variable {R M}

/-- Every simple submodule lies in the socle. -/
theorem le_socle {m : Submodule R M} (hm : IsSimpleModule R m) : m ≤ socle R M :=
  le_sSup hm

/-- A submodule containing every simple submodule contains the socle. -/
theorem socle_le {N : Submodule R M} (h : ∀ m : Submodule R M, IsSimpleModule R m → m ≤ N) :
    socle R M ≤ N :=
  sSup_le h

/-- **The socle is semisimple.** -/
instance isSemisimpleModule_socle : IsSemisimpleModule R (socle R M) := by
  rw [socle, sSup_eq_iSup]
  exact isSemisimpleModule_biSup_of_isSemisimpleModule_submodule fun m hm =>
    haveI : IsSimpleModule R m := hm
    inferInstance

/-- **Every semisimple submodule lies in the socle**, so the socle is the largest semisimple
submodule. -/
theorem le_socle_of_isSemisimpleModule {N : Submodule R M} (hN : IsSemisimpleModule R N) :
    N ≤ socle R M := by
  have := hN
  have hmap : Submodule.map N.subtype (⨆ m ∈ {m : Submodule R N | IsSimpleModule R m}, m) = N := by
    rw [← sSup_eq_iSup, IsSemisimpleModule.sSup_simples_eq_top R N, Submodule.map_subtype_top]
  rw [← hmap, Submodule.map_iSup]
  refine iSup_le fun m => ?_
  rw [Submodule.map_iSup]
  refine iSup_le fun hm => ?_
  have : IsSimpleModule R m := hm
  exact le_socle (IsSimpleModule.congr
    (Submodule.equivMapOfInjective N.subtype (Submodule.subtype_injective N) m).symm)

/-- The socle is everything exactly for a semisimple module. -/
theorem socle_eq_top_iff : socle R M = ⊤ ↔ IsSemisimpleModule R M :=
  sSup_simples_eq_top_iff_isSemisimpleModule

@[simp]
theorem socle_eq_top [IsSemisimpleModule R M] : socle R M = ⊤ :=
  socle_eq_top_iff.2 ‹_›

end TauCeti

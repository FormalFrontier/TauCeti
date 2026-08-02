/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.NumberField.NarrowClassGroup.Basic
public import TauCeti.NumberTheory.NumberField.NarrowClassGroup.Finite

/-!
# The narrow class group (compatibility module)

This module preserves the import path `TauCeti.NumberTheory.NumberField.NarrowClassGroup` after the
development was split into `NarrowClassGroup/Basic.lean` (the definition, `mk`/`lift`/`toClassGroup`
API) and `NarrowClassGroup/Finite.lean` (finiteness). It re-exports both.
-/

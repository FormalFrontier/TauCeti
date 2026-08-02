/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.NumberField.NarrowClassGroup.Finite
public import TauCeti.NumberTheory.NumberField.NarrowClassGroup.TotallyComplex

/-!
# The narrow class group (compatibility module)

This module preserves the import path `TauCeti.NumberTheory.NumberField.NarrowClassGroup` after the
development was split into `NarrowClassGroup/Basic.lean` (the definition, `mk`/`lift`/`toClassGroup`
API and the exact sequence `Kˣ → Cl⁺ → Cl → 1`), `NarrowClassGroup/Finite.lean` (finiteness), and
`NarrowClassGroup/TotallyComplex.lean` (`Cl⁺ ≃ Cl` for totally complex fields). Both `Finite` and
`TotallyComplex` import `Basic`, so these two `public import`s re-export the whole development.
-/

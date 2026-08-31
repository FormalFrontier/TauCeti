/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.ChevalleyRelations
import TauCeti.GroupTheory.Commutator

/-!
# Generating the difference-root subgroups of the symplectic group

For the standard type-`C_m` root system, the roots `eᵢ - eⱼ` form its type-`A_(m-1)`
subsystem, whose structure-constant-one Chevalley relation is

```text
⁅x_{eᵢ-eⱼ}(a), x_{eⱼ-eₖ}(b)⁆ = x_{eᵢ-eₖ}(ab)
```

This file uses it to show that a subgroup containing the difference-root elements at adjacent
indices, in both orientations, contains every difference-root element. This is the first generation
step for identifying the full-weight type-`C` Chevalley carrier with the standard symplectic group:
the numbered short simple roots are adjacent difference roots, while the remaining simple root is
long.

## Main results

* `TauCeti.GLSymplecticFin.differenceShortRootUnit_mem_of_adjacent`: adjacent difference-root
  subgroups generate all difference-root subgroups.

## References

* R. W. Carter, *Simple Groups of Lie Type* (1972), §5.2.
* R. Steinberg, *Lectures on Chevalley Groups* (1968), §§3--4.

This advances Layer 9, "The Chevalley--Demazure construction", of
`TauCetiRoadmap/ReductiveGroups/README.md`: it supplies the type-`A` subsystem generation needed
to identify the explicit full-weight type-`C` carrier on field-valued points.
-/

public section

open Matrix
open scoped commutatorElement

namespace TauCeti.GLSymplecticFin

universe u

variable {R : Type u} [CommRing R] {m : ℕ} {i j : Fin m}

/-- If a subgroup of the standard symplectic group contains every adjacent difference-root
element in both orientations, then it contains every difference-root element. -/
theorem differenceShortRootUnit_mem_of_adjacent
    (H : Subgroup (GLSymplecticFin m R))
    (hadjacent : ∀ {i j : Fin m} (hij : i ≠ j) (c : R),
      i.val + 1 = j.val ∨ j.val + 1 = i.val → differenceShortRootUnit hij c ∈ H)
    {i j : Fin m} (hij : i ≠ j) (c : R) :
    differenceShortRootUnit hij c ∈ H := by
  exact Subgroup.mem_of_adjacent_of_commutator H
    (fun hij c => differenceShortRootUnit hij c)
    (fun hij hjk hik a => by
      simpa using
        commutatorElement_differenceShortRootUnit_differenceShortRootUnit hij hjk hik a 1)
    hadjacent hij c

end TauCeti.GLSymplecticFin

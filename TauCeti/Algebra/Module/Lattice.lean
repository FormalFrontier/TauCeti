/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Module.Lattice

/-!
# Extensions of lattice bases and rank comparisons

This file provides general results about lattices over a commutative ring `R` inside a vector space
over a fraction field `K`, complementing Mathlib's `Mathlib.Algebra.Module.Lattice`.

## Main declarations

* `TauCeti.Basis.span_range_extendOfIsLattice`: the `R`-span of the `K`-basis of `V` extending an
  `R`-basis of a lattice `N` is `N` itself.
* `TauCeti.finrank_of_isLattice`: the `R`-finrank of a full lattice equals the `K`-finrank of the
  ambient space.
-/

public section

open Module

namespace TauCeti

universe u

variable {R K V : Type*} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
variable [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

/-- The `R`-span of the ambient `K`-basis obtained from an `R`-basis of a lattice is the lattice
itself. -/
theorem Basis.span_range_extendOfIsLattice {κ : Type*} {N : Submodule R V} [N.IsLattice K]
    (b : Basis κ R N) :
    Submodule.span R (Set.range (b.extendOfIsLattice K)) = N := by
  have hrange : Set.range (b.extendOfIsLattice K) = Set.range (N.subtype ∘ b) :=
    congrArg Set.range (funext fun i ↦ Basis.extendOfIsLattice_apply K b i)
  rw [hrange, Set.range_comp, ← Submodule.map_span, b.span_eq,
    Submodule.map_top, Submodule.range_subtype]

/-- The `R`-finrank of a full lattice in `V` equals the `K`-finrank of the ambient space. -/
theorem finrank_of_isLattice [IsDomain R] [IsPrincipalIdealRing R]
    (N : Submodule R V) [N.IsLattice K] :
    Module.finrank R N = Module.finrank K V :=
  congr_arg Cardinal.toNat (Submodule.IsLattice.rank' K N)

end TauCeti

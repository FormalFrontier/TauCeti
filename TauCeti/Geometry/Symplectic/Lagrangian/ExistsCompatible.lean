/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Symplectic.ExistsCompatible
public import TauCeti.Geometry.Symplectic.Lagrangian.TotallyReal

/-!
# Lagrangian subspaces are maximal totally real for some compatible structure

`TauCeti.SymplecticForm.IsLagrangian.isMaximalTotallyReal_of_compatible` upgrades a Lagrangian
subspace to a maximal totally real one, but only relative to a compatible almost complex structure
supplied by the caller. Combined with
`TauCeti.SymplecticForm.exists_compatible`, which produces such a structure on any
finite-dimensional symplectic vector space, the hypothesis can be discharged: a Lagrangian subspace
is maximal totally real for *some* compatible structure, with no `J` given in advance.

## Main declaration

* `TauCeti.SymplecticForm.IsLagrangian.exists_compatible_and_isMaximalTotallyReal`: every Lagrangian
  subspace of a finite-dimensional symplectic vector space is maximal totally real for some
  compatible almost complex structure.
-/

public section

namespace TauCeti

namespace SymplecticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Every Lagrangian subspace of a finite-dimensional symplectic vector space is maximal totally
real for some compatible almost complex structure. -/
theorem IsLagrangian.exists_compatible_and_isMaximalTotallyReal [FiniteDimensional ℝ V]
    {ω : SymplecticForm V} {L : Submodule ℝ V} (hL : ω.IsLagrangian L) :
    ∃ J : AlmostComplexStructure V, ω.Compatible J ∧ IsMaximalTotallyReal J.toLinearMap L :=
  let ⟨J, hJ⟩ := ω.exists_compatible
  ⟨J, hJ, hL.isMaximalTotallyReal_of_compatible hJ⟩

end SymplecticForm

end TauCeti

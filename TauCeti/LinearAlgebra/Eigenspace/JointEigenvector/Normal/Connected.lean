/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ConstantGroup.Points
public import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Normal.Finite

/-!
# Connected algebraic actions on normal-subgroup joint weights

Let `H` be the coordinate ring of a connected affine group over a field `k`, acting linearly on a
finite-dimensional vector space. A normal subgroup of the base-valued point group determines a
finite set of characters with nonzero joint weight space, and the ambient point group permutes
those characters.

If this permutation action is represented by a coordinate bialgebra morphism to the corresponding
finite constant symmetric group, connectedness forces it to be trivial. Consequently every
nonzero joint weight space is preserved by every ambient point.

This isolates the connectedness half of the Lie--Kolchin induction. To apply it to a connected
solvable affine group, it remains to construct the coordinate morphism representing the
joint-weight permutation; the finiteness and pointwise action are already supplied by
`finiteIndex_ker_nonzeroJointWeightAction` and `nonzeroJointWeightAction`.

## Main declarations

* `TauCeti.nonzeroJointWeightAction_eq_one_of_eq_pointHom`: a coordinate realization of the
  finite joint-weight action of a connected affine group is trivial.
* `TauCeti.map_iInf_eigenspace_unitHom_eq_self_of_eq_pointHom`: every ambient point preserves
  each nonzero normal-subgroup joint weight space.

## References

* A. Borel, *Linear Algebraic Groups*, §10.5.
* J. E. Humphreys, *Linear Algebraic Groups*, §17.6.

This advances the "Lie--Kolchin; solvable groups" milestone in Layer 5 of the ReductiveGroups
roadmap.
-/

public section

open WithConv

namespace TauCeti

universe u v w x

noncomputable section

variable {k : Type u} [Field k]
variable {H : Type v} [CommRing H] [HopfAlgebra k H]
variable {V : Type w} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

variable (N : Subgroup (WithConv (H →ₐ[k] k))) [N.Normal]
variable (ρ : WithConv (H →ₐ[k] k) →* Module.End k V)

/-- A finite indexing type for the nonzero joint weights. -/
local instance : Fintype (NonzeroJointWeight N ρ) :=
  Fintype.ofFinite _

/-- If the permutation of nonzero normal-subgroup joint weights is represented by a coordinate
morphism to the corresponding finite constant symmetric group, connectedness makes the
permutation action trivial. -/
theorem nonzeroJointWeightAction_eq_one_of_eq_pointHom
    (hconnected : ConnectedSpace (PrimeSpectrum H))
    (f : ConstantGroup.coordinateRing k (Equiv.Perm (NonzeroJointWeight N ρ)) →ₐc[k] H)
    (hcoordinate : nonzeroJointWeightAction N ρ =
      ConstantGroup.pointHom f) :
    nonzeroJointWeightAction N ρ = 1 := by
  rw [hcoordinate]
  exact ConstantGroup.pointHom_eq_one_of_connected hconnected f

/-- Under a coordinate realization of the finite joint-weight action, every point of a connected
affine group preserves every nonzero normal-subgroup joint weight space. -/
theorem map_iInf_eigenspace_unitHom_eq_self_of_eq_pointHom
    (hconnected : ConnectedSpace (PrimeSpectrum H))
    (f : ConstantGroup.coordinateRing k (Equiv.Perm (NonzeroJointWeight N ρ)) →ₐc[k] H)
    (hcoordinate : nonzeroJointWeightAction N ρ =
      ConstantGroup.pointHom f)
    (g : WithConv (H →ₐ[k] k)) (χ : NonzeroJointWeight N ρ) :
    (⨅ n : N, (ρ n).eigenspace (χ.1 n)).map (ρ g) =
      ⨅ n : N, (ρ n).eigenspace (χ.1 n) := by
  apply map_iInf_eigenspace_unitHom_eq_self_of_nonzeroJointWeightAction_eq N ρ g χ
  rw [nonzeroJointWeightAction_eq_one_of_eq_pointHom N ρ hconnected f hcoordinate]
  rfl

end

end TauCeti

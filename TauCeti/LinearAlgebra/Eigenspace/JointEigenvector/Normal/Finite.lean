/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Normal.Basic

/-!
# Finiteness of the normal-subgroup joint-weight action

In a finite-dimensional representation, the characters of a normal subgroup with nonzero joint
weight space form a finite type by `finite_nonzeroJointWeights`. The ambient group therefore acts
on a finite set of nonzero joint weights, so the kernel of this permutation action has finite
index. Each element of that kernel preserves every nonzero joint weight space by
`map_iInf_eigenspace_unitHom_eq_self_of_mem_ker_nonzeroJointWeightAction`.

This is the finite-action bridge in the Lie--Kolchin argument. The remaining connectedness step is
to show that the ambient algebraic group acts trivially on this finite set.

## Main declaration

* `finiteIndex_ker_nonzeroJointWeightAction`: for a normal subgroup, the kernel of the ambient
  permutation action on its nonzero joint weights has finite index.

## References

* A. Borel, *Linear Algebraic Groups*, §10.5.
* J. E. Humphreys, *Linear Algebraic Groups*, §17.6.
-/

public section

noncomputable section

namespace TauCeti

variable {G K V : Type*} [Group G] [Field K] [AddCommGroup V] [Module K V]

/-- The kernel of the permutation action on nonzero normal-subgroup weights has finite index in
the ambient group. -/
theorem finiteIndex_ker_nonzeroJointWeightAction [FiniteDimensional K V]
    (N : Subgroup G) [N.Normal]
    (ρ : G →* Module.End K V) :
    (nonzeroJointWeightAction N ρ).ker.FiniteIndex := by
  let _ : Finite {χ : N →* Kˣ // (⨅ n : N, (ρ n).eigenspace (χ n)) ≠ ⊥} :=
    finite_nonzeroJointWeights (ρ.comp N.subtype)
  exact Subgroup.finiteIndex_ker (nonzeroJointWeightAction N ρ)

end TauCeti

end

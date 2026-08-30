/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Normal.Basic

/-!
# Finiteness of nonzero joint weights

In a finite-dimensional representation, only finitely many characters of a subgroup can have a
nonzero joint weight space. Indeed, distinct character-indexed joint eigenspaces are independent,
so their number is at most the dimension of the representation.

For a normal subgroup, the ambient group therefore acts on a finite set of nonzero joint weights.
The kernel of this permutation action has finite index, and each of its elements preserves every
nonzero joint weight space by
`map_iInf_eigenspace_unitHom_eq_self_of_mem_ker_nonzeroJointWeightAction`.

This is the finite-action bridge in the Lie--Kolchin argument. The remaining connectedness step is
to show that the ambient algebraic group acts trivially on this finite set.

## Main declarations

* `finite_nonzeroJointWeights`: a finite-dimensional representation has only finitely many
  nonzero joint weights for a subgroup.
* `natCard_nonzeroJointWeights_le_finrank`: their number is at most the dimension of the
  representation.
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

/-- A finite-dimensional representation has only finitely many characters of a subgroup
with nonzero joint weight space.

Distinct character-indexed joint eigenspaces are independent, so a finite-dimensional space can
contain only finitely many nonzero ones. -/
noncomputable instance finite_nonzeroJointWeights [FiniteDimensional K V]
    (N : Subgroup G)
    (ρ : G →* Module.End K V) :
    Finite {χ : N →* Kˣ // (⨅ n : N, (ρ n).eigenspace (χ n)) ≠ ⊥} := by
  have h : iSupIndep fun χ : N →* Kˣ ↦
      ⨅ n : N, (ρ n).eigenspace (χ n) :=
    iSupIndep_iInf_eigenspace_unitHom (ρ := ρ.comp N.subtype)
  exact @Finite.of_fintype _ h.fintypeNeBotOfFiniteDimensional

/-- The number of characters of a subgroup with nonzero joint weight space is bounded by
the dimension of the representation. -/
theorem natCard_nonzeroJointWeights_le_finrank [FiniteDimensional K V]
    (N : Subgroup G)
    (ρ : G →* Module.End K V) :
    Nat.card {χ : N →* Kˣ // (⨅ n : N, (ρ n).eigenspace (χ n)) ≠ ⊥} ≤
      Module.finrank K V := by
  have h : iSupIndep fun χ : N →* Kˣ ↦
      ⨅ n : N, (ρ n).eigenspace (χ n) :=
    iSupIndep_iInf_eigenspace_unitHom (ρ := ρ.comp N.subtype)
  let _ : Fintype {χ : N →* Kˣ // (⨅ n : N, (ρ n).eigenspace (χ n)) ≠ ⊥} :=
    h.fintypeNeBotOfFiniteDimensional
  rw [Nat.card_eq_fintype_card]
  exact h.subtype_ne_bot_le_finrank

/-- The kernel of the permutation action on nonzero normal-subgroup weights has finite index in
the ambient group. -/
theorem finiteIndex_ker_nonzeroJointWeightAction [FiniteDimensional K V]
    (N : Subgroup G) [N.Normal]
    (ρ : G →* Module.End K V) :
    (nonzeroJointWeightAction N ρ).ker.FiniteIndex :=
  Subgroup.finiteIndex_ker (nonzeroJointWeightAction N ρ)

end TauCeti

end
